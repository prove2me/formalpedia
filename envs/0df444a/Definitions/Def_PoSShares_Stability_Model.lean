-- Prove2me | Definitions.Def_PoSShares_Stability_Model
-- name    : PoSShares_Stability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:53.530997+00:00
-- url     : https://prove2.me/theorems/7ab53de8-9100-4b06-b06b-c99c0b5e232a
-- title:
--   §2, (1), (5) — the Proof-of-Stake share model: supply $N_t$, coins $n_t$, share $\pi_t$, selection rule, power reward
-- statement:
--   The Proof-of-Stake (PoS) model of Roşu and Saleh, seen from one buy-and-hold investor.
--
--   Time is discrete, $t \in \mathbb{N}$. Let $(\Omega, \mathcal{F}, \mathbb{P})$ be a probability space with a filtration $(\mathcal{F}_t)_{t \ge 0}$. A **model** consists of
--   1. an initial number of coins outstanding $N_0 > 0$ and the tracked investor's initial endowment $n_0$ with $0 \le n_0 \le N_0$;
--   2. deterministic coin rewards $R_t \ge 0$ (used for $t \ge 1$);
--   3. selection indicators $\mathbf{1}_{S_t} \in \{0, 1\}$, each $\mathcal{F}_t$-measurable (used for $t \ge 1$), where $S_t$ is the event that the investor is selected by the protocol at date $t$.
--
--   From these the file defines:
--   - the **coin supply** $N_t = N_0 + \sum_{n=1}^{t} R_n$, i.e. $N_t = N_{t-1} + R_t$;
--   - the investor's **coins** by the buy-and-hold rule (5): $n_t = n_{t-1} + R_t \mathbf{1}_{S_t}$;
--   - the **investor share** (1): $\pi_t = n_t / N_t$;
--   - the **PoS selection rule**: before trading at $t+1$ the investor is selected with probability $\pi_t$, i.e.
--   $$\mathbb{E}\big[\mathbf{1}_{S_{t+1}} \,\big|\, \mathcal{F}_t\big] = \pi_t \quad \text{almost surely, for every } t \ge 0;$$
--   - the **power reward rule** of Proposition 4: $R_t = \rho N_{t-1}^{\gamma}$ for every $t \ge 1$ (a real power).
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** One investor is tracked; the others enter only through the total supply $N_t$, as §3.3.1 aggregates them (their mutual trades sum to zero). The page's assumption that $S_t$ is "independent of all other random variables" cannot be literal, since its probability $\pi_{t-1}$ depends on past selections; the proofs use exactly the conditional probability above, which is what is encoded. The endowment $n_0$ is real (the paper has $n_0 \in \mathbb{N}$; rewards are already real). $R_0$ and $\mathbf{1}_{S_0}$ are never used.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 6, §2 (1) and Proof-of-Stake Protocol; p. 7, (5); p. 10, §3.3.1; p. 14, Proposition 4 (R_t = ρN^γ_{t−1}); p. 17, proof of Proposition 1 (N_t = N_{t−1} + R_t)

import Mathlib

open MeasureTheory

namespace PoSShares.Stability

/-! # The Proof-of-Stake share model of Roşu and Saleh

Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb), p. 6 (§2: investor shares (1), the PoS protocol), p. 7
((5), buy-and-hold), p. 10 (§3.3.1: N = N_0, π_1, n_1 = π_1 N), p. 14 (Proposition 4: R_t = ρN^γ_{t−1}),
p. 17 (proof of Proposition 1: N_t = N_{t−1} + R_t).

**Formalization Note.**
* One investor (the paper's "investor i" of Proposition 1, "investor 1" of Proposition 4) is tracked.
  The other investors enter only through the total supply `N_t`, as §3.3.1 (p. 10) aggregates them;
  trades among them sum to zero and do not change `N_t`.
* The tracked investor never trades, so her holding follows (5): `n_t = n_{t−1} + R_t 1_{S_t}`.
* The selection indicator `1_{S_t}` is `ξ t`, `{0,1}`-valued and `ℱ t`-measurable. The selection rule
  "selected with probability π_{t−1}" is the conditional-expectation condition `IsPoS`
  (`E[1_{S_{t+1}} | ℱ_t] = π_t`). The page's "independent of all other random variables" cannot be
  literal (the probability π_{t−1} depends on past selections); the proofs (A3), (A10) use exactly
  this conditional probability.
* The initial endowment `n₀` is real with `0 ≤ n₀ ≤ N₀` (the paper has `n_{i,0} ∈ ℕ`; rewards are
  already real, "not necessarily an integer", p. 6, and no proof used here needs integrality).
* `R 0` and `ξ 0` are never used: rewards and selections happen at dates `t ≥ 1`.
-/

/-- The PoS share model of §2 (p. 6) for one tracked buy-and-hold investor, on a measurable space
`Ω` carrying a filtration `ℱ` (the paper's (2)). -/
structure Model (Ω : Type*) [m0 : MeasurableSpace Ω] where
  /-- The filtration `ℱ_t` of the PoS awards ((2), p. 6). -/
  ℱ : Filtration ℕ m0
  /-- The initial number of coins outstanding `N = N_0`. -/
  N₀ : ℝ
  /-- The tracked investor's initial endowment `n_0`. -/
  n₀ : ℝ
  /-- The deterministic coin reward `R_t` (used for `t ≥ 1`). -/
  R : ℕ → ℝ
  /-- The selection indicator `1_{S_t}` of the tracked investor (used for `t ≥ 1`). -/
  ξ : ℕ → Ω → ℝ
  N₀_pos : 0 < N₀
  n₀_nonneg : 0 ≤ n₀
  n₀_le : n₀ ≤ N₀
  R_nonneg : ∀ t, 0 ≤ R t
  ξ_mem : ∀ t ω, ξ t ω = 0 ∨ ξ t ω = 1
  ξ_meas : ∀ t, StronglyMeasurable[ℱ t] (ξ t)

/-- The total number of coins outstanding, `N_t = N_0 + Σ_{n=1}^t R_n`, i.e. `N_t = N_{t−1} + R_t`
(proof of Proposition 1, p. 17). Deterministic. -/
def coinSupply (N₀ : ℝ) (R : ℕ → ℝ) (t : ℕ) : ℝ :=
  N₀ + ∑ n ∈ Finset.Icc 1 t, R n

/-- The tracked buy-and-hold investor's coins, by (5) (p. 7): `n_0` at `t = 0` and
`n_{t+1} = n_t + R_{t+1} 1_{S_{t+1}}`. -/
def coins {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) : ℕ → Ω → ℝ
  | 0 => fun _ => M.n₀
  | t + 1 => fun ω => coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω

/-- The investor share `π_t = n_t / N_t` ((1), p. 6). -/
noncomputable def share {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) : ℝ :=
  coins M t ω / coinSupply M.N₀ M.R t

/-- The Proof-of-Stake selection rule (p. 6): before trading at `t + 1` the tracked investor is
selected with probability `π_t`, encoded as `E[1_{S_{t+1}} | ℱ_t] = π_t` almost surely. -/
def IsPoS {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (M : Model Ω) : Prop :=
  ∀ t : ℕ, μ[M.ξ (t + 1) | M.ℱ t] =ᵐ[μ] share M t

/-- The power reward rule of Proposition 4 (p. 14) and Lemma 5 (p. 22):
`R_t = ρ N_{t−1}^γ` for every `t ≥ 1` (real power `Real.rpow`). -/
def IsPowerReward (ρ γ N₀ : ℝ) (R : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → R t = ρ * coinSupply N₀ R (t - 1) ^ γ

end PoSShares.Stability


