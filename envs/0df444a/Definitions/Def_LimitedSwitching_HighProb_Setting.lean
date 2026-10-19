-- Prove2me | Definitions.Def_LimitedSwitching_HighProb_Setting
-- name    : LimitedSwitching_HighProb_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:22.014354+00:00
-- url     : https://prove2.me/theorems/a852e0ea-f9d6-4f96-a07e-8ae89e16d87b
-- title:
--   §1–§2, pp. 3–13 — prediction from experts against an oblivious adversary: online algorithms, regret, switches, FPL, FPL* (sign corrected), Framework 1, BFPL*
-- statement:
--   This file sets up **prediction from experts** (PFE) with $n$ actions against an **oblivious adversary**, and the algorithms of §2 of Altschuler–Talwar.
--
--   1. **Losses.** A loss sequence is $(\ell_t)_{t\ge1}$ with $\ell_t:[n]\to[0,1]$ (p. 3). The adversary is oblivious: it fixes the whole sequence before the game (p. 5).
--   2. **Online algorithms.** A randomized online algorithm draws internal randomness $\omega$ from a probability space $(\Omega,\mu)$. At round $t$ it chooses an action $i_t\in[n]$ as a function of $\omega$ and the past losses $\ell_1,\dots,\ell_{t-1}$ only (full-information feedback).
--   3. **Regret and switches.** For an action sequence $(i_t)$,
--   $$\mathrm{Regret}_T=\sum_{t=1}^T\ell_t(i_t)-\min_{i\in[n]}\sum_{t=1}^T\ell_t(i),\qquad \mathrm{Switches}_T=\#\{t\in\{2,\dots,T\}: i_t\neq i_{t-1}\}.$$
--   4. **FPL** (p. 12). With perturbations $P_t(i)$ and the fake round $\ell_0:=0$ (p. 8), Follow the Perturbed Leader plays at round $t$ the minimiser of $\sum_{s=0}^{t-1}(\ell_s(i)+P_{s+1}(i))$. Ties go to the smallest index.
--   5. **FPL$^*_\varepsilon$** (p. 13). Draw $R(1),\dots,R(n)$ i.i.d. standard exponential, set $P_1(i)=-R(i)/\varepsilon$ and $P_t=0$ for $t>1$. At round $t$ it plays the minimiser of $-R(i)/\varepsilon+\sum_{s=1}^{t-1}\ell_s(i)$.
--   6. **Framework 1** (Figure 2, p. 9). Given an algorithm $\mathcal A$ and a budget $S'$, run a copy of $\mathcal A$ with fresh randomness. The copy sees only the losses of its own epoch. The epoch continues while that copy has made at most $S'$ switches. At the round where the copy would make a switch that takes its count above $S'$, a new epoch starts there instead, and a fresh copy plays its first action. $E$ denotes the number of epochs used in rounds $1,\dots,T$.
--   7. **BFPL$^*_\delta$** (p. 13). Framework 1 applied to FPL$^*_\varepsilon$, with $N=\lceil\log(2/\delta)\rceil$,
--   $$\varepsilon=\tfrac12\sqrt{\frac{N\log n}{T}},\qquad S'=135\sqrt{\frac{T\log n}{N}},$$
--   and independent exponential vectors $R_e$, one for each epoch $e$.
--
--   These are the objects of the paper's high-probability guarantee for regret and switching (Theorems 1 and 8).
--
--   **Formalization Note** Rounds are 1-based, and an algorithm's type gives it at round $t$ only $\omega$ and $\ell_1,\dots,\ell_{t-1}$. Epochs are 0-based, with randomness $\omega:\mathbb N\to\Omega$ under the infinite product measure. Two corrections are made. (i) The paper prints $P_1(i)=+R(i)/\varepsilon$. With a one-sided exponential law that variant violates Lemma 7, which the paper cites from Kalai–Vempala, so the sign is corrected to $-R(i)/\varepsilon$. (ii) The paper ignores integrality (p. 8). Here $N=\lceil\log(2/\delta)\rceil$ is a natural number, used in both $\varepsilon$ and $S'$. The epoch rule "stop when use $S'$ switches" is pinned by the proof of Lemma 4 (p. 11): an epoch reaches length $L$ iff its copy makes at most $S'$ switches in its first $L$ rounds. A switch at an epoch boundary is a switch of the batched algorithm, but it is not counted against the new copy's budget.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, pp. 3, 5, 8, 9, 12, 13, §1, Notation, Framework 1 (Figure 2), §2.3, §2.4

import Mathlib

namespace LimitedSwitching.HighProb

open MeasureTheory ProbabilityTheory

/-- An oblivious loss sequence for prediction from experts with `n` actions: `ℓ t i ∈ [0, 1]`
for rounds `t ≥ 1` (p. 3). The value `ℓ 0` is never read by the protocol. -/
def IsLossSeq {n : ℕ} (ℓ : ℕ → Fin n → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1

/-- A randomized full-information online algorithm with internal randomness `ω : Ω`. At round `t`
it sees `ω` and the past loss vectors `ℓ_1, …, ℓ_{t-1}` (as a function on `Fin (t - 1)`), and
nothing else, and returns the action it plays at round `t`. -/
abbrev OnlineAlg (Ω : Type*) (n : ℕ) : Type _ := Ω → (t : ℕ) → (Fin (t - 1) → Fin n → ℝ) → Fin n

/-- The action played at round `t` by the algorithm `A`, with randomness `ω`, against the loss
sequence `ℓ`: the algorithm is fed `ℓ_1, …, ℓ_{t-1}`. -/
def play {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (ω : Ω) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) : Fin n :=
  A ω t (fun s => ℓ (s.val + 1))

/-- `Regret_T` of an action sequence `a` against `ℓ` (p. 3):
`∑_{t=1}^T ℓ_t(a_t) − min_i ∑_{t=1}^T ℓ_t(i)`. -/
noncomputable def regret {n : ℕ} (T : ℕ) (ℓ : ℕ → Fin n → ℝ) (a : ℕ → Fin n) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ℓ t (a t) - ⨅ i, ∑ t ∈ Finset.Icc 1 T, ℓ t i

/-- `Switches_T` of an action sequence `a` (p. 8): the number of rounds `t ∈ {2, …, T}` with
`a_t ≠ a_{t-1}`. -/
def switches {n : ℕ} (T : ℕ) (a : ℕ → Fin n) : ℕ :=
  ((Finset.Icc 2 T).filter (fun t => a t ≠ a (t - 1))).card

/-- The lowest-index minimiser of `v : Fin n → ℝ` (ties broken towards the smallest index). -/
noncomputable def argminFin {n : ℕ} [NeZero n] (v : Fin n → ℝ) : Fin n :=
  (Finset.univ.filter (fun i => v i = Finset.univ.inf' Finset.univ_nonempty v)).min' (by
    obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
    exact ⟨i, by simp [h]⟩)

/-- Follow the Perturbed Leader with perturbations `P` (p. 12): at round `t` it plays the
(lowest-index) argmin of `∑_{s=0}^{t-1} (ℓ_s + P_{s+1})`, with the fake round `ℓ_0 := 0` (p. 8).
Defined for every `t`, so `fplPlay P ℓ (T + 1)` is the perturbed leader after round `T`. -/
noncomputable def fplPlay {n : ℕ} [NeZero n] (P : ℕ → Fin n → ℝ) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) :
    Fin n :=
  argminFin (fun i => ∑ s ∈ Finset.range t, ((if s = 0 then 0 else ℓ s i) + P (s + 1) i))

/-- Multiplicative FPL, `FPL*_ε` (p. 13), **sign corrected**: initial perturbation
`P_1(i) = −R(i)/ε` and `P_t = 0` for `t > 1`, with randomness `R : Fin n → ℝ`. At round `t` it plays
the lowest-index argmin of `−R(i)/ε + ∑_{s=1}^{t-1} ℓ_s(i)`. -/
noncomputable def fplStar {n : ℕ} [NeZero n] (ε : ℝ) : OnlineAlg (Fin n → ℝ) n :=
  fun R t past => argminFin (fun i => -(R i) / ε + ∑ s : Fin (t - 1), past s i)

/-- The standard exponential law `Exp(1)` is a probability measure. -/
instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- The joint law of `n` i.i.d. standard exponentials `R(1), …, R(n)`. -/
noncomputable def expLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => expMeasure 1)

/-- `expLaw n` is a probability measure. -/
instance (n : ℕ) : IsProbabilityMeasure (expLaw n) := by
  unfold expLaw; infer_instance

/-- State of Framework 1 after a round: the current epoch (`0`-based), the first round of that
epoch, the number of switches the current copy of the subroutine has made in it, and the action
played in the round. -/
structure BState (n : ℕ) where
  epoch : ℕ
  start : ℕ
  count : ℕ
  act : Fin n

/-- The action the copy of `A` run in epoch `e` (randomness `ω e`), started at round `st`, plays at
round `r ≥ st`: it is at its own round `r − st + 1` and has seen `ℓ_st, …, ℓ_{r−1}`. -/
def localAct {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ)
    (e st r : ℕ) : Fin n :=
  A (ω e) (r - st + 1) (fun s => ℓ (st + s.val))

/-- Framework 1 (Figure 2, p. 9) run against `ℓ`: `batchRun A S' ω ℓ k` is the state after round
`k + 1`. Epoch `e` runs a fresh copy of `A` with randomness `ω e`, which sees only the losses since
its epoch began. **Epoch rule** (pinned by the proof of Lemma 4, p. 11): an epoch continues while
its copy has made at most `S'` switches; the round at which the copy would make a switch that brings
its count above `S'` instead opens the next epoch, in which a fresh copy plays its first action. -/
noncomputable def batchRun {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S' : ℝ) (ω : ℕ → Ω)
    (ℓ : ℕ → Fin n → ℝ) : ℕ → BState n
  | 0 => ⟨0, 1, 0, localAct A ω ℓ 0 1 1⟩
  | k + 1 =>
    let st := batchRun A S' ω ℓ k
    let c := localAct A ω ℓ st.epoch st.start (k + 2)
    let k' := st.count + if c ≠ st.act then 1 else 0
    if (k' : ℝ) ≤ S' then ⟨st.epoch, st.start, k', c⟩
    else ⟨st.epoch + 1, k + 2, 0, localAct A ω ℓ (st.epoch + 1) (k + 2) (k + 2)⟩

/-- Extend a finite history `ℓ_1, …, ℓ_m` (given as a function on `Fin m`) to a loss sequence on
`ℕ`, by zero outside `{1, …, m}`. -/
def padPast {n m : ℕ} (past : Fin m → Fin n → ℝ) : ℕ → Fin n → ℝ :=
  fun s => if h : 1 ≤ s ∧ s ≤ m then past ⟨s - 1, by omega⟩ else 0

/-- Framework 1 as an online algorithm with randomness `ω : ℕ → Ω` (fresh randomness `ω e` for
epoch `e`): at round `t` it replays the run on the past losses `ℓ_1, …, ℓ_{t-1}` and plays the
action of round `t`. -/
noncomputable def batch {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S' : ℝ) : OnlineAlg (ℕ → Ω) n :=
  fun ω t past => (batchRun A S' ω (padPast past) (t - 1)).act

/-- `E`, the number of epochs Framework 1 uses in rounds `1, …, T`. -/
noncomputable def numEpochs {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S' : ℝ) (ω : ℕ → Ω)
    (ℓ : ℕ → Fin n → ℝ) (T : ℕ) : ℕ :=
  (batchRun A S' ω ℓ (T - 1)).epoch + 1

/-- `N = ⌈log(2/δ)⌉`, the number of epochs BFPL*_δ budgets for (integrality pinned). -/
noncomputable def bfplN (δ : ℝ) : ℕ := ⌈Real.log (2 / δ)⌉₊

/-- `ε = ½ √(log n · N / T)` (p. 13, with `N` for `log(2/δ)`). -/
noncomputable def bfplEps (T n : ℕ) (δ : ℝ) : ℝ := (1 / 2) * √(Real.log n * bfplN δ / T)

/-- `S' = 135 √(T log n / N)` (p. 13, with `N` for `log(2/δ)`). -/
noncomputable def bfplS (T n : ℕ) (δ : ℝ) : ℝ := 135 * √(T * Real.log n / bfplN δ)

/-- Batched Multiplicative Follow the Perturbed Leader, BFPL*_δ (p. 13): Framework 1 applied to
the (sign-corrected) `FPL*_ε` with `ε = bfplEps T n δ` and `S' = bfplS T n δ`. -/
noncomputable def bfplStar (T n : ℕ) [NeZero n] (δ : ℝ) : OnlineAlg (ℕ → Fin n → ℝ) n :=
  batch (fplStar (bfplEps T n δ)) (bfplS T n δ)

/-- The law of BFPL*_δ's randomness: independent `n`-vectors of i.i.d. standard exponentials, one
per epoch. -/
noncomputable def bfplLaw (n : ℕ) : Measure (ℕ → Fin n → ℝ) :=
  Measure.infinitePi (fun _ => expLaw n)

end LimitedSwitching.HighProb


