-- Prove2me | Definitions.Def_LeiBR_Async_Algorithm
-- name    : LeiBR_Async_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:24.238827+00:00
-- url     : https://prove2.me/theorems/075fa32c-aa3a-4f65-802d-51b09fab81da
-- title:
--   Assumption 4, the update counter $\beta_{i,k}$, the outdated profile $y^i_k$, Algorithm 3, the SA scheme (43), $\rho$, $\hat\epsilon$ and $\ell^{(1)}_i(\eta)$
-- statement:
--   This definition fixes the asynchronous protocol of §5 and the quantities of its analysis.
--
--   **Schedule and delays.** At each time $k = 0,1,2,\dots$ a set $I_k \subseteq \{1,\dots,N\}$ of players updates. Player $i \in I_k$ sees only the outdated profile
--   $$y^i_k = \big(x_{1,k-\tau_{i1}(k)}, \dots, x_{N,k-\tau_{iN}(k)}\big),$$
--   with delays $0 \le \tau_{ij}(k) \le k$ and $\tau_{ii}(k) = 0$. **Assumption 4** requires: (a) the sets $I_k$ are deterministic; (b) $B_1 \ge 1$ and every player updates at least once in every window of $B_1$ consecutive times; (c) $\tau_{ij}(k) \le B_2$ whenever $i \in I_k$. The counter $\beta_{i,k}$ is the number of updates player $i$ has carried out up to and including time $k$.
--
--   **Algorithm 3.** Given a filtration $(\mathcal F_k)$ and deterministic accuracies $\alpha_{i,k}$, the iterates $x_k$ lie in $X$, $x_k$ is $\mathcal F_k$-measurable, and
--   $$\mathbb E\big[\|x_{i,k+1} - \hat x_i(y^i_k)\|^2 \,\big|\, \mathcal F_k\big] \le \alpha_{i,k}^2 \ \text{a.s. if } i \in I_k, \qquad x_{i,k+1} = x_{i,k}\ \text{ if } i \notin I_k. \tag{38}$$
--
--   **The SA scheme (43).** In major iteration $k$, player $i \in I_k$ starts from $z_{i,1} = x_{i,k}$ and takes stochastic projected gradient steps
--   $$z_{i,t+1} = \Pi_{X_i}\Big[z_{i,t} - \gamma_t\big(\nabla_{x_i}\psi_i(z_{i,t}, y^i_{-i,k}; \xi^t_{i,k}) + \mu(z_{i,t} - x_{i,k})\big)\Big],\qquad \gamma_t = \frac{1}{\mu(t+1)} .$$
--   The oracle condition of Lemma 8 asks, for $t = 1,\dots,j$ and $\sigma$-algebras $\mathcal G_t$ playing the role of $\sigma\{\mathcal F_k, \xi^{[t-1]}_{i,k}\}$, that the sampled gradient $g_t$ have integrable squared norm, $\mathbb E[g_t \mid \mathcal G_t] = \nabla_{x_i} f_i(z_{i,t}, y^i_{-i,k})$ and $\mathbb E[\|g_t\|^2 \mid \mathcal G_t] \le M_i^2$ a.s. The number of steps in iteration $k$ is $j_{i,k} = \lceil Q_i/\eta^{2(k+1)}\rceil$.
--
--   **Constants.** With $n_0 = \lceil B_2/B_1\rceil$,
--   $$\rho = \big(\max\{a_\infty, \eta\}\big)^{1/(n_0+1)},\qquad \hat\epsilon = \frac{\epsilon}{C + D}\,\rho^{\frac{B_1-1}{B_1}},$$
--   $$\ell^{(1)}_i(\eta) = \frac{Q_i}{\eta^4\ln(1/\eta^2)}\Big(\frac{1}{\hat\epsilon}\Big)^{\frac{\ln(1/\eta^2)}{\ln(1/q)}} + \Big\lceil\frac{\ln(1/\hat\epsilon)}{\ln(1/q)}\Big\rceil .$$
--
--   These are the objects in which Lemma 7, Lemma 8 and Theorem 3 are stated.
--
--   **Formalization Note** The delays are deterministic functions $\tau_{ij}(k)$; the page allows random delays, but its proof step (C.5) is valid only when the delays do not depend on the iterates. Assumption 4(b)'s per-player lengths $b_i \le B_1$ are replaced by $B_1$, which is equivalent. Algorithm 3 is a predicate on a random sequence of profiles (`IsAlgorithm3`), with the filtration a parameter to which the iterates are adapted. The SA iterates are a recursive function with $z_1$ the centre (the value at $t=0$ is unused). The page's literal second-moment hypothesis "$= \|\nabla_{x_i} f_i\|^2$" forces zero noise and is replaced by the bound $\le M_i^2$ that the proof uses; $\psi_i$ in the page's hypotheses is read as $\nabla_{x_i}\psi_i$. Exponents $1/(n_0+1)$, $(B_1-1)/B_1$ and the power in $\ell^{(1)}_i$ are real powers; the ceilings are natural-number ceilings.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 17 (I_k, y^i_k, τ_ij(k), Algorithm 3, (38)), p. 18 (Assumption 4, β_{i,k}, ρ and n_0 in Lemma 7, (43)), p. 19 (Lemma 8, j_{i,k}, (45), (46))

import Mathlib
import Definitions.Def_LeiBR_Async_Game

namespace LeiBR.Async

open MeasureTheory

/-- **Assumption 4** (Lei, Shanbhag, Pang & Sen, arXiv:1704.04578v2, p. 18) on a deterministic update
schedule `I : ℕ → Finset (Fin N)` (`I k` = the players updating at time `k`) and deterministic delays
`τ i j k = τ_ij(k)`:

(a) the schedule is deterministic (it is a function of `k` only);
(b) `B₁ ≥ 1` and every player updates at least once in every window `[k₀, k₀ + B₁)` of `B₁`
consecutive times;
(c) `τ_ij(k) ≤ B₂` whenever `i ∈ I_k`.

Formalization Note: the page lets the delays be random with a random bound `τ_ij ≤ B₂`; here they are
deterministic (the proof's step (C.5) needs them to be independent of the iterates). The page's
per-player window lengths `b_i ≤ B₁` are replaced by `B₁`, which is equivalent. -/
structure Assumption4 {N : ℕ} (I : ℕ → Finset (Fin N)) (τ : Fin N → Fin N → ℕ → ℕ)
    (B1 B2 : ℕ) : Prop where
  B1_pos : 0 < B1
  window : ∀ (i : Fin N) (k₀ : ℕ), ∃ k, k₀ ≤ k ∧ k < k₀ + B1 ∧ i ∈ I k
  delay_le : ∀ k, ∀ i ∈ I k, ∀ j, τ i j k ≤ B2

/-- `β_{i,k}`: the number of updates player `i` has carried out up to and including time `k` (p. 18),
`#{l ≤ k : i ∈ I_l}`. -/
def updCount {N : ℕ} (I : ℕ → Finset (Fin N)) (i : Fin N) (k : ℕ) : ℕ :=
  ((Finset.range (k + 1)).filter (fun l => i ∈ I l)).card

/-- The outdated profile `y^i_k = (x_{1,k−τ_{i1}(k)}, …, x_{N,k−τ_{iN}(k)})` available to player `i` at
time `k` (p. 17). -/
def delayed {Ω : Type*} {N : ℕ} {n : Fin N → ℕ} (x : ℕ → Ω → LeiBR.Sync.Profile n)
    (τ : Fin N → Fin N → ℕ → ℕ) (i : Fin N) (k : ℕ) (ω : Ω) : LeiBR.Sync.Profile n :=
  fun j => x (k - τ i j k) ω j

/-- **Algorithm 3** (asynchronous inexact proximal BR scheme, p. 17), as a property of a random
sequence of profiles `x k : Ω → LeiBR.Sync.Profile n` adapted to a filtration `F`:

* the delays satisfy `τ_ij(k) ≤ k` and `τ_ii(k) = 0` (p. 17);
* every iterate lies in `X` (in particular `x_{i,0} ∈ X_i`);
* `x_k` is `F_k`-measurable;
* (38): if `i ∈ I_k`, then `E[‖x_{i,k+1} − x̂_i(y^i_k)‖² | F_k] ≤ α²_{i,k}` a.s.;
* otherwise `x_{i,k+1} = x_{i,k}`.

`α i k = α_{i,k}` is deterministic and `xhat` is the proximal BR map (7). -/
structure IsAlgorithm3 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℕ mΩ)
    {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (I : ℕ → Finset (Fin N)) (τ : Fin N → Fin N → ℕ → ℕ) (α : Fin N → ℕ → ℝ)
    (x : ℕ → Ω → LeiBR.Sync.Profile n) : Prop where
  delay_le_k : ∀ i j k, τ i j k ≤ k
  delay_self : ∀ i k, τ i i k = 0
  mem : ∀ k ω, x k ω ∈ profileSet X
  adapted : ∀ k, Measurable[F k] (x k)
  inexact : ∀ k, ∀ i ∈ I k,
    P[fun ω => ‖x (k + 1) ω i - xhat (delayed x τ i k ω) i‖ ^ 2 | F k] ≤ᵐ[P] fun _ => α i k ^ 2
  idle : ∀ k, ∀ i ∉ I k, ∀ ω, x (k + 1) ω i = x k ω i

/-- `n₀ = ⌈B₂/B₁⌉` (Lemma 7, p. 18). -/
noncomputable def nZero (B1 B2 : ℕ) : ℕ := ⌈(B2 : ℝ) / (B1 : ℝ)⌉₊

/-- `ρ = (max{a_∞, η})^{1/(n₀+1)}` (Lemma 7, p. 18), a real power. -/
noncomputable def rhoAsync (aInf η : ℝ) (B1 B2 : ℕ) : ℝ :=
  (max aInf η) ^ (1 / ((nZero B1 B2 : ℝ) + 1))

/-- The stochastic approximation iterates of (43) (p. 18) for a generic player space `V`:
`z_1 = c` (the prox centre `x_{i,k}`) and, for `t ≥ 1`,
`z_{t+1} = Π[z_t − γ_t (G(z_t, ξ^t) + μ(z_t − c))]` with `γ_t = 1/(μ(t+1))`, where `G(z, s)` is the
sampled gradient at `z` for the sample `s`. The value at `t = 0` is not used (set to `c`). -/
noncomputable def saIter {V S : Type*} [AddCommGroup V] [Module ℝ V] (proj : V → V)
    (G : V → S → V) (μ : ℝ) (c : V) (ξ : ℕ → S) : ℕ → V
  | 0 => c
  | 1 => c
  | (t + 2) =>
      proj (saIter proj G μ c ξ (t + 1) -
        (1 / (μ * ((t : ℝ) + 2))) •
          (G (saIter proj G μ c ξ (t + 1)) (ξ (t + 1)) + μ • (saIter proj G μ c ξ (t + 1) - c)))

/-- Player `i`'s path (43) in a major iteration with (delayed) profile `y`: `z_1 = y_i` and the
sampled gradient at `z` is `∇_{x_i}ψ_i(z, y_{-i}; s) = gψ i (Function.update y i z) s`, with the
projection `proj i = Π_{X_i}`. -/
noncomputable def saPath {N d : ℕ} {n : Fin N → ℕ} (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (μ : ℝ) (i : Fin N)
    (y : LeiBR.Sync.Profile n) (ξ : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → LeiBR.Sync.Strat n i :=
  saIter (proj i) (fun z s => gψ i (Function.update y i z) s) μ (y i) ξ

/-- The sampled-gradient oracle hypotheses of Lemma 8 (p. 19), repaired as in Lemma 3: for the path
`z_t` of (43) started from the random profile `y` with samples `ξ^t = ξ t`, and for `t = 1, …, j`,
writing `g_t = ∇_{x_i}ψ_i(z_t, y_{-i}; ξ^t)`,

* `‖g_t‖²` is integrable;
* `E[g_t | G_t] = ∇_{x_i} f_i(z_t, y_{-i})` a.s. (unbiasedness);
* `E[‖g_t‖² | G_t] ≤ M_i²` a.s.

Here `G t` plays the role of `σ{F_k, ξ^{[t−1]}_{i,k}}`. -/
def IsSAOracle {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {N d : ℕ} {n : Fin N → ℕ}
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i) (μ : ℝ) (M : Fin N → ℝ) (i : Fin N)
    (y : Ω → LeiBR.Sync.Profile n) (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (G : ℕ → MeasurableSpace Ω)
    (j : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ j →
    Integrable (fun ω => ‖gψ i (Function.update (y ω) i
        (saPath proj gψ μ i (y ω) (fun s => ξ s ω) t)) (ξ t ω)‖ ^ 2) P ∧
    P[fun ω => gψ i (Function.update (y ω) i (saPath proj gψ μ i (y ω) (fun s => ξ s ω) t))
        (ξ t ω) | G t] =ᵐ[P]
      (fun ω => partialGrad (f i) i
        (Function.update (y ω) i (saPath proj gψ μ i (y ω) (fun s => ξ s ω) t))) ∧
    P[fun ω => ‖gψ i (Function.update (y ω) i (saPath proj gψ μ i (y ω) (fun s => ξ s ω) t))
        (ξ t ω)‖ ^ 2 | G t] ≤ᵐ[P] fun _ => M i ^ 2

/-- `j_{i,k} = ⌈Q_i/η^{2(k+1)}⌉`, the number of steps of (43) taken by player `i` in major iteration
`k` (proof of Theorem 3, p. 19). -/
noncomputable def jSteps {N : ℕ} (Q : Fin N → ℝ) (η : ℝ) (i : Fin N) (k : ℕ) : ℕ :=
  ⌈Q i / η ^ (2 * (k + 1))⌉₊

/-- `ϵ̂ = ϵ ρ^{(B₁−1)/B₁}/(C + D)` of (46) (p. 19). -/
noncomputable def epsHat (ϵ C D ρ : ℝ) (B1 : ℕ) : ℝ :=
  ϵ / (C + D) * ρ ^ (((B1 : ℝ) - 1) / B1)

/-- The bound (45) (p. 19):
`ℓ^{(1)}_i(η) = Q_i/(η⁴ ln(1/η²)) · (1/ϵ̂)^{ln(1/η²)/ln(1/q)} + ⌈ln(1/ϵ̂)/ln(1/q)⌉`. -/
noncomputable def ellOne (Qi η q ϵhat : ℝ) : ℝ :=
  Qi / (η ^ 4 * Real.log (1 / η ^ 2)) * (1 / ϵhat) ^ (Real.log (1 / η ^ 2) / Real.log (1 / q)) +
    (⌈Real.log (1 / ϵhat) / Real.log (1 / q)⌉₊ : ℝ)

end LeiBR.Async


