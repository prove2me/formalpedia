-- Prove2me | Definitions.Def_CalibratedMA_Randomized_Algorithm1
-- name    : CalibratedMA_Randomized_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:21.084979+00:00
-- url     : https://prove2.me/theorems/30939d94-5f91-42e7-8ac4-1afa52a5a823
-- title:
--   Lemma 3.4's greedy partition and Algorithm 1 — learning a randomized calibrated-multiaccurate predictor
-- statement:
--   **Greedy partition** (proof of Lemma 3.4). Let $\nu$ be a distribution on $[0,1]$, $m\ge2$, and $\Lambda_\rho$ a grid with $1/\rho=K$ an integer. Set $\tau=1/(64m^2)$ and $\gamma_0=0$. Given $\gamma_j<1$, let $\gamma_{j+1}$ be the smallest grid point $b\in\Lambda_\rho$ with $b>\gamma_j$ such that
--   $$\mathbb E_{S\sim\nu}\Big[\frac{(S-\gamma_j)(b-S)}{b-\gamma_j}\mathbf 1\{\gamma_j<S<b\}\Big]\ge\tau;$$
--   if there is no such grid point, $\gamma_{j+1}=1$. The construction stops when the right endpoint reaches $1$.
--
--   **Algorithm 1.** The input is $n$ labeled examples $(X_t,Y_t)$, a finite test class $\mathcal G$ and a failure probability $\delta$.
--   1. Set $m=\max\{2,\lceil (n/\log(2n/\delta))^{1/5}\rceil\}$, $\rho=m^{-2}$, $M_*=4m+2$, and $\mathcal A=\mathcal A_{M_*,\rho}$.
--   2. Run the online rule of Lemma 3.1 on all $n$ examples with $\Phi_{\mathcal G,\mathcal A}=\{(x,s)\mapsto g(x):g\in\mathcal G\}\cup\{(x,s)\mapsto a(s):a\in\mathcal A\}$. Save the rules $s_1,\dots,s_n$ and the scores $S_t=s_t(X_t)$.
--   3. Apply the greedy construction with parameters $m,\rho$ to $\hat\nu=n^{-1}\sum_{t=1}^n\delta_{S_t}$, obtaining $\hat\Gamma$.
--   4. Output the randomized predictor $Q$ that, on input $x$, draws $J$ uniformly from $\{1,\dots,n\}$ and then $P=\mathrm{Round}_{\hat\Gamma}(s_J(x))$ with fresh randomness, i.e.
--   $$Q_x=\frac1n\sum_{t=1}^n\mathrm{Law}\big(\mathrm{Round}_{\hat\Gamma}(s_t(x))\big).$$
--
--   The goal theorem (Theorem 4.1) is a statement about this output.
--
--   **Formalization Note.** Partition points are tracked by grid indices: `greedyIdx` is the index sequence (it stays at $K$ once $1$ is reached), and the number of intervals is the number of indices below $K$. Here $1/\rho=K=m^2$ is an integer. Training uses no randomness, so `algorithm1 n δ G ω` is a deterministic function of the sample `ω : Fin n → X × ℝ`.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 16 (proof of Lemma 3.4, 'Equalizing the interval contributions') and p. 18, Algorithm 1

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Rounding
import Definitions.Def_CalibratedMA_Randomized_OnlineRule

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized

/-! # The greedy partition of Lemma 3.4 and Algorithm 1

Lu, Noarov, Roth, *Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity*,
STOC 2027 submission #900, proof of Lemma 3.4 (p. 16) and Algorithm 1 (p. 18).

The fine grid is `Λ_ρ` with `ρ = 1/K`; partition points are tracked by their grid indices.
The greedy construction accepts a real scale `m ≥ 2`, as in Lemma 3.4. Algorithm 1
uses the natural-number scale `algM`, coerced to ℝ for this construction. -/

/-- The contribution `E_ν[(S − a)(b − S)/(b − a) · 1{a < S < b}]` of a candidate interval
`(a, b)`. -/
noncomputable def contribution (ν : Measure ℝ) (a b : ℝ) : ℝ :=
  ∫ s, (if a < s ∧ s < b then (s - a) * (b - s) / (b - a) else 0) ∂ν

open Classical in
/-- One greedy step from the left endpoint with grid index `i < K`: the smallest grid index
`k ∈ (i, K]` whose interval `(i/K, k/K)` has contribution at least `τ`; if there is none, `K`
(the right endpoint `1`). -/
noncomputable def greedyNext (ν : Measure ℝ) (K : ℕ) (τ : ℝ) (i : ℕ) : ℕ :=
  let C := (Finset.Ioc i K).filter
    (fun k : ℕ => τ ≤ contribution ν ((i : ℝ) / K) ((k : ℝ) / K))
  if h : C.Nonempty then C.min' h else K

/-- The grid indices of the greedy partition points, `τ = 1/(64 m²)`, starting from `γ_0 = 0`;
once the right endpoint `1` (index `K`) is reached the sequence stays at `K`. -/
noncomputable def greedyIdx (ν : Measure ℝ) (m : ℝ) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    let i := greedyIdx ν m K j
    if i < K then greedyNext ν K (1 / (64 * m ^ 2)) i else K

/-- The number `M` of intervals of the greedy partition: the number of steps before index `K`
is reached (each step strictly increases the index, so `M ≤ K`). -/
noncomputable def greedyNumIntervals (ν : Measure ℝ) (m : ℝ) (K : ℕ) : ℕ :=
  ((Finset.range (K + 1)).filter (fun j => greedyIdx ν m K j < K)).card

/-- The greedy partition `Γ = (γ_0, …, γ_M)` of the proof of Lemma 3.4 for the distribution `ν`,
the parameter `m` and the grid `Λ_{1/K}`: `γ_j = (greedyIdx j)/K`. -/
noncomputable def greedyPartition (ν : Measure ℝ) (m : ℝ) (K : ℕ) : ℕ × (ℕ → ℝ) :=
  (greedyNumIntervals ν m K, fun j => (greedyIdx ν m K j : ℝ) / K)

/-- Algorithm 1, step 2: `m = max{2, ⌈(n / log(2n/δ))^{1/5}⌉}`. -/
noncomputable def algM (n : ℕ) (δ : ℝ) : ℕ :=
  max 2 ⌈((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ)⌉₊

variable {X : Type*}

open Classical in
/-- `Φ_{G,A} = {(x, s) ↦ g(x) : g ∈ G} ∪ {(x, s) ↦ a(s) : a ∈ A}` (as a finite set of
functions). -/
noncomputable def testFamily (G : Finset (X → ℝ)) (A : Finset (ℝ → ℝ)) :
    Finset (X → ℝ → ℝ) :=
  G.image (fun g => fun x _ => g x) ∪ A.image (fun a => fun _ s => a s)

/-- The online test family used by Algorithm 1 with `n` examples and failure probability `δ`:
`Φ_{G,A}` with `A = A_{M∗,ρ}`, `ρ = m^{-2}` (so `1/ρ = K = m²`), `M∗ = 4m + 2`. -/
noncomputable def algTests (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) : Finset (X → ℝ → ℝ) :=
  testFamily G (liftedClass (algM n δ ^ 2) (4 * algM n δ + 2))

/-- Algorithm 1, step 4: the empirical score distribution `ν̂ = n⁻¹ Σ_t δ_{S_t}` and the greedy
partition `Γ̂` (parameters `m` and `ρ = m^{-2}`). -/
noncomputable def algPartition (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) (ω : Fin n → X × ℝ) :
    ℕ × (ℕ → ℝ) :=
  let Φ := algTests n δ G
  let νhat : Measure ℝ := (n : ℝ≥0∞)⁻¹ • ∑ t : Fin n, Measure.dirac (onlineScore n Φ ω t)
  greedyPartition νhat (algM n δ) (algM n δ ^ 2)

/-- Algorithm 1 (p. 18): on the sample `ω` of `n` labeled examples, run the online rule of
Lemma 3.1 with `N = n` and `Φ = Φ_{G,A}`, choose `Γ̂` greedily from the recorded scores, and
output the randomized predictor `Q_x = n⁻¹ Σ_{t} Law(Round_Γ̂(s_t(x)))`: draw `J` uniformly
from the `n` rounds and round `s_J(x)` with fresh randomness. -/
noncomputable def algorithm1 (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) (ω : Fin n → X × ℝ) :
    X → Measure ℝ :=
  let Φ := algTests n δ G
  let Γ := algPartition n δ G ω
  fun x => (n : ℝ≥0∞)⁻¹ • ∑ t : Fin n, roundMeasure Γ.1 Γ.2 (onlineRule n Φ ω t x)

end CalibratedMA.Randomized


