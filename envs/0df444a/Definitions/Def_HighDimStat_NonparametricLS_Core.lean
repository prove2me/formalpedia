-- Prove2me | Definitions.Def_HighDimStat_NonparametricLS_Core
-- name    : HighDimStat_NonparametricLS_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:28:55.612233+00:00
-- url     : https://prove2.me/theorems/91e8b1a9-45b7-4c83-a37a-4c5ea6494355
-- title:
--   Star-shaped classes, local Gaussian complexity and the least-squares estimate
-- statement:
--   This file collects Chapter 13's core vocabulary for nonparametric least squares over a
--   function class $F$ evaluated at $n$ fixed design points $x_1,\dots,x_n$.
--
--   - **`empiricalNormSq x g`** / **`empiricalNorm x g`**: the empirical $L^2(P_n)$ squared
--     seminorm $\|g\|_n^2 := \frac1n\sum_{i=1}^n g(x_i)^2$ and its square root $\|g\|_n$
--     (used throughout, e.g. the basic inequality (13.18), p. 423).
--   - **`IsStarShaped H`**: a function class $H$ is star-shaped (footnote 2, p. 422) if
--     $h\in H,\ \alpha\in[0,1]\implies \alpha h\in H$.
--   - **`shiftedClass F fStar`**: the $f^*$-shifted class $F^*:=F-\{f^*\}=\{f-f^*\mid f\in F\}$
--     (Eq. (13.15), p. 421).
--   - **`diffClass F`**: the symmetric difference class $\partial F:=F-F=\{f_1-f_2\mid
--     f_1,f_2\in F\}$ (Eq. (13.22), p. 424), used once $f^*$ is no longer assumed a member of
--     $F$ (Theorem 13.13).
--   - **`IsIIDStdGaussian P w`**: $n$ i.i.d. standard Gaussian variates $w_1,\dots,w_n$ on a
--     probability space $(\Omega,P)$ — the noise variables of the local Gaussian complexity.
--   - **`localGaussianComplexity x w P H δ`**: the local Gaussian complexity
--     $$
--     G_n(\delta;H) := \mathbb E_w\Big[\sup_{h\in H,\ \|h\|_n\le\delta}\Big|\tfrac1n\sum_{i=1}^n
--     w_i h(x_i)\Big|\Big]
--     $$
--     (Eq. (13.16), p. 421), with the supremum taken over the subtype of the radius-$\delta$
--     slice of $H$.
--   - **`SatisfiesCriticalInequality x w P H σ δ`**: $\delta>0$, the local Gaussian complexity's
--     defining supremum is `Integrable` (guarding, per Revision 1, against a non-measurable or
--     non-integrable integrand silently satisfying the inequality below via Mathlib's Bochner-
--     integral junk value `0` — see Formalization Note), and $G_n(\delta;H)/\delta\le
--     \delta/(2\sigma)$ — the critical inequality (13.17)/(13.42a), p. 422/433. A $\delta$
--     satisfying it is called *valid*.
--   - **`IsLeastSquaresEstimate x F y fHat`**: $\hat f\in F$ minimizes the empirical sum of
--     squared residuals $\sum_i(y_i-f(x_i))^2$ over $F$ (Eq. (13.7)) — the nonparametric
--     least-squares estimate.
--
--   **Formalization Note** The supremum defining $G_n$ is taken over the subtype
--   `{h // h ∈ H ∧ empiricalNorm x h ≤ δ}` rather than a `sSup` over a `Set ℝ` image, so it
--   is well-defined (never the junk value `0` of an unbounded or non-`BddAbove` `sSup`)
--   whenever this subtype is nonempty — guaranteed whenever `H` is star-shaped and nonempty,
--   since `α = 0` shows `0 ∈ H`. Design points `x : Fin n → X` range over an arbitrary
--   covariate type `X`; the estimate `fHat : Ω → (X → ℝ)` is data-dependent (a function of the
--   noise realization `ω`), matching the book's random estimator $\hat f_n$. **Revision 1**:
--   `X` and `H` carry no topology, separability or countability constraint, so
--   `localGaussianComplexity`'s outer `∫ ω, ⨆ h, |...| ∂P` can fail `AEStronglyMeasurable` for a
--   generic `H`, which Mathlib's Bochner integral then silently evaluates to `0` — a value that
--   trivially satisfies `0/δ≤δ/(2σ)` for every `δ,σ>0`. `SatisfiesCriticalInequality` therefore
--   carries an explicit `Integrable` hypothesis on that same supremum, ruling out this junk-value
--   route to satisfying the critical inequality before the numeric bound is even considered.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 421-425 (PDF pp. 441-445), Eqs. (13.7), (13.15), (13.16), (13.17), (13.22), footnote 2 p. 422

import Mathlib

namespace HighDimStat.NonparametricLS

open MeasureTheory ProbabilityTheory

/-- The empirical (`L²(Pₙ)`) squared seminorm `‖g‖ₙ²` of a function `g : X → ℝ` relative to `n`
fixed design points `x : Fin n → X` — the quantity `‖f − f*‖ₙ²` appearing throughout Chapter 13
(e.g. the basic inequality (13.18), p. 423). -/
noncomputable def empiricalNormSq {X : Type*} {n : ℕ} (x : Fin n → X) (g : X → ℝ) : ℝ :=
  (∑ i, (g (x i)) ^ 2) / n

/-- The empirical (`L²(Pₙ)`) seminorm `‖g‖ₙ`. -/
noncomputable def empiricalNorm {X : Type*} {n : ℕ} (x : Fin n → X) (g : X → ℝ) : ℝ :=
  Real.sqrt (empiricalNormSq x g)

/-- A function class `H` is star-shaped (footnote 2, p. 422) if for every `h ∈ H` and every
`α ∈ [0, 1]`, the rescaled function `αh` also belongs to `H`. -/
def IsStarShaped {X : Type*} (H : Set (X → ℝ)) : Prop :=
  ∀ h ∈ H, ∀ α ∈ Set.Icc (0 : ℝ) 1, (fun z => α * h z) ∈ H

/-- The `f*`-shifted function class `F* := F − {f*}` (Eq. (13.15), p. 421). -/
def shiftedClass {X : Type*} (F : Set (X → ℝ)) (fStar : X → ℝ) : Set (X → ℝ) :=
  (fun f => fun z => f z - fStar z) '' F

/-- The (symmetric) difference class `∂F := F − F = {f₁ − f₂ | f₁, f₂ ∈ F}` (Eq. (13.22),
p. 424), used in Theorem 13.13 when `f*` is not assumed known. -/
def diffClass {X : Type*} (F : Set (X → ℝ)) : Set (X → ℝ) :=
  {g | ∃ f1 ∈ F, ∃ f2 ∈ F, g = fun z => f1 z - f2 z}

/-- `n` i.i.d. standard Gaussian variates `w : Fin n → Ω → ℝ` on a probability space `(Ω, P)`
— the noise variables `{wᵢ}` of the local Gaussian complexity (Eq. (13.16), p. 421). -/
def IsIIDStdGaussian {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (w : Fin n → Ω → ℝ) : Prop :=
  (∀ i, Measurable (w i)) ∧ iIndepFun w P ∧ ∀ i, Measure.map (w i) P = gaussianReal 0 1

/-- The local Gaussian complexity `Gₙ(δ; H)` of a function class `H` at radius `δ`
(Eq. (13.16), p. 421): the expectation, over the noise `w`, of the supremum over the
radius-`δ` slice `{h ∈ H | ‖h‖ₙ ≤ δ}` of the absolute empirical Gaussian process
`|(1/n) Σᵢ wᵢ h(xᵢ)|`. The supremum is taken over the subtype of this slice, which is always
nonempty when `0 ∈ H` (in particular whenever `H` is star-shaped and nonempty, since taking
`α = 0` on any `h ∈ H` shows `0 ∈ H`). -/
noncomputable def localGaussianComplexity {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) (H : Set (X → ℝ)) (δ : ℝ) : ℝ :=
  ∫ ω, ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ},
      |(∑ i, w i ω * h.1 (x i)) / n| ∂P

/-- `δ` satisfies the critical inequality (13.17)/(13.42a): `Gₙ(δ; H)/δ ≤ δ/(2σ)`, `δ > 0`.
A `δ` satisfying this is called *valid* in the book (p. 422). The explicit `Integrable`
hypothesis on the defining supremum (trap 2) guards against `localGaussianComplexity`'s
Bochner integral silently collapsing to Mathlib's junk value `0` on a non-measurable or
non-integrable integrand — a genuine risk since `X` and `H` carry no topology, separability or
countability constraint elsewhere in this file — which would otherwise make this predicate
(and every theorem that assumes it) trivially/vacuously satisfiable for every `δ > 0`. -/
def SatisfiesCriticalInequality {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) (H : Set (X → ℝ)) (σ δ : ℝ) : Prop :=
  0 < δ ∧
    MeasureTheory.Integrable
      (fun ω => ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ},
          |(∑ i, w i ω * h.1 (x i)) / n|) P ∧
    localGaussianComplexity x w P H δ / δ ≤ δ / (2 * σ)

/-- `fHat` is a nonparametric least-squares estimate over `F` for the observed data `y`
(Eq. (13.7)): `fHat ∈ F` and it minimizes the empirical sum of squared residuals over `F`. -/
def IsLeastSquaresEstimate {X : Type*} {n : ℕ} (x : Fin n → X) (F : Set (X → ℝ))
    (y : Fin n → ℝ) (fHat : X → ℝ) : Prop :=
  fHat ∈ F ∧ ∀ f ∈ F, ∑ i, (y i - fHat (x i)) ^ 2 ≤ ∑ i, (y i - f (x i)) ^ 2

end HighDimStat.NonparametricLS


