-- Prove2me | Definitions.Def_SemiBanditSOO_ConfidenceSet
-- name    : SemiBanditSOO_ConfidenceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:45.263354+00:00
-- url     : https://prove2.me/theorems/ca9949e0-eaec-476f-98f7-fe5f8d7ae4d1
-- title:
--   The parameter $\Lambda$, the radius $b_m$ and the confidence sets $\mathcal C_m(\widehat D_{i,m})$
-- statement:
--   Let $n$ be the number of coordinates, $T$ the number of rounds and $\delta\in(0,1)$. The confidence parameter is
--   $$\Lambda=\log\bigl(80n(T+1)^3/\delta\bigr).$$
--   For $m\ge1$ and $z\in[0,1]$, the radius is
--   $$b_m(z)=\min\Bigl\{1,\ 6\sqrt{z(1-z)\Lambda/m}+32\Lambda/m\Bigr\}. \qquad (3.1)$$
--   For a sample $Z_{1},\dots,Z_{m}$ of a coordinate with domain $\mathrm{dom}\subseteq[0,1]$, the empirical distribution is $\widehat D_m(B)=\frac1m\sum_{j=1}^m\mathbf 1\{Z_j\in B\}$, and the confidence set is
--   $$\mathcal C_m(\widehat D_m)=\Bigl\{Q:\ |Q(I)-\widehat D_m(I)|\le b_m(\widehat D_m(I))\ \ \forall I\in\mathcal I_1\Bigr\}, \qquad (3.2)$$
--   where $Q$ ranges over distributions on the domain; for $m=0$, $\mathcal C_0$ is the set of all distributions on the domain.
--
--   These are the confidence sets that Algorithm 1 forms at the beginning of each round from the values revealed so far.
--
--   **Formalization Note.** A sample is a list of points of the domain, and $m$ is its length; $Q(I)$ is the mass of $\mathrm{dom}\cap I$. $\Lambda$ is a parameter of the confidence set; Algorithm 1 uses $\Lambda=\log(80n(T+1)^3/\delta)$.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, §3.1, pp.9–10, Λ, (3.1), (3.2)

import Mathlib
import Definitions.Def_SemiBanditSOO_LevelSet

open MeasureTheory

namespace SemiBanditSOO

/-- **The confidence parameter** `Λ = log(80 n (T + 1)³ / δ)` (§3.1, p.9). Harada, Kawase, Sumita,
*Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*,
arXiv:2611.02739v1, §3.1, p.9. Here `n` is the number of coordinates, `T` the number of rounds and
`δ ∈ (0, 1)` the input of Algorithm 1; `log` is the natural logarithm. -/
noncomputable def Lam (n T : ℕ) (δ : ℝ) : ℝ :=
  Real.log (80 * (n : ℝ) * ((T : ℝ) + 1) ^ 3 / δ)

/-- **The radius** (3.1), p.9: for `m ≥ 1` and `z ∈ [0, 1]`,
`b_m(z) = min{1, 6 √(z(1 − z)Λ/m) + 32Λ/m}`. It is only used with `m ≥ 1`. -/
noncomputable def bm (Λ : ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  min 1 (6 * Real.sqrt (z * (1 - z) * Λ / m) + 32 * Λ / m)

/-- **The empirical distribution of a sample, evaluated on a set** (§3.1, p.9):
`D̂_m(B) = (1/m) Σ_{j=1}^m 1{Z_j ∈ B}` for the sample `L = (Z_1, …, Z_m)` of values of a coordinate
with domain `dom`. -/
noncomputable def empFreq {dom : Set ℝ} (L : List dom) (B : Set ℝ) : ℝ :=
  (L.map fun z : dom => B.indicator (fun _ => (1 : ℝ)) (z : ℝ)).sum / L.length

/-- `Q(B)` for a distribution `Q` on the domain `dom ⊆ [0, 1]` and a set `B ⊆ ℝ`: the mass of
`dom ∩ B`. -/
noncomputable def probOf {dom : Set ℝ} (Q : ProbabilityMeasure dom) (B : Set ℝ) : ℝ :=
  (Q : Measure dom).real (Subtype.val ⁻¹' B)

/-- **The confidence set** (3.2), pp.9–10. For `m ≥ 1` observations `L = (Z_1, …, Z_m)` of a
coordinate with domain `dom`,
`𝒞_m(D̂_m) = {Q : |Q(I) − D̂_m(I)| ≤ b_m(D̂_m(I)) for all I ∈ ℐ₁}`, where `Q` ranges over
distributions on the domain; for `m = 0`, `𝒞_0` is the set of all distributions on the domain.

**Formalization Note.** Distributions on the domain are `ProbabilityMeasure dom` (the subtype with
its subspace σ-algebra); `Λ` is a parameter (Algorithm 1 uses `Lam n T δ`); `m` is the length of
the sample list. -/
noncomputable def confSet {dom : Set ℝ} (Λ : ℝ) (L : List dom) : Set (ProbabilityMeasure dom) :=
  if L.length = 0 then Set.univ
  else {Q | ∀ I ∈ IntervalUnions 1, |probOf Q I - empFreq L I| ≤ bm Λ L.length (empFreq L I)}

end SemiBanditSOO


