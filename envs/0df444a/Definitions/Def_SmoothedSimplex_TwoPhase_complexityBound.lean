-- Prove2me | Definitions.Def_SmoothedSimplex_TwoPhase_complexityBound
-- name    : SmoothedSimplex_TwoPhase_complexityBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:53:30.465235+00:00
-- url     : https://prove2.me/theorems/ad6035f9-cd88-4841-acba-58a42fd6962a
-- title:
--   Section 5 — two-phase shadow-size cost
-- statement:
--   For input $(A,y,z)$, the algorithm samples $d$-subsets, selects one maximizing the smallest singular value, and sets the power-of-two scales $\kappa$ and $M$. The relaxed right-hand sides are $y'_i=M$ on the selected set and $y'_i=\sqrt d\,M^2/(4\kappa)$ elsewhere. The first-phase count $S'_z$ is the cardinality of the shadow of LP′ in the plane spanned by $A_I\alpha$ and $z$.
--
--   The second phase lifts each original constraint to $a_i^+=((y'_i-y_i)/2,a_i)$ with $y_i^+=(y'_i+y_i)/2$. Its count $S_z^+$ is the shadow cardinality in the plane spanned by $(0,z)$ and $(1,0,\ldots,0)$ when $\sqrt d M/(4\kappa)\ge1$, and zero otherwise. The shadow-size cost is
--   $$C(A,y,z)=\mathbb E_{\mathcal I,\alpha}[S'_z(A,y,\mathcal I,\alpha)+S_z^+(A,y,\mathcal I)+2].$$
--   By Lemma 3.3.5 and the display on page 58, this is the paper's upper bound on expected polar pivot count. The first and second counts are finite because their shadows consist of at most $\binom nd$ and $\binom n{d+1}$ subsets.
--
--   **Formalization Note** $\mathcal I$ is a list of independent uniform draws with replacement; ties in the maximizing sample go to the first draw. Gaussian-null zero denominators are assigned Lean's total-operation values. The theorem asks for integrability of the cost, so nonmeasurable default integrals cannot establish its bound.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, LP′ and LP⁺, printed pp. 33–35, PDF pp. 33–35; cost and inequality, printed p. 58, PDF p. 58; T′, printed p. 68, PDF p. 68; T⁺, printed p. 80, PDF p. 80

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_shadow
import Definitions.Def_SmoothedSimplex_TwoPhase_gaussianInput

namespace SmoothedSimplex.TwoPhase

/-- The smallest singular value of the matrix with columns indexed by `I`, in the
variational form of Proposition 2.2.6(a), printed p. 15, PDF p. 15. For an empty
index set Lean's `sInf` is zero, matching the singular value convention used here. -/
noncomputable def sMin {n d : ℕ} (a : Fin n → Point d) (I : Finset (Fin n)) : ℝ :=
  sInf {r : ℝ | ∃ u : EuclideanSpace ℝ I, ‖u‖ = 1 ∧
    r = ‖∑ i : I, (u i) • a i.1‖}

/-- A deterministic tie rule for `𝓘(A) = argmax_{I∈𝓘} s_min(A_I)`:
retain the first sampled set at equal singular values. Spielman–Teng,
printed pp. 35, 60, PDF pp. 35, 60. -/
noncomputable def bestSample {n d : ℕ} (a : Fin n → Point d)
    (draw : Fin (sampleCount n d) → DSet n d) : Finset (Fin n) :=
  (List.ofFn draw).foldl (fun best J =>
    if best.card = d ∧ sMin a J.1 ≤ sMin a best then best else J.1) ∅

/-- `max_i ‖(y_i,a_i)‖₂`; the pair norm is Euclidean, not the default max norm
on a product. Spielman–Teng, algorithm step (2), printed p. 35, PDF p. 35.
At `n=0`, `sSup ∅=0`; all theorems use `n>d≥3`. -/
noncomputable def maxDataNorm {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin n => Real.sqrt ((y i)^2 + ‖a i‖^2)))

/-- The power-of-two scale `M` of step (2), printed p. 35, PDF p. 35.
At all-zero data, `Real.logb 2 0=0`, so `M=4`. -/
noncomputable def scaleM {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ) : ℝ :=
  (2 : ℝ) ^ (Int.ceil (Real.logb 2 (maxDataNorm a y)) + 2)

/-- The power-of-two condition scale `κ`, step (2), printed p. 35, PDF p. 35.
At `sMin=0`, `Real.logb 2 0=0`, so `κ=1`. -/
noncomputable def scaleK {n d : ℕ} (a : Fin n → Point d) (I : Finset (Fin n)) : ℝ :=
  (2 : ℝ) ^ (Int.floor (Real.logb 2 (sMin a I)))

/-- The relaxed right-hand side `y'` of LP′, printed p. 33, PDF p. 33. -/
noncomputable def relaxedRhs {n d : ℕ} (I : Finset (Fin n)) (κ M : ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then M else Real.sqrt d * M ^ 2 / (4 * κ)

/-- The first-phase shadow `T'_z(A,I,α,κ,M)`, printed p. 68, PDF p. 68.
The coefficients `α` are indexed by the selected `d`-set. -/
noncomputable def firstPhaseShadow {n d : ℕ} (a : Fin n → Point d)
    (I : Finset (Fin n)) (α : Fin n → ℝ) (κ M : ℝ) (z : Point d) : ℕ :=
  (shadow a (relaxedRhs (d := d) I κ M) (∑ i ∈ I, (α i) • a i) z).card

/-- The lifted LP⁺ constraint vector `a⁺ᵢ=((y'ᵢ−yᵢ)/2,aᵢ)` in Euclidean
`ℝ^{d+1}`, printed p. 34, PDF p. 34. -/
noncomputable def liftedVector {n d : ℕ} (a : Fin n → Point d) (y y' : Fin n → ℝ)
    (i : Fin n) : Point (d + 1) :=
  WithLp.toLp 2 (Fin.cons ((y' i - y i) / 2) (fun j => a i j))

/-- The lifted LP⁺ right-hand side `y⁺ᵢ=(y'ᵢ+yᵢ)/2`, printed p. 34,
PDF p. 34. -/
noncomputable def liftedRhs {n : ℕ} (y y' : Fin n → ℝ) (i : Fin n) : ℝ :=
  (y' i + y i) / 2

/-- The objective `(0,z)` in the lifted space, printed p. 80, PDF p. 80. -/
noncomputable def liftedOldObjective {d : ℕ} (z : Point d) : Point (d + 1) :=
  WithLp.toLp 2 (Fin.cons 0 (fun j => z j))

/-- The objective `z⁺=(1,0,...,0)` in the lifted space, printed p. 34,
PDF p. 34. -/
noncomputable def liftedNewObjective (d : ℕ) : Point (d + 1) :=
  WithLp.toLp 2 (Fin.cons 1 (fun _ : Fin d => 0))

/-- The second-phase shadow `T⁺_z(A,y,κ,M)`, printed p. 80, PDF p. 80.
The formula uses only the `n` lifted original constraints; the two artificial
constraints contribute the separate `+2` in the step bound. Division by `y⁺=0`
is total in Lean and occurs only on a Gaussian-null event in the stated bounds. -/
noncomputable def secondPhaseShadow {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ)
    (I : Finset (Fin n)) (κ M : ℝ) (z : Point d) : ℕ :=
  if 1 ≤ Real.sqrt d * M / (4 * κ) then
    let y' := relaxedRhs (d := d) I κ M
    let b : Fin n → Point (d + 1) := fun i =>
      (liftedRhs y y' i)⁻¹ • liftedVector a y y' i
    (shadow b (fun _ => 1) (liftedOldObjective z) (liftedNewObjective d)).card
  else 0

/-- The sampled coefficients of step (4), using independent rate-one exponential
weights. Conditional on the selected `I`, these have the uniform law on
`A_{1/d²}`. Spielman–Teng, printed pp. 35, 68, PDF pp. 35, 68. -/
noncomputable def sampledCoefficients {n d : ℕ} (I : Finset (Fin n))
    (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 1 / (d : ℝ)^2 + (1 - 1 / (d : ℝ)) * w i / (∑ j ∈ I, w j)

/-- The algorithm's independent random draws of `d`-subsets and exponential
weights. Spielman–Teng, step (1), step (4), printed p. 35, PDF p. 35. -/
noncomputable def algorithmLaw (n d : ℕ) : MeasureTheory.Measure
    ((Fin (sampleCount n d) → DSet n d) × (Fin n → ℝ)) :=
  (sampleLaw n d).prod (MeasureTheory.Measure.pi
    (fun _ : Fin n => ProbabilityTheory.expMeasure 1))

/-- `S'_z(A,y,𝓘,α)` of printed p. 68, PDF p. 68, with `I=𝓘(A)` and the
power-of-two choices of `κ,M` from algorithm step (2). -/
noncomputable def firstPhaseSteps {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ)
    (z : Point d) (draw : Fin (sampleCount n d) → DSet n d)
    (w : Fin n → ℝ) : ℕ :=
  let I := bestSample a draw
  firstPhaseShadow a I (sampledCoefficients (d := d) I w) (scaleK a I) (scaleM a y) z

/-- `S⁺_z(A,y,𝓘)` of printed p. 80, PDF p. 80, with `I=𝓘(A)` and the
power-of-two choices of `κ,M`. -/
noncomputable def secondPhaseSteps {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ)
    (z : Point d) (draw : Fin (sampleCount n d) → DSet n d) : ℕ :=
  let I := bestSample a draw
  secondPhaseShadow a y I (scaleK a I) (scaleM a y) z

/-- The §5 shadow-size upper bound for expected pivot count,
`E[S′]+E[S⁺]+2`, printed p. 58, PDF p. 58. Lemma 3.3.5
bounds the actual pivot count by this quantity. The two internal Bochner
integrals must be shown integrable when this definition is used in a theorem. -/
noncomputable def complexityBound {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ)
    (z : Point d) : ℝ :=
  ∫ p, ((firstPhaseSteps a y z p.1 p.2 : ℝ) +
    (secondPhaseSteps a y z p.1 : ℝ) + 2) ∂(algorithmLaw n d)

end SmoothedSimplex.TwoPhase


