-- Prove2me | Definitions.Def_NoStretch1PRS_sphereMeasure
-- name    : NoStretch1PRS_sphereMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:28.156625+00:00
-- url     : https://prove2.me/theorems/828b12b5-22ae-49a7-9fb7-167053d5972a
-- title:
--   Real and complex Haar measures on unit spheres
-- statement:
--   For a finite index set $\iota$, let $S_\iota=\{v\in\mathbb R^\iota:\|v\|_2=1\}$ be the unit sphere. The **real Haar measure** $\mu^{\mathbb R}_\iota$ is the uniform (rotation-invariant) probability measure on $S_\iota$; it is the law of a Haar-random real pure state.
--
--   The **complex Haar measure** $\mu_\iota$ on pure states of $\mathbb C^\iota$ is the uniform probability measure on the unit sphere of $\mathbb C^\iota$, obtained from $\mu^{\mathbb R}_{\iota\times\{0,1\}}$ through the isometry $\mathbb R^{\iota\times\{0,1\}}\cong\mathbb C^\iota$, $v\mapsto (v_{i,0}+\mathrm i\,v_{i,1})_i$.
--
--   The module also provides the entrywise expectation $\mathbb E_{x\sim\mu}[F(x)]$ of a matrix-valued function.
--
--   These measures are the challenge law of single-copy pseudorandom-state security ($\mu_{2^m}$), the law of the CHRS states ($\mu^{\mathbb R}_{2^i}$), and the randomness in Theorem 5.1, Lemma 5.4 and Lévy's lemma.
--
--   **Formalization Note** $\mu^{\mathbb R}_\iota$ is Mathlib's cone measure `Measure.toSphere` of Lebesgue measure, divided by its total mass; it is proved to be a probability measure for nonempty $\iota$. The complex Haar measure is a measure on vectors $\iota\to\mathbb C$ supported on the unit sphere; phase-invariant functions (acceptance probabilities) have the same integral as under the Haar measure on rays.
-- source:
--   Chen, Coladangelo, Lin, Skoumios, Tysdal, Wang, No linear stretching of single-copy quantum pseudorandomness, arXiv:2606.24736 (held version, sha256 2670cb2f…), §3, p.15 (µ_d and µ^R_d); Definition 3.1, p.15; §4, p.21

import Mathlib

set_option autoImplicit false

namespace NoStretch1PRS

open MeasureTheory

/-- The unit sphere of the real Euclidean space `ℝ^ι` (`ι` a finite index set of coordinates).
B. Chen, A. Coladangelo, Y.-T. Lin, N. Skoumios, J. Tysdal, Y. Wang, *No linear stretching of
single-copy quantum pseudorandomness*, arXiv:2606.24736 (held version, sha256 2670cb2f…), §3,
p.15: "the real Haar measure on the set of real states on `ℝ^d ⊂ ℂ^d`". -/
abbrev Sph (ι : Type) [Fintype ι] : Type := Metric.sphere (0 : EuclideanSpace ℝ ι) 1

/-- **The real Haar measure** `µ^R_d` on unit vectors of `ℝ^ι` (arXiv:2606.24736, held version,
§3, p.15; §4, p.21; Theorem 5.1, p.30): the uniform (rotation-invariant) probability measure on the
unit sphere.

**Formalization Note.** It is Mathlib's cone measure `Measure.toSphere` of Lebesgue measure on
`EuclideanSpace ℝ ι`, normalized by its total mass. For nonempty `ι` that mass is finite and
positive (instance below), so this is a probability measure; the uniform measure on a sphere is
the unique rotation-invariant probability measure there, which is the real Haar measure on real
pure states. -/
noncomputable def sphereMeasure (ι : Type) [Fintype ι] : Measure (Sph ι) :=
  ((volume : Measure (EuclideanSpace ℝ ι)).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ ι)).toSphere

instance sphereMeasure.instIsProbabilityMeasure (ι : Type) [Fintype ι] [Nonempty ι] :
    IsProbabilityMeasure (sphereMeasure ι) := by
  constructor
  unfold sphereMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (volume : Measure (EuclideanSpace ℝ ι)).toSphere Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
  exact ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)

/-- A real vector of `ℝ^ι` viewed as a complex vector of `ℂ^ι ⊃ ℝ^ι`. -/
noncomputable def toC {ι : Type} [Fintype ι] (v : EuclideanSpace ℝ ι) : ι → ℂ :=
  fun i => ((v i : ℝ) : ℂ)

/-- The identification `ℝ^{ι × {0,1}} ≅ ℂ^ι`: coordinate `(i, false)` is the real part and
`(i, true)` the imaginary part of the `i`-th complex coordinate. It is a linear isometry, so it
maps the unit sphere of `ℝ^{2|ι|}` onto the unit sphere of `ℂ^ι`. -/
noncomputable def realToComplex {ι : Type} [Fintype ι] (v : EuclideanSpace ℝ (ι × Bool)) :
    ι → ℂ :=
  fun i => ((v (i, false) : ℝ) : ℂ) + ((v (i, true) : ℝ) : ℂ) * Complex.I

/-- **The (complex) Haar measure** `µ_d` on pure states of `ℂ^ι` (arXiv:2606.24736, held version,
§3, p.15; Definition 3.1, p.15; Proposition 4.6, p.27): the uniform probability measure on the unit
sphere of `ℂ^ι`, as a measure on vectors `ι → ℂ`.

**Formalization Note.** The unit sphere of `ℂ^ι` is the unit sphere `S^{2|ι|−1}` of
`ℝ^{ι × {0,1}}` under `realToComplex` (real and imaginary parts), and the uniform measure on it is
the image of `sphereMeasure (ι × Bool)`. The map is continuous, hence measurable, so the image is
again a probability measure. A function of a pure state that is invariant under global phases (such
as an acceptance probability) has the same integral against this measure as against the Haar
measure on rays. -/
noncomputable def complexHaar (ι : Type) [Fintype ι] : Measure (ι → ℂ) :=
  (sphereMeasure (ι × Bool)).map fun v : Sph (ι × Bool) => realToComplex v.1

/-- Entrywise expectation `E_{x∼μ}[F(x)]` of a matrix-valued function. -/
noncomputable def avgMat {α : Type} [MeasurableSpace α] (μ : Measure α) {m n : Type}
    (F : α → Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => ∫ x, F x i j ∂μ

end NoStretch1PRS


