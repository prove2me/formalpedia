-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosProfileComplex_F000
-- name    : LevyStochCalc_Driver_JointChaosProfileComplex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:28:15.440177+00:00
-- url     : https://prove2.me/theorems/faa70ecc-29d6-41a2-a99d-997f5e4e1d69
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosProfileComplex
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosProfileComplex. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Driver_JointChaosProfile_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F000
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Complex joint chaos elements of a step at a mark profile, across mark families

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise
disjoint family `A` of mark sets of finite intensity and a complex profile `c` constant on each of
them, the complex bidegree-`(r, s)` element of the step is `X_(r, s)(c; A) = H_r(ΔWʲ; τ) D_s(c)`,
the product of the degree-`r` Wiener chaos element of the increment and the degree-`s` element of
the profile over the strips `(a, b] ×ˢ A k`. The Brownian and the Poisson factors are independent,
so the bilinear moment of two such elements over different families `A`, `A'` factors into the
Hermite and the Charlier Gram across the families,

  `E[X_(r, s)(c; A) X_(r', s')(c'; A')] = δ_(r r') r! τ ^ r δ_(s s') s! (τ ⟨c, c'⟩) ^ s`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`; distinct bidegrees, and a fortiori distinct total
degrees, are orthogonal whatever the two families. Every element of the step is measurable for
the σ-algebra of the step over the strips of both families, which is independent of the joint
filtration at `a`, and also of the augmentation of its join with an initial σ-algebra independent
of the whole filtration. So against a coefficient measurable for such a node σ-algebra the pairing
of two elements is the mean of the coefficient times their pairing, and the conditional pairing
given the node σ-algebra is the constant pairing.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC` — the complex bidegree-`(r, s)` element.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_conj_cross` — the bidegree
  Gram across two mark families.
* `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_filtration`,
  `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_aug_sup` — the σ-algebra of the step is
  independent of the joint filtration at the node, and of the augmentation of its join with an
  independent initial σ-algebra.
* `LevyStochCalc.Driver.LevyDriver.integral_mul_eq_mul_integral_of_indep_stepSigma` — the pairing
  of a variable of the step against a coefficient measurable at the node.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStepProfileC_mul_conj` — the
  same for the Hermitian pairing of two elements over different families.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfileC_mul_conj` — the conditional
  Hermitian pairing at the node is the constant Gram.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Elements

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Measurability -/

/-- A complex degree element of a profile on a finite family of measurable regions is measurable
for the Poisson σ-algebra of the driver. -/
theorem measurable_markedChaosDegreeC_sigmaPoisson (D : LevyDriver.{u, v, w} P d ν) {p : ℕ}
    (s : ℕ) {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℂ) :
    Measurable[sigmaPoisson D.N] (markedChaosDegreeC D.N s B c) :=
  Finset.measurable_sum _ fun α _ => (Complex.measurable_ofReal.comp
    (Finset.univ.measurable_prod fun k _ =>
      (((continuous_charlierScaled (α k) _).measurable).comp ENNReal.measurable_toReal).comp
        (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N (hB k))))).const_mul _
/-- A complex degree element of a profile on a family of regions, each of which is a member of the
family `C`, is measurable for the σ-algebra of the step over `C`. -/
theorem measurable_markedChaosDegreeC_stepSigma (D : LevyDriver.{u, v, w} P d ν) {m p : ℕ}
    (C : Fin m → Set (ℝ × E)) (s t : ℝ) (r : ℕ) {B : Fin p → Set (ℝ × E)}
    (hBC : ∀ k, ∃ i, C i = B k) (c : Fin p → ℂ) :
    Measurable[D.stepSigma C s t] (markedChaosDegreeC D.N r B c) := by
  have hcount : ∀ k, Measurable[D.stepSigma C s t] (fun ω => D.N.N ω (B k)) := by
    intro k
    obtain ⟨i, hi⟩ := hBC k
    rw [← hi]
    exact Measurable.of_comap_le
      (le_sup_of_le_right (le_iSup (fun i => D.regionSigma (C i)) i))
  exact Finset.measurable_sum _ fun α _ => (Complex.measurable_ofReal.comp
    (Finset.univ.measurable_prod fun k _ =>
      (((continuous_charlierScaled (α k) _).measurable).comp ENNReal.measurable_toReal).comp
        (hcount k))).const_mul _
/-! ### The complex bidegree element -/

/-- The complex joint chaos element of bidegree `(r, s)` of the step `(a, b]` of the driver at a
complex profile `c` on a finite family `A` of mark sets: the degree-`r` Wiener chaos element of the
increment of the coordinate `j` times the degree-`s` element of the profile over the strips
`(a, b] ×ˢ A k`. -/
noncomputable def jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (r s : ℕ) (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  (wienerChaosStep r (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℂ)
    * markedChaosDegreeC D.N s (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
/-- At a real profile the complex element is the real one. -/
theorem jointChaosStepProfileC_ofReal (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (r s : ℕ)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℝ) (ω : Ω) :
    D.jointChaosStepProfileC j r s a b A (fun k => (c k : ℂ)) ω
      = (D.jointChaosStepProfile j r s a b A c ω : ℂ) := by
  rw [jointChaosStepProfileC, markedChaosDegreeC_ofReal, jointChaosStepProfile,
    Complex.ofReal_mul]
/-- Conjugating the profile conjugates the element. -/
theorem conj_jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (r s : ℕ)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℂ) (ω : Ω) :
    (starRingEnd ℂ) (D.jointChaosStepProfileC j r s a b A c ω)
      = D.jointChaosStepProfileC j r s a b A (fun k => (starRingEnd ℂ) (c k)) ω := by
  rw [jointChaosStepProfileC, jointChaosStepProfileC, map_mul, Complex.conj_ofReal,
    conj_markedChaosDegreeC]
/-- A complex joint chaos element of a step at a profile on a family of measurable mark sets is
measurable. -/
theorem measurable_jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (r s : ℕ) (a b : ℝ≥0) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (c : Fin p → ℂ) :
    Measurable (D.jointChaosStepProfileC j r s a b A c) :=
  (Complex.measurable_ofReal.comp ((measurable_wienerChaosStep r _).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _)))).mul
    (measurable_markedChaosDegreeC D.N s (fun k => measurableSet_Ioc.prod (hA k)) c)
/-- A complex joint chaos element of a step at a profile on a family of mark sets whose strips are
members of the family `C` is measurable for the σ-algebra of the step over `C`. -/
theorem measurable_jointChaosStepProfileC_stepSigma (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (r s : ℕ) (a b : ℝ≥0) {m p : ℕ} (C : Fin m → Set (ℝ × E)) {A : Fin p → Set E}
    (hAC : ∀ k, ∃ i, C i = Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) (c : Fin p → ℂ) :
    Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (D.jointChaosStepProfileC j r s a b A c) := by
  have hincr : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      (le_sup_of_le_left (le_iSup (fun i => D.incrementSigma i (a : ℝ) (b : ℝ)) j))
  exact (Complex.measurable_ofReal.comp ((measurable_wienerChaosStep r _).comp hincr)).mul
    (D.measurable_markedChaosDegreeC_stepSigma C _ _ s hAC c)
end Elements

/-! ### The pairing at the node preceding the step -/

section Node

variable {Ω : Type u} {M 𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

end Node

end LevyStochCalc.Driver.LevyDriver


