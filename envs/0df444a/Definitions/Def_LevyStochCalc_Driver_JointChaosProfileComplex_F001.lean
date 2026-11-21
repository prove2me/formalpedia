-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosProfileComplex_F001
-- name    : LevyStochCalc_Driver_JointChaosProfileComplex_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:02:13.531904+00:00
-- url     : https://prove2.me/theorems/aaddc4b6-0749-47d9-a29d-b4db890f52f2
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosProfileComplex
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosProfileComplex. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileComplex_F000
import Definitions.Def_SourceProof_4d042d322bf3234fc77542c9

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

/-! ### The complex bidegree element -/

/-- **The Hermitian bidegree Gram across two mark families.**
`E[X_(r, s)(c; A) conj X_(r', s')(c'; A')]
  = δ_(r r') r! τ ^ r δ_(s s') s! (τ ∑_(k, l) c_k conj c'_l ν(A k ∩ A' l)) ^ s`. -/
theorem integral_jointChaosStepProfileC_mul_conj_cross (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω) ∂P
      = (((if r = r' then (r.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ r else 0 : ℝ)) : ℂ)
        * (if s = s' then (s.factorial : ℂ) * ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
            * ∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s
          else 0) := by
  simp_rw [conj_jointChaosStepProfileC]
  exact (_root_.Prove2MeSourceProof.h_4d042d322bf3234fc77542c9 D) j hab hA hAν hd hA' hAν' hd' r s r' s' c _
end Elements

/-! ### The pairing at the node preceding the step -/

section Node

variable {Ω : Type u} {M 𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- The σ-algebra of the step over `(a, b]` and a finite family of measurable regions inside
`(a, b] ×ˢ E` is independent of the joint filtration at `a`. -/
theorem indep_stepSigma_filtration (D : LevyDriver.{u, v, w} P d ν) {m : ℕ}
    (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hCs : ∀ k, C k ⊆ Set.Ioc a b ×ˢ Set.univ) :
    Indep (D.stepSigma C a b) (D.filtration a) P :=
  (_root_.Prove2MeSourceProof.h_b5912c738affc5f69d2adbcb D) C hCm ha hab fun k =>
    (hCs k).trans (Set.prod_mono Set.Ioc_subset_Ioi_self le_rfl)
/-- The σ-algebra of the step over `(a, b]` and a finite family of measurable regions inside
`(a, b] ×ˢ E` is independent of the augmentation of `𝒢₀ ⊔ ℱ_a`, for an initial σ-algebra `𝒢₀`
independent of the whole joint filtration. -/
theorem indep_stepSigma_aug_sup (D : LevyDriver.{u, v, w} P d ν) {m : ℕ}
    (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hCs : ∀ k, C k ⊆ Set.Ioc a b ×ˢ Set.univ) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) :
    Indep (D.stepSigma C a b) (aug (𝒢₀ ⊔ D.filtration a) mΩ P) P := by
  have hS := D.indep_stepSigma_filtration C hCm ha hab hCs
  have hSle : D.stepSigma C a b ≤ D.filtration b := D.stepSigma_le_filtration C hCm hab.le
    fun k => (hCs k).trans (Set.prod_mono Set.Ioc_subset_Iic_self le_rfl)
  have h2 : Indep 𝒢₀ (D.filtration a ⊔ D.stepSigma C a b) P :=
    indep_of_indep_of_le_right hind₀ (sup_le (le_iSup (fun t => D.filtration t) a)
      (hSle.trans (le_iSup (fun t => D.filtration t) b)))
  have h := _root_.Prove2MeSourceProof.h_fa5eb32f3be3b75875b08ef5 (D.filtration.le a) h𝒢₀ (D.stepSigma_le C hCm a b)
    hS.symm h2
  rw [sup_comm] at h
  exact (indep_aug P h).symm
/-- Against a complex coefficient measurable for a σ-algebra `M` independent of the σ-algebra of
the step over `(s, t]` and a finite family of regions, the mean of the product with a complex
variable measurable for the latter factors. -/
theorem integral_mul_eq_mul_integral_of_indep_stepSigma (D : LevyDriver.{u, v, w} P d ν)
    {m : ℕ} (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k)) (s t : ℝ)
    (hM : M ≤ mΩ) (hind : Indep (D.stepSigma C s t) M P)
    {Q Y : Ω → ℂ} (hQ : StronglyMeasurable[M] Q) (hY : Measurable[D.stepSigma C s t] Y) :
    ∫ ω, Q ω * Y ω ∂P = (∫ ω, Q ω ∂P) * ∫ ω, Y ω ∂P := by
  have hQY : IndepFun Q Y P :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hind.symm hQ.measurable.comap_le) hY.comap_le)
  exact hQY.integral_fun_mul_eq_mul_integral (hQ.mono hM).aestronglyMeasurable
    (hY.mono (D.stepSigma_le C hCm s t) le_rfl).aestronglyMeasurable
/-- The strips over `(a, b]` of two families of measurable mark sets, listed as one family, are
measurable. -/
theorem measurableSet_append_strip {p q : ℕ} (a b : ℝ≥0) {A : Fin p → Set E}
    {A' : Fin q → Set E} (hA : ∀ k, MeasurableSet (A k)) (hA' : ∀ l, MeasurableSet (A' l))
    (i : Fin (p + q)) :
    MeasurableSet (Fin.append (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) i) := by
  refine Fin.addCases (fun k => ?_) (fun l => ?_) i
  · rw [Fin.append_left]; exact measurableSet_Ioc.prod (hA k)
  · rw [Fin.append_right]; exact measurableSet_Ioc.prod (hA' l)
omit [MeasurableSpace E] in
/-- The strips over `(a, b]` of two families of mark sets, listed as one family, lie inside
`(a, b] ×ˢ E`. -/
theorem append_strip_subset {p q : ℕ} (a b : ℝ≥0) (A : Fin p → Set E) (A' : Fin q → Set E)
    (i : Fin (p + q)) :
    Fin.append (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) i ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ := by
  refine Fin.addCases (fun k => ?_) (fun l => ?_) i
  · rw [Fin.append_left]; exact Set.prod_mono le_rfl (Set.subset_univ _)
  · rw [Fin.append_right]; exact Set.prod_mono le_rfl (Set.subset_univ _)
/-- The Hermitian pairing of two complex joint chaos elements of the step `(a, b]` over two
families of mark sets is measurable for the σ-algebra of the step over the strips of both
families. -/
theorem measurable_jointChaosStepProfileC_mul_conj_stepSigma (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) (a b : ℝ≥0) {p q : ℕ} (A : Fin p → Set E) (A' : Fin q → Set E)
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    Measurable[D.stepSigma (Fin.append (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
        (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l)) (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω)) := by
  simp_rw [conj_jointChaosStepProfileC]
  exact (D.measurable_jointChaosStepProfileC_stepSigma j r s a b _
      (fun k => ⟨Fin.castAdd q k, Fin.append_left _ _ k⟩) c).mul
    (D.measurable_jointChaosStepProfileC_stepSigma j r' s' a b _
      (fun l => ⟨Fin.natAdd p l, Fin.append_right _ _ l⟩) _)
/-- **The pairing at the node across two mark families.** Against a complex coefficient `Q`
measurable for a σ-algebra `M` independent of the σ-algebra of the step over `(a, b]` and every
finite family of measurable regions inside `(a, b] ×ˢ E` (such as the joint filtration at `a`),
the Hermitian pairing of two complex joint chaos elements of the step over two families of mark
sets is the mean of `Q` times their pairing. -/
theorem integral_coeff_mul_jointChaosStepProfileC_mul_conj (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hA' : ∀ l, MeasurableSet (A' l)) (hM : M ≤ mΩ)
    (hind : ∀ {m : ℕ} (C : Fin m → Set (ℝ × E)), (∀ k, MeasurableSet (C k)) →
      (∀ k, C k ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ) →
        Indep (D.stepSigma C (a : ℝ) (b : ℝ)) M P)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[M] Q) (r s r' s' : ℕ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) :
    ∫ ω, Q ω * (D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω)) ∂P
      = (∫ ω, Q ω ∂P) * ∫ ω, D.jointChaosStepProfileC j r s a b A c ω
          * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω) ∂P :=
  D.integral_mul_eq_mul_integral_of_indep_stepSigma _ (measurableSet_append_strip a b hA hA')
    _ _ hM (hind _ (measurableSet_append_strip a b hA hA') (append_strip_subset a b A A')) hQ
    (D.measurable_jointChaosStepProfileC_mul_conj_stepSigma j a b A A' r s r' s' c c')
/-- **The conditional pairing at the node across two mark families.** Given a σ-algebra `M`
independent of the σ-algebra of the step over `(a, b]` and every finite family of measurable
regions inside `(a, b] ×ˢ E` (such as the joint filtration at `a`), the conditional expectation
of the Hermitian pairing of two complex joint chaos elements of the step over two families of
mark sets is the constant bidegree Gram. -/
theorem condExp_jointChaosStepProfileC_mul_conj (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (hM : M ≤ mΩ)
    (hind : ∀ {m : ℕ} (C : Fin m → Set (ℝ × E)), (∀ k, MeasurableSet (C k)) →
      (∀ k, C k ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ) →
        Indep (D.stepSigma C (a : ℝ) (b : ℝ)) M P)
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    P[fun ω => D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω) | M]
      =ᵐ[P] fun _ => (((if r = r' then (r.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ r
          else 0 : ℝ)) : ℂ)
        * (if s = s' then (s.factorial : ℂ) * ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
            * ∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s
          else 0) := by
  have hCm := measurableSet_append_strip a b hA hA'
  have h := condExp_indep_eq (D.stepSigma_le _ hCm (a : ℝ) (b : ℝ)) hM
    (D.measurable_jointChaosStepProfileC_mul_conj_stepSigma j a b A A' r s r' s' c
      c').stronglyMeasurable (hind _ hCm (append_strip_subset a b A A'))
  rw [D.integral_jointChaosStepProfileC_mul_conj_cross j hab hA hAν hd hA' hAν' hd'] at h
  exact h
end Node

end LevyStochCalc.Driver.LevyDriver


