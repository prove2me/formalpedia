-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d7521a4e-bae8-51dd-92de-91dce229dc24

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.algebraMap_mem' IsCurveOver Place.evalAt Place.chartRead_apply Place.analyticAt_evalAt_extChartAt_symm_of_mem"
namespace OrderDictionaryProof
p2m_open "AlgebraicCurve"

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
  · have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    exact le_of_eq this.symm
  · exact (ord_pos_of_not_isUnit v (fun h0 => hf0 (by simpa using congrArg Subtype.val h0)) hu).le

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] (f : F) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  by_cases hf0 : f = 0
  · subst hf0
    convert Set.finite_empty
    ext w
    simp
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

end Algebra

theorem isOpen_setOf_mem {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [T2Space (Place ℂ F)] (f : F) :
    IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
  have h : {w : Place ℂ F | f ∈ w.toValuationSubring} =
      {w : Place ℂ F | f ∉ w.toValuationSubring}ᶜ := by
    ext w; simp
  rw [h]
  exact (finite_setOf_not_mem (K := ℂ) f).isClosed.isOpen_compl

section Charts

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem eventually_chartRead_eq (w P Q : Place ℂ F) (hw : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source)
    (hP : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w Q), ∀ f : F,
      w.chartRead f z =
        P.chartRead f (extChartAt 𝓘(ℂ, ℂ) P ((extChartAt 𝓘(ℂ, ℂ) w).symm z)) := by
  have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) w).symm (extChartAt 𝓘(ℂ, ℂ) w Q) :=
    continuousAt_extChartAt_symm' hw
  have hmem : (extChartAt 𝓘(ℂ, ℂ) P).source ∈
      𝓝 ((extChartAt 𝓘(ℂ, ℂ) w).symm (extChartAt 𝓘(ℂ, ℂ) w Q)) := by
    rw [(extChartAt 𝓘(ℂ, ℂ) w).left_inv hw]
    exact (isOpen_extChartAt_source P).mem_nhds hP
  filter_upwards [hc.preimage_mem_nhds hmem] with z hz f
  simp only [Place.chartRead_apply]
  rw [(extChartAt 𝓘(ℂ, ℂ) P).left_inv hz]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticAt_coordChange (w P Q : Place ℂ F) (hw : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source)
    (hP : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm)
      (extChartAt 𝓘(ℂ, ℂ) w Q) := by
  have hy : extChartAt 𝓘(ℂ, ℂ) w Q ∈
      ((extChartAt 𝓘(ℂ, ℂ) w).symm ≫ extChartAt 𝓘(ℂ, ℂ) P).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine ⟨(extChartAt 𝓘(ℂ, ℂ) w).map_source hw, ?_⟩
    rw [Set.mem_preimage, (extChartAt 𝓘(ℂ, ℂ) w).left_inv hw]
    exact hP
  have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) P w hy
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.analyticAt

end Charts

section Compatible

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
    [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem deriv_coordChange_ne_zero (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    deriv (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w w) ≠ 0 := by
  set τ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm with hτ
  set σ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hσ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) w w) :=
    analyticAt_coordChange w v w (mem_extChartAt_source w) hw
  have hσa : AnalyticAt ℂ σ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) w w) = extChartAt 𝓘(ℂ, ℂ) v w := by
    simp [hτ]
  have hid : (σ ∘ τ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)] id := by
    have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w), z ∈ (extChartAt 𝓘(ℂ, ℂ) w).target :=
      extChartAt_target_mem_nhds w
    have h2 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w),
        (extChartAt 𝓘(ℂ, ℂ) w).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) v).source := by
      refine (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v).mem_nhds hw
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hσ, hτ, Function.comp_apply, id_eq]
    rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hz2, (extChartAt 𝓘(ℂ, ℂ) w).right_inv hz1]
  have hcomp : HasDerivAt (σ ∘ τ)
      (deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) w w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) w w))
      (extChartAt 𝓘(ℂ, ℂ) w w) := by
    refine HasDerivAt.comp _ ?_ hτa.differentiableAt.hasDerivAt
    rw [hτw]
    exact hσa.differentiableAt.hasDerivAt
  have hone : deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) w w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) w w) = 1 := by
    rw [← (hcomp.congr_of_eventuallyEq hid.symm).deriv, deriv_id]
  intro h0
  rw [h0, mul_zero] at hone
  exact zero_ne_one hone

theorem enat_map_eq_coe {o : ℕ∞} {k : ℤ} (h : o.map (fun n : ℕ => (n : ℤ)) = (k : WithTop ℤ)) :
    o ≠ ⊤ ∧ ((o.toNat : ℕ) : ℤ) = k := by
  induction o using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    simp only [ENat.map_coe, WithTop.coe_eq_coe] at h
    exact ⟨ENat.coe_ne_top m, by simpa using h⟩

theorem analyticOrderAt_chartRead_sub (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (hf : f ∈ w.toValuationSubring) (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    (analyticOrderAt (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w)).map
        (fun n : ℕ => (n : ℤ)) = ((w.ord (f - algebraMap ℂ F t) : ℤ) : WithTop ℤ) := by
  obtain ⟨-, hord⟩ := hF (f - algebraMap ℂ F t) hne w
  have hreg : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) w).symm z).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds
      (t := {w' : Place ℂ F | f ∈ w'.toValuationSubring})
      (by rw [extChartAt_to_inv]; exact (isOpen_setOf_mem f).mem_nhds hf)
    exact this
  have hEq : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) (f - algebraMap ℂ F t))
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)] fun z => w.chartRead f z - t := by
    filter_upwards [hreg] with z hz
    rw [Place.chartRead_apply, sub_eq_add_neg, ← map_neg,
      evalAt_add _ (isRational _) hz (Place.algebraMap_mem' _ _), evalAt_algebraMap]
    ring
  rw [meromorphicOrderAt_congr (hEq.filter_mono nhdsWithin_le_nhds)] at hord
  have hA : AnalyticAt ℂ (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w) :=
    (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf).sub analyticAt_const
  rw [hA.meromorphicOrderAt_eq] at hord
  exact hord

end Compatible

end AlgebraicCurve.OrderDictionaryProof

open AlgebraicCurve.OrderDictionaryProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) {f : F}
    (hf : f ∈ w.toValuationSubring) (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    analyticOrderAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) ≠ ⊤ ∧
      w.ord (f - algebraMap ℂ F t) =
        (analyticOrderNatAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) : ℤ) := by
  have hFc : ChartCompatible F := hF
  have h1 := analyticOrderAt_chartRead_sub hFc w hf t hne
  set τ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm with hτ
  have hreads := eventually_chartRead_eq w v w (mem_extChartAt_source w) hw
  have hEq : (fun z => w.chartRead f z - t) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)]
      ((fun z => v.chartRead f z - t) ∘ τ) :=
    hreads.mono fun z hz => by simp only [Function.comp_apply, hτ, hz f]
  rw [analyticOrderAt_congr hEq, analyticOrderAt_comp_of_deriv_ne_zero
      (analyticAt_coordChange w v w (mem_extChartAt_source w) hw)
      (deriv_coordChange_ne_zero v w hw)] at h1
  simp only [Function.comp_apply, extChartAt_to_inv] at h1
  obtain ⟨htop, hk⟩ := enat_map_eq_coe h1
  exact ⟨htop, by rw [← hk]; rfl⟩

end

end S_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead (solution)
