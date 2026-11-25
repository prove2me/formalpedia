-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:44:54.092799+00:00
-- url     : https://prove2.me/theorems/0548bba1-5074-465f-8f80-d1c2c7ddcd06
-- title:
--   Bounded On Frames Iff Integral On Frames
-- statement:
--   Definitions and structural lemmas for Bounded On Frames Iff Integral On Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_HasTriangularWeight_smul
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_exists_injective_algHom_integralClosure
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff
import Theorems.Thm_GlobalTheory_mem_maximalIdeal_integralClosure_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X


set_option autoImplicit false
namespace GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
section Series
variable {K : Type*} [NormedField K] [CompleteSpace K] {O : Type*} [CommRing O]
  (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) {t : K} (ht : ‖t‖ < 1)
omit [CompleteSpace K] in
include hi ht in
theorem summable_norm_term (f : O⟦X⟧) :
    Summable fun n : ℕ => ‖i (PowerSeries.coeff n f) * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg t) ht)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hi _)
noncomputable def discEval : O⟦X⟧ →+* K :=
  GlobalTheory.BoundedPowerSeriesDisc.evalDisc i hi t ht
theorem hasSum_discEval (f : O⟦X⟧) :
    HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) :=
  (summable_norm_term i hi ht f).of_norm.hasSum
@[simp] theorem discEval_C (a : O) : discEval i hi ht (PowerSeries.C a) = i a := by
  refine (hasSum_discEval i hi ht _).unique ?_
  convert hasSum_single 0 fun n hn => ?_ using 1
  · simp
  · simp [PowerSeries.coeff_C, hn]
@[simp] theorem discEval_X : discEval i hi ht PowerSeries.X = t := by
  refine (hasSum_discEval i hi ht _).unique ?_
  convert hasSum_single 1 fun n hn => ?_ using 1
  · simp
  · simp [PowerSeries.coeff_X, hn]
theorem norm_discEval_le_one [IsUltrametricDist K] (f : O⟦X⟧) : ‖discEval i hi ht f‖ ≤ 1 := by
  rw [← (hasSum_discEval i hi ht f).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hi _) (by positivity) (pow_le_one₀ (norm_nonneg _) ht.le)
end Series
section Away
variable {K : Type*} {O : Type*} [CommRing O] (π : O)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
section Laurent
variable [Field K] (i : O →+* K) (hπ : i π ≠ 0)
noncomputable def laurent : A →+* K⸨X⸩ :=
  IsLocalization.Away.lift (PowerSeries.C π * PowerSeries.X : O⟦X⟧)
    (g := (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i)) (by
      rw [isUnit_iff_ne_zero, RingHom.comp_apply,
        map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_mul, PowerSeries.map_C,
        PowerSeries.map_X]
      exact mul_ne_zero (by simpa using hπ) PowerSeries.X_ne_zero)
@[simp] theorem laurent_algebraMap (f : O⟦X⟧) :
    laurent π A i hπ (algebraMap O⟦X⟧ A f) = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map i f) :=
  IsLocalization.Away.lift_eq _ _ f
variable {π A}
end Laurent
section Value
variable [NormedField K] [CompleteSpace K] (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)
noncomputable def discEvalAway : A →+* K :=
  IsLocalization.Away.lift (PowerSeries.C π * PowerSeries.X : O⟦X⟧) (g := discEval i hi ht) (by
    rw [isUnit_iff_ne_zero, map_mul, discEval_C, discEval_X]
    exact mul_ne_zero hπ ht0)
@[simp] theorem discEvalAway_algebraMap (f : O⟦X⟧) :
    discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f :=
  IsLocalization.Away.lift_eq _ _ f
variable {π A}
end Value
end Away
section Coefficients
open MvPolynomial
variable {K : Type*} [Field K] {σ τ : Type*}
noncomputable def coeffPoly (m : ℤ) (G : MvPolynomial σ K⸨X⸩) : MvPolynomial σ K :=
  ∑ μ ∈ G.support, monomial μ ((coeff μ G).coeff m)
@[simp] theorem coeff_coeffPoly (m : ℤ) (G : MvPolynomial σ K⸨X⸩) (μ : σ →₀ ℕ) :
    coeff μ (coeffPoly m G) = (coeff μ G).coeff m := by
  classical
  simp only [coeffPoly, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [notMem_support_iff.1 h]
end Coefficients
section Core
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]
end Core
section Padic
theorem exists_comp_eq_of_mem_range {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    (e : B →+* K) (he : Function.Injective e) (φ : R →+* K) (h : ∀ a, φ a ∈ e.range) :
    ∃ ψ : R →+* B, ∀ a, e (ψ a) = φ a := by
  let ε : B ≃+* e.range := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b hab => he (congrArg Subtype.val hab), e.rangeRestrict_surjective⟩
  exact ⟨ε.symm.toRingHom.comp (φ.codRestrict e.range h), fun a =>
    congrArg Subtype.val (ε.apply_symm_apply ⟨φ a, h a⟩)⟩
variable (p : ℕ) [Fact p.Prime]
noncomputable def algField : Subfield ℂ_[p] := (algebraMap (PadicAlgCl p) ℂ_[p]).fieldRange
def algDisc : Set ℂ_[p] := {t | t ∈ algField p ∧ 0 < ‖t‖ ∧ ‖t‖ < 1}
variable {p}
theorem mem_algField_iff {x : ℂ_[p]} : x ∈ algField p ↔ IsIntegral ℚ_[p] x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).algebraMap
  · intro hx
    have h : IsIntegral (PadicAlgCl p) x := hx.tower_top
    exact minpoly.mem_range_of_degree_eq_one _ _
      (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h))
theorem ringHom_padicInt_eq (g : ℤ_[p] →+* ℂ_[p]) (hg : ∀ z, ‖g z‖ ≤ 1) (z : ℤ_[p]) :
    g z = algebraMap ℚ_[p] ℂ_[p] z := by
  let h : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hh : ∀ z, ‖h z‖ ≤ 1 := fun z => by
    change ‖algebraMap ℚ_[p] ℂ_[p] z‖ ≤ 1
    rw [norm_algebraMap']
    exact z.2
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have key : ∀ n : ℕ, ‖g z - h z‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun n => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = y * p ^ n + (z.appr n : ℕ) := by rw [hy]; ring
    have : g z - h z = (g y + -h y) * p ^ n := by
      conv_lhs => rw [hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hg y) (by rw [norm_neg]; exact hh y)))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
noncomputable def fieldEmb (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : L →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap L (PadicAlgCl p))
noncomputable def intEmb (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    integralClosure ℤ_[p] L →+* ℂ_[p] :=
  (fieldEmb L).comp (algebraMap (integralClosure ℤ_[p] L) L)
section Field
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))
theorem fieldEmb_apply (x : L) : fieldEmb L x = ((x : PadicAlgCl p) : ℂ_[p]) := rfl
theorem intEmb_apply (x : integralClosure ℤ_[p] L) : intEmb L x = fieldEmb L x := rfl
theorem intEmb_injective : Function.Injective (intEmb L) :=
  (fieldEmb L).injective.comp Subtype.val_injective
theorem mem_integralClosure_iff_norm (x : L) : x ∈ integralClosure ℤ_[p] L ↔ ‖fieldEmb L x‖ ≤ 1 := by
  rw [mem_integralClosure_padicInt_iff, fieldEmb_apply, PadicComplex.norm_extends]
theorem norm_intEmb_le_one (x : integralClosure ℤ_[p] L) : ‖intEmb L x‖ ≤ 1 :=
  (mem_integralClosure_iff_norm L x).1 x.2
theorem mem_range_intEmb_iff (x : ℂ_[p]) :
    x ∈ (intEmb L).range ↔ x ∈ (fieldEmb L).fieldRange ∧ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, rfl⟩, norm_intEmb_le_one L y⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨⟨y, (mem_integralClosure_iff_norm L y).2 hy⟩, rfl⟩
variable [FiniteDimensional ℚ_[p] L]
theorem mem_maximalIdeal_iff_norm (x : integralClosure ℤ_[p] L) :
    x ∈ maximalIdeal (integralClosure ℤ_[p] L) ↔ ‖intEmb L x‖ < 1 := by
  rw [mem_maximalIdeal_integralClosure_iff, intEmb_apply, fieldEmb_apply, PadicComplex.norm_extends]
theorem isUnit_iff_norm (x : integralClosure ℤ_[p] L) : IsUnit x ↔ ‖intEmb L x‖ = 1 := by
  rw [← notMem_maximalIdeal, mem_maximalIdeal_iff_norm, not_lt]
  exact ⟨fun h => le_antisymm (norm_intEmb_le_one L x) h, fun h => h.ge⟩
end Field
section Finite
variable {O : Type*} [CommRing O] [Algebra ℤ_[p] O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1)
include hi in

theorem map_algebraMap_padicInt (z : ℤ_[p]) :
    i (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] ℂ_[p] z :=
  ringHom_padicInt_eq (i.comp (algebraMap ℤ_[p] O)) (fun _ => hi _) z
noncomputable def genField (T : Set ℂ_[p]) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {y : PadicAlgCl p | (y : ℂ_[p]) ∈ Set.range i ∪ T}
variable [Module.Finite ℤ_[p] O]
include hi
theorem map_mem_algField (x : O) : i x ∈ algField p := by
  obtain ⟨q, hq, hqx⟩ : IsIntegral ℤ_[p] x := Algebra.IsIntegral.isIntegral x
  refine mem_algField_iff.2 ⟨q.map (algebraMap ℤ_[p] ℚ_[p]), hq.map _, ?_⟩
  have h : (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p]) = i.comp (algebraMap ℤ_[p] O) :=
    RingHom.ext fun z => (map_algebraMap_padicInt i hi z).symm
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hqx, map_zero]
theorem fieldRange_genField {T : Set ℂ_[p]} (hT : T ⊆ algField p) :
    (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) := by
  refine le_antisymm ?_ (Subfield.closure_le.2 fun x hx => ?_)
  · rintro _ ⟨⟨y, hy⟩, rfl⟩
    change algebraMap (PadicAlgCl p) ℂ_[p] y ∈ _
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy => exact Subfield.subset_closure hy
    | algebraMap z =>
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) z
      rw [← IsScalarTower.algebraMap_apply, map_div₀]
      exact div_mem (Subfield.subset_closure (Or.inl ⟨_, map_algebraMap_padicInt i hi a⟩))
        (Subfield.subset_closure (Or.inl ⟨_, map_algebraMap_padicInt i hi b⟩))
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  · obtain ⟨y, rfl⟩ : x ∈ algField p := by
      rcases hx with ⟨a, rfl⟩ | hx
      exacts [map_mem_algField i hi a, hT hx]
    exact ⟨⟨y, IntermediateField.subset_adjoin _ _ hx⟩, rfl⟩
theorem map_mem_genField {T : Set ℂ_[p]} (hT : T ⊆ algField p) (x : O) :
    i x ∈ (fieldEmb (genField i T)).fieldRange := by
  rw [fieldRange_genField i hi hT]
  exact Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
theorem finiteDimensional_genField {T : Set ℂ_[p]} (hT : T.Finite) :
    FiniteDimensional ℚ_[p] (genField i T) := by
  have hinj := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  obtain ⟨i₀, hi₀⟩ := exists_comp_eq_of_mem_range _ hinj i (map_mem_algField i hi)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := O)
  set U : Set (PadicAlgCl p) := i₀ '' s ∪ algebraMap (PadicAlgCl p) ℂ_[p] ⁻¹' T
  have : Finite U := ((s.finite_toSet.image _).union (hT.preimage hinj.injOn)).to_subtype
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] U) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ b, i₀ b ∈ IntermediateField.adjoin ℚ_[p] U := fun b => by
    have hb : b ∈ Submodule.span ℤ_[p] (s : Set O) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have : i₀ (algebraMap ℤ_[p] O a) = algebraMap ℚ_[p] (PadicAlgCl p) a := hinj (by
        rw [hi₀, map_algebraMap_padicInt i hi, ← IsScalarTower.algebraMap_apply])
      rw [Algebra.smul_def, map_mul, this]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
  have hle : genField i T ≤ IntermediateField.adjoin ℚ_[p] U := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro y (⟨a, ha⟩ | hy)
    · rw [← hinj ((hi₀ a).trans ha)]
      exact hmem a
    · exact IntermediateField.subset_adjoin _ _ (Or.inr hy)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
omit [Module.Finite ℤ_[p] O] in

theorem finite_of_intEmb_eq {j : O →+* integralClosure ℤ_[p] L} (hj : ∀ a, intEmb L (j a) = i a) :
    j.Finite := by
  have h : j.comp (algebraMap ℤ_[p] O) = algebraMap ℤ_[p] (integralClosure ℤ_[p] L) :=
    RingHom.ext fun z => intEmb_injective L (by
      rw [RingHom.comp_apply, hj, map_algebraMap_padicInt i hi]
      exact (map_algebraMap_padicInt (intEmb L) (norm_intEmb_le_one L) z).symm)
  refine RingHom.Finite.of_comp_finite (f := algebraMap ℤ_[p] O) ?_
  rw [h, RingHom.finite_algebraMap]
  infer_instance
omit [Module.Finite ℤ_[p] O] in
theorem isLocalHom_of_intEmb_eq (hinj : Function.Injective i)
    {j : O →+* integralClosure ℤ_[p] L} (hj : ∀ a, intEmb L (j a) = i a) : IsLocalHom j :=
  RingHom.IsIntegral.isLocalHom (finite_of_intEmb_eq i hi L hj).to_isIntegral
    fun a b h => hinj (by rw [← hj, ← hj, h])
theorem norm_map_eq_one_iff (hinj : Function.Injective i) (x : O) : ‖i x‖ = 1 ↔ IsUnit x := by
  have := finiteDimensional_genField i hi Set.finite_empty
  obtain ⟨j, hj⟩ := exists_comp_eq_of_mem_range _ (intEmb_injective (genField i ∅)) i fun a =>
    (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi (Set.empty_subset _) a, hi a⟩
  have := isLocalHom_of_intEmb_eq i hi _ hinj hj
  rw [← hj, ← isUnit_iff_norm, isUnit_map_iff]
end Finite
theorem exists_injective_norm_le_one (O : Type*) [CommRing O] [IsDomain O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (hp : (p : O) ≠ 0) :
    ∃ i : O →+* ℂ_[p], Function.Injective i ∧ ∀ x, ‖i x‖ ≤ 1 := by
  obtain ⟨L, _, g, hg⟩ := exists_injective_algHom_integralClosure O hp
  exact ⟨(intEmb L).comp g, (intEmb_injective L).comp hg, fun x => norm_intEmb_le_one L _⟩
section Points
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
def IsDiscPoint (L : IntermediateField ℚ_[p] (PadicAlgCl p)) {t : ℂ_[p]} (ht0 : t ≠ 0)
    (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L) : Prop :=
  (∀ f, intEmb L (ev f) = discEval i hi ht f) ∧
    ∀ f, fieldEmb L (evA f) = discEvalAway π A i hi hπ ht0 ht f
end Points
section Frames
open MvPolynomial
variable (p) in

def algInt : Subring ℂ_[p] where
  carrier := {x | x ∈ algField p ∧ ‖x‖ ≤ 1}
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by
    rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_mem _, norm_one.le⟩
  add_mem' ha hb := ⟨add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
def BoundedOnFrames (F : MvPolynomial (EntryIndex n n) A) : Prop :=
  ∀ t ∈ algField p, ∀ (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (g : ∀ s, GL (n s) (algInt p)),
    ‖eval₂ (discEvalAway π A i hi hπ ht0 ht)
      (entries fun s => (g s : Matrix (n s) (n s) (algInt p)).map (algInt p).subtype) F‖ ≤ 1
def IntegralOnFrames (F : MvPolynomial (EntryIndex n n) A) : Prop :=
  ∀ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] (t : ℂ_[p])
    (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L),
    IsDiscPoint i hi hπ A L ht0 ht ev evA → ∀ g : ∀ s, GL (n s) (integralClosure ℤ_[p] L),
      eval₂ evA (entries fun s => (g s : Matrix (n s) (n s) (integralClosure ℤ_[p] L)).map
        (algebraMap (integralClosure ℤ_[p] L) L)) F ∈ integralClosure ℤ_[p] L
variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}
theorem boundedOnFrames_map (F₀ : MvPolynomial (EntryIndex n n) O⟦X⟧) :
    BoundedOnFrames i hi hπ (map (algebraMap O⟦X⟧ A) F₀) := by
  intro t _ ht0 ht g
  rw [eval₂_map, eval₂_eq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [norm_mul, RingHom.comp_apply, discEvalAway_algebraMap, norm_prod]
  refine mul_le_one₀ (norm_discEval_le_one i hi ht _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_)
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ((g k.1).1 k.2.1 k.2.2).2.2
end Frames
end Padic
example (p : ℕ) [Fact p.Prime] :
    ∃ (i : ℤ_[p] →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) (_ : Function.Injective i) (hπ : i p ≠ 0),
      ‖i p‖ < 1 ∧ BoundedOnFrames i hi hπ (MvPolynomial.map (algebraMap ℤ_[p]⟦X⟧
        (Localization.Away (PowerSeries.C (p : ℤ_[p]) * PowerSeries.X : ℤ_[p]⟦X⟧)))
        (detProdPoly ℤ_[p]⟦X⟧ fun _ : Fin 2 => Fin 3)) := by
  have hp : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  obtain ⟨i, hinj, hi⟩ := exists_injective_norm_le_one (p := p) ℤ_[p] hp.ne_zero
  exact ⟨i, hi, hinj, (map_ne_zero_iff i hinj).2 hp.ne_zero,
    (hi p).lt_of_ne fun h => hp.not_isUnit ((norm_map_eq_one_iff i hi hinj p).1 h),
    boundedOnFrames_map _⟩
end GlobalTheory.DiscEval


