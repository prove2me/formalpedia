-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:31.037841+00:00
-- url     : https://prove2.me/theorems/6ce0b76f-bc7c-499c-9a8c-bd32e64ad16b
-- title:
--   Twisting Sheaf One Chart Eq Preimage Standard Chart
-- statement:
--   Definitions and structural lemmas for Twisting Sheaf One Chart Eq Preimage Standard Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Theorems.Thm_GlobalTheory_ProjFrac_awayToSection_mk
import Theorems.Thm_GlobalTheory_ProjFrac_basicOpen_frac
import Theorems.Thm_GlobalTheory_ProjFrac_frac_pow
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_comp_SpecMap
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_res
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a
import Theorems.Thm_ReciprocityTheory_AnForm_R_toSpecZero_appLE_basicOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.ProjSpace
variable (R : Type) [CommRing R] (N : ℕ)
abbrev grading : ℕ → Submodule R (MvPolynomial (Fin (N + 1)) R) :=
  homogeneousSubmodule (Fin (N + 1)) R
theorem X_mem (i : Fin (N + 1)) : (X i : MvPolynomial (Fin (N + 1)) R) ∈ grading R N 1 :=
  isHomogeneous_X R i
theorem X_pow_mem (i : Fin (N + 1)) (n : ℕ) :
    (X i ^ n : MvPolynomial (Fin (N + 1)) R) ∈ grading R N n :=
  isHomogeneous_X_pow i n
abbrev chart (i : Fin (N + 1)) : (PSpace R N).Opens :=
  Proj.basicOpen (grading R N) (X i)
theorem mem_span_X_of_isHomogeneous {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) : f ∈ Ideal.span (Set.range (X : Fin (N + 1) → MvPolynomial _ R)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! H
  obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
  have := hf (mem_support_iff.1 hm)
  simp only [map_zero] at this
  omega
theorem irrelevant_le_span_X : (HomogeneousIdeal.irrelevant (grading R N)).toIdeal ≤
    Ideal.span (Set.range (X : Fin (N + 1) → MvPolynomial _ R)) :=
  (HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_isHomogeneous R N hn hf
theorem iSup_chart : ⨆ i, chart R N i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (irrelevant_le_span_X R N)
theorem exists_mem_chart (x : PSpace R N) : ∃ i, x ∈ chart R N i :=
  Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))
variable {R N}
theorem le_basicOpen_X_pow {U : (PSpace R N).Opens} {i : Fin (N + 1)} (hU : U ≤ chart R N i) (n : ℕ) :
    U ≤ Proj.basicOpen (grading R N) (X i ^ n) :=
  fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)
def formOn (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hU : U ≤ chart R N i) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) : Γ(PSpace R N, U) :=
  frac (grading R N) U f (X i ^ n) hf (X_pow_mem R N i n) (le_basicOpen_X_pow hU n)
def ratioOn (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hU : U ≤ chart R N i) (j : Fin (N + 1)) :
    Γ(PSpace R N, U) :=
  frac (grading R N) U (X j) (X i) (X_mem R N j) (X_mem R N i) hU
variable (R N) in

abbrev ratio (i j : Fin (N + 1)) : Γ(PSpace R N, chart R N i) := ratioOn (chart R N i) i le_rfl j
def ratioUnit (U : (PSpace R N).Opens) (i j : Fin (N + 1)) (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) :
    Γ(PSpace R N, U)ˣ :=
  fracUnit (grading R N) U (X j) (X i) (X_mem R N j) (X_mem R N i) hj hi
section
variable {U V : (PSpace R N).Opens} {i j k : Fin (N + 1)} {hi : U ≤ chart R N i} {hj : U ≤ chart R N j}
  {hk : U ≤ chart R N k} {n m : ℕ} {f g : MvPolynomial (Fin (N + 1)) R}
@[simp] theorem val_ratioUnit : (ratioUnit U i j hi hj : Γ(PSpace R N, U)) = ratioOn U i hi j := rfl
@[simp] theorem ratioOn_self : ratioOn U i hi i = 1 := frac_self
theorem ratioOn_mul_ratioOn : ratioOn U i hi j * ratioOn U j hj k = ratioOn U i hi k :=
  frac_mul_eq (by ring)
theorem basicOpen_ratioOn : (PSpace R N).basicOpen (ratioOn U i hi j) = U ⊓ chart R N j :=
  basicOpen_frac
theorem formOn_eq_ratioOn_pow_mul (hj : U ≤ chart R N j) (hf : f.IsHomogeneous n) :
    formOn U i hi n f hf = ratioOn U i hi j ^ n * formOn U j hj n f hf := by
  rw [ratioOn, frac_pow]
  exact (frac_mul_eq (by ring)).symm
end
variable (R N)
def O1 : LB (PSpace R N) where
  ι := Fin (N + 1)
  U := chart R N
  g i j := ratioUnit (chart R N i ⊓ chart R N j) i j inf_le_left inf_le_right
@[simp] theorem twistingSheafOne_chart_eq_preimage_standardChart (i : Fin (N + 1)) : (O1 R N).U i = Proj.basicOpen (grading R N) (X i) := rfl
def coord (k : Fin (N + 1)) : (O1 R N).Sec where
  f i := ratio R N i k
  compat _ _ := (ratioOn_mul_ratioOn (hi := inf_le_left) (hj := inf_le_right)).symm
@[simp] theorem coord_f (k i : Fin (N + 1)) : (coord R N k).f i = ratio R N i k := rfl
theorem nonzeroLocus_coord (k : Fin (N + 1)) : nonzeroLocus (coord R N k) = (O1 R N).U k := by
  change ⨆ i, (PSpace R N).basicOpen (ratio R N i k) = chart R N k
  simp only [ratio, basicOpen_ratioOn]
  rw [← iSup_inf_eq, iSup_chart, top_inf_eq]
theorem linComb_punit_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℤ) (i j : PUnit → L.ι) :
    (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).g i j =
      res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => φ) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ => φ) j PUnit.unit)) :
          LB.wchart L (fun _ => φ) i ⊓ LB.wchart L (fun _ => φ) j ≤
            φ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)))
        (pullU φ _ (L.g (i PUnit.unit) (j PUnit.unit))) ^ n := by
  simp only [LB.LinComb, Fintype.prod_unique]
  rfl
abbrev On (n : ℤ) : LB (PSpace R N) :=
  LB.LinComb (O1 R N) (K := PUnit) (fun _ => 𝟙 (PSpace R N)) (fun _ => n)
theorem On_U (n : ℤ) (j : PUnit → Fin (N + 1)) : (On R N n).U j = chart R N (j PUnit.unit) :=
  le_antisymm (LB.wchart_le (O1 R N) (fun _ => 𝟙 (PSpace R N)) j PUnit.unit)
    fun _ hx => Set.mem_iInter.2 fun _ => hx
theorem On_g (n : ℤ) (i j : PUnit → Fin (N + 1)) :
    (On R N n).g i j = ratioUnit ((On R N n).U i ⊓ (On R N n).U j) (i PUnit.unit) (j PUnit.unit)
      (inf_le_left.trans (On_U R N n i).le) (inf_le_right.trans (On_U R N n j).le) ^ n :=
  (linComb_punit_g (O1 R N) (𝟙 _) n i j).trans (congrArg (· ^ n) (Units.ext rfl))
variable {R N}
def formSec (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    (lbPow (O1 R N) n).Sec where
  f j := formOn _ (j PUnit.unit) (On_U R N n j).le n f hf
  compat i j := by
    have e := On_g R N n i j
    rw [zpow_natCast] at e
    have e' := (congrArg Units.val e).trans (Units.val_pow_eq_pow_val _ _)
    exact (formOn_eq_ratioOn_pow_mul (hi := inf_le_left.trans (On_U R N n i).le)
      (inf_le_right.trans (On_U R N n j).le) hf).trans (congrArg (· * _) e'.symm)
@[simp] theorem formSec_f (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n)
    (j : PUnit → Fin (N + 1)) :
    (formSec n f hf).f j = formOn _ (j PUnit.unit) (On_U R N n j).le n f hf := rfl
variable (R N)
@[instance_reducible]
scoped instance algebraSections (U : (PSpace R N).Opens) : Algebra R Γ(PSpace R N, U) :=
  (baseRingHom (PSpace.str R N) U).hom.toAlgebra
variable {R N} in

theorem resG_algebraMap {U V : (PSpace R N).Opens} (h : V ≤ U) (r : R) :
    resG _ h (algebraMap R Γ(PSpace R N, U) r) = algebraMap R Γ(PSpace R N, V) r :=
  baseRingHom_res (PSpace.str R N) h r
def constAway (i : Fin (N + 1)) : R →+* HomogeneousLocalization.Away (grading R N) (X i) :=
  (HomogeneousLocalization.fromZeroRingHom (grading R N) _).comp (algebraMap R (grading R N 0))
theorem algebraMap_chart (i : Fin (N + 1)) (r : R) :
    algebraMap R Γ(PSpace R N, chart R N i) r =
      (Proj.awayToSection (grading R N) (X i)).hom (constAway R N i r) := by
  have h := baseRingHom_comp_SpecMap (Proj.toSpecZero (grading R N))
    (CommRingCat.ofHom (algebraMap R (grading R N 0))) (chart R N i)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading R N) (X_mem R N i) one_pos
  rw [baseRingHom.eq_1 (Proj.toSpecZero _), h'] at h
  exact congrArg (fun φ => φ.hom r) h
def dehom (i : Fin (N + 1)) : MvPolynomial (Fin (N + 1)) R →ₐ[R] MvPolynomial {j // j ≠ i} R :=
  aeval fun j => if h : j = i then 1 else X ⟨j, h⟩
@[simp] theorem dehom_X_self (i : Fin (N + 1)) : dehom R N i (X i) = 1 := by simp [dehom]
@[simp] theorem dehom_X_of_ne (i : Fin (N + 1)) (j : {j // j ≠ i}) : dehom R N i (X j.1) = X j := by
  simp [dehom, j.2]
def ratioAway (i j : Fin (N + 1)) : HomogeneousLocalization.Away (grading R N) (X i) :=
  HomogeneousLocalization.Away.mk (grading R N) (X_mem R N i) 1 (X j) (X_mem R N j)
def polyToAway (i : Fin (N + 1)) :
    MvPolynomial {j // j ≠ i} R →+* HomogeneousLocalization.Away (grading R N) (X i) :=
  eval₂Hom (constAway R N i) fun j => ratioAway R N i j.1
def awayToPoly (i : Fin (N + 1)) :
    HomogeneousLocalization.Away (grading R N) (X i) →+* MvPolynomial {j // j ≠ i} R :=
  (IsLocalization.Away.lift (S := Localization.Away (X i : MvPolynomial (Fin (N + 1)) R)) (X i)
    (g := (dehom R N i).toRingHom) (by simp)).comp (algebraMap _ _)
theorem awayToPoly_mk (i : Fin (N + 1)) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f ∈ grading R N (n • 1)) :
    awayToPoly R N i (HomogeneousLocalization.Away.mk (grading R N) (X_mem R N i) n f hf) =
      dehom R N i f := by
  simp only [awayToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  simp
theorem polyToAway_dehom (i : Fin (N + 1)) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f ∈ grading R N (n • 1)) :
    polyToAway R N i (dehom R N i f) =
      HomogeneousLocalization.Away.mk (grading R N) (X_mem R N i) n f hf := by
  let L := Localization.Away (X i : MvPolynomial (Fin (N + 1)) R)
  let t : L := Localization.mk 1 ⟨X i, 1, pow_one _⟩
  let a := algebraMap (MvPolynomial (Fin (N + 1)) R) L
  have h1 : ((algebraMap _ L).comp (polyToAway R N i)).comp (dehom R N i).toRingHom =
      eval₂Hom (a.comp C) (fun j => a (X j) * t) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [polyToAway, constAway]
      rfl
    · have e : a (X j) * t = Localization.mk (X j) (⟨X i ^ 1, 1, rfl⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R)) := by
        rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
        congr 1
        all_goals simp
      rw [eval₂Hom_X', e]
      by_cases h : j = i
      · subst h
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehom_X_self, map_one]
        rw [eq_comm, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp⟩
      · have := dehom_X_of_ne R N i ⟨j, h⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this, polyToAway,
          eval₂Hom_X']
        rfl
  apply HomogeneousLocalization.val_injective
  have h2 := congrArg (fun φ => φ f) h1
  have hf' : f.IsHomogeneous n := by simpa using hf
  simp only [coe_eval₂Hom, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hf'] at h2
  have h3 : eval₂ (a.comp C) (fun j => a (X j)) f = a f := by
    have := eval₂_comp_left a C X f
    rw [eval₂_eta] at this
    exact this.symm
  refine h2.trans ?_
  rw [h3, HomogeneousLocalization.Away.val_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow,
    Localization.mk_mul]
  congr 1
  · simp
  · ext1; simp
def polyEquivAway (i : Fin (N + 1)) :
    MvPolynomial {j // j ≠ i} R ≃+* HomogeneousLocalization.Away (grading R N) (X i) where
  __ := polyToAway R N i
  invFun := awayToPoly R N i
  left_inv p := by
    have : (awayToPoly R N i).comp (polyToAway R N i) = RingHom.id _ := by
      refine ringHom_ext (fun r => ?_) (fun j => ?_)
      · have := awayToPoly_mk R N i 0 (C r) (isHomogeneous_C _ r)
        simp only [RingHom.comp_apply, polyToAway, eval₂Hom_C, RingHom.id_apply]
        exact this.trans (by simp)
      · simp only [RingHom.comp_apply, polyToAway, eval₂Hom_X', RingHom.id_apply, ratioAway]
        exact (awayToPoly_mk R N i 1 _ _).trans (dehom_X_of_ne R N i j)
    exact congrArg (fun φ => φ p) this
  right_inv x := by
    obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) x
    rw [awayToPoly_mk]
    exact polyToAway_dehom R N i n f hf
def chartAlgEquiv (i : Fin (N + 1)) :
    MvPolynomial {j // j ≠ i} R ≃ₐ[R] Γ(PSpace R N, chart R N i) where
  __ := (polyEquivAway R N i).trans
    (Proj.basicOpenIsoAway (grading R N) (X i) (X_mem R N i) one_pos).commRingCatIsoToRingEquiv
  commutes' r := by
    rw [algebraMap_chart]
    exact congrArg (Proj.awayToSection (grading R N) (X i)).hom (eval₂Hom_C _ _ r)
theorem chartAlgEquiv_apply (i : Fin (N + 1)) (p : MvPolynomial {j // j ≠ i} R) :
    chartAlgEquiv R N i p = (Proj.awayToSection (grading R N) (X i)).hom (polyToAway R N i p) := rfl
@[simp] theorem chartAlgEquiv_X (i : Fin (N + 1)) (j : {j // j ≠ i}) :
    chartAlgEquiv R N i (X j) = ratio R N i j.1 := by
  rw [chartAlgEquiv_apply, polyToAway, eval₂Hom_X', ratioAway, awayToSection_mk]
  exact frac_eq (by ring)
theorem chartAlgEquiv_dehom (i : Fin (N + 1)) {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) :
    chartAlgEquiv R N i (dehom R N i f) = formOn (chart R N i) i le_rfl n f hf := by
  rw [chartAlgEquiv_apply, polyToAway_dehom R N i n f (by simpa using hf), awayToSection_mk]
  exact frac_eq rfl
variable {R N} in

theorem formOn_eq_aeval {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    formOn U i hi n f hf = aeval (ratioOn U i hi) f := by
  have h : ((resG _ hi).comp (RingHomClass.toRingHom (chartAlgEquiv R N i))).comp
      (RingHomClass.toRingHom (dehom R N i)) =
      RingHomClass.toRingHom (aeval (ratioOn U i hi) : MvPolynomial (Fin (N + 1)) R →ₐ[R] _) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, algHom_C]
      rw [AlgEquiv.commutes]
      exact resG_algebraMap hi r
    · simp only [RingHom.comp_apply, RingHom.coe_coe, aeval_X]
      by_cases h : j = i
      · subst h
        rw [dehom_X_self, map_one, map_one, ratioOn_self]
      · rw [dehom_X_of_ne R N i ⟨j, h⟩, chartAlgEquiv_X]
        rfl
  have := congrArg (fun φ => φ f) h
  simp only [RingHom.comp_apply, RingHom.coe_coe, chartAlgEquiv_dehom R N i hf] at this
  exact this
def chartι (i : Fin (N + 1)) : Sp (MvPolynomial {j // j ≠ i} R) ⟶ PSpace R N :=
  spMap (awayToPoly R N i) ≫ Proj.awayι (grading R N) (X i) (X_mem R N i) one_pos
instance isIso_spMap_awayToPoly (i : Fin (N + 1)) : IsIso (spMap (awayToPoly R N i)) :=
  inferInstanceAs (IsIso (Spec.map (polyEquivAway R N i).toCommRingCatIso.inv))
instance isOpenImmersion_chartι (i : Fin (N + 1)) : IsOpenImmersion (chartι R N i) := by
  unfold chartι
  infer_instance
theorem opensRange_chartι (i : Fin (N + 1)) : (chartι R N i).opensRange = chart R N i :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)
def chartCover : (PSpace R N).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (N + 1)) (fun i => Sp (MvPolynomial {j // j ≠ i} R)) (chartι R N)
    fun x => by
      obtain ⟨i, hi⟩ := exists_mem_chart R N x
      rw [← opensRange_chartι] at hi
      exact ⟨i, hi⟩
section BaseChange
variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')
def gradedMap : grading R N →+*ᵍ grading R' N where
  __ := MvPolynomial.map φ
  map_mem hf := IsHomogeneous.map hf φ
theorem irrelevant_le_map : HomogeneousIdeal.irrelevant (grading R' N) ≤
    (HomogeneousIdeal.irrelevant (grading R N)).map (gradedMap N φ) := by
  refine (irrelevant_le_span_X R' N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  rw [← map_X φ i]
  exact Ideal.mem_map_of_mem (gradedMap N φ).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem R N i))
def baseChange : PSpace R' N ⟶ PSpace R N :=
  Proj.map (gradedMap N φ) (irrelevant_le_map N φ)
theorem baseChange_preimage_basicOpen (f : MvPolynomial (Fin (N + 1)) R) :
    baseChange N φ ⁻¹ᵁ Proj.basicOpen (grading R N) f =
      Proj.basicOpen (grading R' N) (MvPolynomial.map φ f) := rfl
theorem baseChange_preimage_chart (i : Fin (N + 1)) :
    baseChange N φ ⁻¹ᵁ chart R N i = chart R' N i := by
  rw [chart, baseChange_preimage_basicOpen, map_X]
variable {N} in

theorem baseChange_preimage_le {U : (PSpace R N).Opens} {i : Fin (N + 1)} (hi : U ≤ chart R N i) :
    baseChange N φ ⁻¹ᵁ U ≤ chart R' N i :=
  fun _ hx => (baseChange_preimage_chart N φ i).le (hi hx)
theorem pull_O1_chart (j : PUnit → Fin (N + 1)) :
    ((O1 R N).pull (baseChange N φ)).U j = chart R' N (j PUnit.unit) :=
  le_antisymm ((LB.wchart_le (O1 R N) (fun _ => baseChange N φ) j PUnit.unit).trans
      (baseChange_preimage_chart N φ _).le)
    fun _ hx => Set.mem_iInter.2 fun _ => (baseChange_preimage_chart N φ _).ge hx
def baseChangeIso : LB.Iso ((O1 R N).pull (baseChange N φ)) (O1 R' N) where
  s p := ratioUnit _ p.1 (p.2 PUnit.unit) inf_le_left (inf_le_right.trans (pull_O1_chart N φ p.2).le)
end BaseChange
example : (coord R 1 1).f (0 : Fin 2) = chartAlgEquiv R 1 0 (X ⟨1, by decide⟩) ∧
    (coord R 1 1).f (1 : Fin 2) = 1 ∧
    ((O1 R 1).g (0 : Fin 2) (1 : Fin 2)).val = resG _ inf_le_left ((coord R 1 1).f (0 : Fin 2)) :=
  ⟨(chartAlgEquiv_X R 1 0 ⟨1, by decide⟩).symm, ratioOn_self (hi := le_rfl), rfl⟩
example [Nontrivial R] : nonzeroLocus (coord R 1 1) ≠ ⊤ := by
  intro h
  rw [nonzeroLocus_coord] at h
  have h1 : (PSpace R 1).basicOpen (ratio R 1 0 1) = chart R 1 0 :=
    basicOpen_ratioOn.trans ((congrArg (_ ⊓ ·) h).trans (inf_top_eq _))
  have h2 : IsUnit (ratio R 1 0 1) := (PSpace R 1).toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx =>
    ((PSpace R 1).mem_basicOpen _ x hx).1 (h1.ge hx)
  rw [← chartAlgEquiv_X R 1 0 ⟨1, by decide⟩] at h2
  have h3 := (h2.map (chartAlgEquiv R 1 0).symm).map constantCoeff
  rw [AlgEquiv.symm_apply_apply, constantCoeff_X] at h3
  exact not_isUnit_zero h3
example (h : (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) R).IsHomogeneous 2) :
    formOn (chart R 2 0) 0 le_rfl 2 (X 0 * X 1 - X 2 ^ 2) h = ratio R 2 0 1 - ratio R 2 0 2 ^ 2 := by
  rw [formOn_eq_aeval]
  simp
end GlobalTheory.ProjSpace


