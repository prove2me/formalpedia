-- Prove2me | solution 1 for AutomorphicForm.isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8d1ddcf4-74d1-5a17-928b-07b144ab1c76

import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm FLT.SmoothVectors

noncomputable section

namespace P2mS28CA

variable (F : Type) [Field F] [NumberField F]

theorem det_unipotentGL2 (q : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 q) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  ring

theorem chiDet_unipotent_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (q : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (unipotentGL2 q * g) = chiDet (𝓞 F) F η g := by
  show ((η (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) : ℂˣ) : ℂ) = _
  rw [map_mul, det_unipotentGL2, one_mul]
  rfl

theorem isCuspidalFn_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {nS : MeasurableSpace (AdeleRing (𝓞 F) F)} (ν : Measure (AdeleRing (𝓞 F) F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : @IsCuspidalFn _ nS _ _ ν unipotentGL2 φ) :
    @IsCuspidalFn _ nS _ _ ν unipotentGL2 (fnTwist F η φ) := by
  intro g
  have hpt : ∀ q : AdeleRing (𝓞 F) F,
      constantTermIntegrand unipotentGL2 (fnTwist F η φ) g q
        = chiDet (𝓞 F) F η g * constantTermIntegrand unipotentGL2 φ g q := by
    intro q
    unfold constantTermIntegrand
    show chiDet (𝓞 F) F η (unipotentGL2 q * g) * φ (unipotentGL2 q * g) = _
    rw [chiDet_unipotent_mul]
  unfold constantTerm
  calc ∫ q, constantTermIntegrand unipotentGL2 (fnTwist F η φ) g q ∂ν
      = ∫ q, chiDet (𝓞 F) F η g * constantTermIntegrand unipotentGL2 φ g q ∂ν := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = chiDet (𝓞 F) F η g * ∫ q, constantTermIntegrand unipotentGL2 φ g q ∂ν :=
        integral_const_mul _ _
    _ = 0 := by rw [show (∫ q, constantTermIntegrand unipotentGL2 φ g q ∂ν) = 0 from hφ g, mul_zero]

theorem continuous_chiDet {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hcont : Continuous η) :
    Continuous (chiDet (𝓞 F) F η) :=
  Units.continuous_val.comp (hcont.comp Matrix.GeneralLinearGroup.continuous_det)

theorem isOpen_ker_of_isOfFinOrder {G : Type*} [Group G] [TopologicalSpace G] (η : G →* ℂˣ)
    (hc : Continuous η) (ho : IsOfFinOrder η) : IsOpen (η.ker : Set G) := by
  obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho

  set R : Set ℂˣ := {z | (z : ℂ) ∈ Polynomial.nthRoots n (1 : ℂ)} with hR
  have hRfin : R.Finite :=
    Set.Finite.preimage (Units.val_injective.injOn) (Polynomial.nthRoots n (1 : ℂ)).finite_toSet
  have hval : ∀ x, η x ∈ R := fun x => by
    rw [hR, Set.mem_setOf_eq, Polynomial.mem_nthRoots hn, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hηn,
      MonoidHom.one_apply, Units.val_one]
  have hfin : Set.Finite (R \ {1}) := hRfin.subset Set.diff_subset
  have hcompl : (η.ker : Set G)ᶜ = η ⁻¹' (R \ {1}) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_diff,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨hval x, h⟩, fun h => h.2⟩
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.isClosed).preimage hc

theorem isKfSmooth_chiDet {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hc : Continuous η) (ho : IsOfFinOrder η) :
    IsKfSmooth F (chiDet (𝓞 F) F η) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(η.comp Matrix.GeneralLinearGroup.det).ker.comap (finiteAdelicGL2Subgroup F).subtype, ?_, fun u hu => ?_⟩
  · have hopen := isOpen_ker_of_isOfFinOrder
      (η.comp (Matrix.GeneralLinearGroup.det : AdelicGL2 (𝓞 F) F →* (AdeleRing (𝓞 F) F)ˣ))
      (hc.comp Matrix.GeneralLinearGroup.continuous_det) (by
        obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho
        refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, ?_⟩
        ext x
        rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hηn, MonoidHom.one_apply,
          MonoidHom.one_apply])
    exact hopen.preimage continuous_subtype_val
  · refine RightTranslationFn.ext fun g => ?_
    rw [Subgroup.smul_def, RightTranslationFn.toFun_smul]
    show chiDet (𝓞 F) F η (g * (u : AdelicGL2 (𝓞 F) F)) = chiDet (𝓞 F) F η g
    have hu' : η (Matrix.GeneralLinearGroup.det (u : AdelicGL2 (𝓞 F) F)) = 1 :=
      Subgroup.mem_comap.mp hu
    unfold chiDet
    rw [map_mul, map_mul, hu', mul_one]

theorem norm_chiDet_eq_one {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (ho : IsOfFinOrder η) (g : AdelicGL2 (𝓞 F) F) :
    ‖chiDet (𝓞 F) F η g‖ = 1 := by
  obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho
  have h : (chiDet (𝓞 F) F η g) ^ n = 1 := by
    unfold chiDet
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hηn, MonoidHom.one_apply, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h hn.ne'

end P2mS28CA

end

open P2mS28CA in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η) (fnTwist F η φ) := by
  obtain ⟨⟨haut, hcusp⟩, hkf⟩ := hφ
  refine ⟨⟨?_, ?_⟩, isKfSmooth_fnTwist F η (isKfSmooth_chiDet F hη.continuous hη.isOfFinOrder) hkf⟩
  ·
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := (productionPinsOf F D U gen B).mS
    haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
    have h := (lsXiMemberAt_iff (𝓞 F) F (productionPinsOf F D U gen B).μ (productionPinsOf F D U gen B).Z ξ
      (productionPinsOf F D U gen B).D φ).mp haut
    refine (lsXiMemberAt_iff (𝓞 F) F (productionPinsOf F D U gen B).μ (productionPinsOf F D U gen B).Z _
      (productionPinsOf F D U gen B).D (fnTwist F η φ)).mpr ⟨isLsXiFunction_fnTwist F η hη.isIdeleClassChar h.1, ?_⟩
    refine MemLp.of_le h.2 ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((continuous_chiDet F hη.continuous).aestronglyMeasurable).mul h.2.aestronglyMeasurable
    · rw [fnTwist_apply, norm_mul, norm_chiDet_eq_one F hη.isOfFinOrder, one_mul]
  · exact isCuspidalFn_fnTwist F η _ hcusp

end S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf
end P2MW
export P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf (solution)
