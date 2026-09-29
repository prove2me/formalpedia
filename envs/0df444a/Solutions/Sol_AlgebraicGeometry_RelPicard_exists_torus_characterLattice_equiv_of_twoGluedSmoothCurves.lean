-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/aaed8790-68c2-5dab-9d29-edbd1835af79

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_one_iso
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_comp_eq_one_iff
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus AlgebraicGeometry.TwoGluedCurves AlgebraicCurve ModularCurve"

p2m_open "CategoryTheory.MonoidalCategory"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective Flat IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.Spec_iff ext_of_apply_closedPoint_eq Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso Scheme.Pullback.exists_preimage_pullback HasRingHomProperty toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusCoordAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

def coordUnit (k : Type u) [Field k] (n : ℕ) (j : Fin n) : (torusCoord k n)ˣ :=
  (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single j 1))

def unitsMonoidHom {ι : Type*} [Fintype ι] {M : Type*} [CommGroup M] (v : ι → M) : Multiplicative (ι → ℤ) →* M where
  toFun a := ∏ j, v j ^ (Multiplicative.toAdd a j)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem unitsMonoidHom_ofAdd {ι : Type*} [Fintype ι] {M : Type*} [CommGroup M] (v : ι → M) (a : ι → ℤ) :
    unitsMonoidHom v (Multiplicative.ofAdd a) = ∏ j, v j ^ a j := rfl

theorem unitsMonoidHom_single {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [CommGroup M] (v : ι → M) (j : ι) :
    unitsMonoidHom v (Multiplicative.ofAdd (Pi.single j 1)) = v j := by
  simp only [unitsMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem prod_zpow_const {ι : Type*} {G : Type*} [CommGroup G] (s : Finset ι) (c : G) (f : ι → ℤ) :
    ∏ i ∈ s, c ^ f i = c ^ ∑ i ∈ s, f i := by
  classical
  exact Finset.induction_on s (by simp) (fun i s hi ih => by rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add])

theorem toHomUnits_of_eq_unitsMonoidHom (k : Type u) [Field k] (n : ℕ) :
    (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits = unitsMonoidHom (coordUnit k n) := by
  classical
  have : MonoidHom.toAdditiveRight (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits =
      MonoidHom.toAdditiveRight (unitsMonoidHom (coordUnit k n)) := by
    refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
    have hx : ∀ (g : (Fin n → ℤ) →+ Additive (torusCoord k n)ˣ), g (Pi.single j x) =
        (g.comp (AddMonoidHom.single (fun _ : Fin n => ℤ) j)) x := fun g => rfl
    rw [hx, hx]
    congr 1
    refine AddMonoidHom.ext_int ?_
    show (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single j 1)) =
      unitsMonoidHom (coordUnit k n) (Multiplicative.ofAdd (Pi.single j 1))
    rw [unitsMonoidHom_single]
    rfl
  exact MonoidHom.toAdditiveRight.injective this

theorem algHom_single_eq_prod (n : ℕ) {A : Type u} [CommRing A] [Algebra k A] (χ : torusCoord k n →ₐ[k] A)
    (v : Fin n → ℤ) :
    χ (AddMonoidAlgebra.single v 1) =
      ((∏ i, Units.map (χ : torusCoord k n →* A) (coordUnit k n i) ^ v i : Aˣ) : A) := by
  have h1 : (AddMonoidAlgebra.single v (1 : k) : torusCoord k n) =
      ((∏ i, coordUnit k n i ^ v i : (torusCoord k n)ˣ) : torusCoord k n) := by
    have h := congrArg (fun f : Multiplicative (Fin n → ℤ) →* (torusCoord k n)ˣ =>
      ((f (Multiplicative.ofAdd v) : (torusCoord k n)ˣ) : torusCoord k n)) (toHomUnits_of_eq_unitsMonoidHom k n)
    simp only [MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply, toAdd_ofAdd, unitsMonoidHom_ofAdd] at h
    exact h
  rw [h1]
  have h2 : (∏ i, Units.map (χ : torusCoord k n →* A) (coordUnit k n i) ^ v i) =
      Units.map (χ : torusCoord k n →* A) (∏ i, coordUnit k n i ^ v i) := by
    rw [map_prod]; simp only [map_zpow]
  rw [h2, Units.coe_map, MonoidHom.coe_coe]

def latticeCoord {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1)) :
    characterLattice ι ≃+ (Fin n → ℤ) where
  toFun a i := -(a : ι → ℤ) (e.symm i.succ)
  invFun v := ⟨fun σ => Fin.cases (∑ i, v i) (fun i => -v i) (e σ), by
    rw [mem_characterLattice, ← e.symm.sum_comp]
    simp only [Equiv.apply_symm_apply, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Finset.sum_neg_distrib,
      add_neg_cancel]⟩
  left_inv a := by
    apply Subtype.ext
    funext σ
    have hsum : (a : ι → ℤ) (e.symm 0) + ∑ i : Fin n, (a : ι → ℤ) (e.symm i.succ) = 0 := by
      have h := mem_characterLattice.mp a.2
      rw [← e.symm.sum_comp, Fin.sum_univ_succ] at h
      exact h
    show Fin.cases (∑ i : Fin n, -(a : ι → ℤ) (e.symm i.succ)) (fun i => -(-(a : ι → ℤ) (e.symm i.succ))) (e σ) = (a : ι → ℤ) σ
    rcases Fin.eq_zero_or_eq_succ (e σ) with h | ⟨i, h⟩
    · have hσ : σ = e.symm 0 := by rw [← h, Equiv.symm_apply_apply]
      rw [h, Fin.cases_zero, hσ, Finset.sum_neg_distrib]
      linarith
    · have hσ : σ = e.symm i.succ := by rw [← h, Equiv.symm_apply_apply]
      rw [h, Fin.cases_succ, neg_neg, hσ]
  right_inv v := by
    funext i
    show -(Fin.cases (∑ i, v i) (fun i => -v i) (e (e.symm i.succ))) = v i
    rw [Equiv.apply_symm_apply, Fin.cases_succ, neg_neg]
  map_add' a b := by
    funext i
    show -((a : ι → ℤ) + (b : ι → ℤ)) (e.symm i.succ) = -(a : ι → ℤ) (e.symm i.succ) + -(b : ι → ℤ) (e.symm i.succ)
    rw [Pi.add_apply, neg_add]

theorem latticeCoord_apply {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1)) (a : characterLattice ι) (i : Fin n) :
    latticeCoord e a i = -(a : ι → ℤ) (e.symm i.succ) := rfl

theorem exists_inv_eq_mul_iff_forall_prod_zpow_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [CommGroup G]
    {n : ℕ} (e : ι ≃ Fin (n + 1)) (w : ι → G) (z : Fin n → G) :
    (∃ c : G, ∀ σ, (w σ)⁻¹ = c * Fin.cases (1 : G) z (e σ)) ↔
      ∀ a : characterLattice ι, ∏ σ, w σ ^ (a : ι → ℤ) σ = ∏ i, z i ^ latticeCoord e a i := by
  constructor
  · rintro ⟨c, hc⟩ a
    have hsum : ∑ σ, (a : ι → ℤ) σ = 0 := mem_characterLattice.mp a.2

    have h1 : (∏ σ, w σ ^ (a : ι → ℤ) σ)⁻¹ = ∏ σ, Fin.cases (1 : G) z (e σ) ^ (a : ι → ℤ) σ := by
      rw [← Finset.prod_inv_distrib]
      simp_rw [← inv_zpow, hc, mul_zpow, Finset.prod_mul_distrib, prod_zpow_const, hsum, zpow_zero, one_mul]
    have h2 : ∏ σ, Fin.cases (1 : G) z (e σ) ^ (a : ι → ℤ) σ = ∏ i, z i ^ (a : ι → ℤ) (e.symm i.succ) := by
      rw [← e.symm.prod_comp]
      simp only [Equiv.apply_symm_apply, Fin.prod_univ_succ, Fin.cases_zero, one_zpow, Fin.cases_succ, one_mul]
    simp only [latticeCoord_apply, zpow_neg, Finset.prod_inv_distrib]
    rw [← h2, ← h1, inv_inv]
  · intro hall
    refine ⟨(w (e.symm 0))⁻¹, fun σ => ?_⟩
    rcases Fin.eq_zero_or_eq_succ (e σ) with h | ⟨i₀, h⟩
    · have hσ : σ = e.symm 0 := by rw [← h, Equiv.symm_apply_apply]
      rw [h, Fin.cases_zero, mul_one, hσ]
    ·
      let a : characterLattice ι := ⟨Pi.single σ 1 - Pi.single (e.symm 0) 1, by
        rw [mem_characterLattice]
        simp [Finset.sum_sub_distrib]⟩
      have ha := hall a
      have hl : ∏ τ, w τ ^ (a : ι → ℤ) τ = w σ / w (e.symm 0) := by
        rw [← unitsMonoidHom_ofAdd]
        show unitsMonoidHom w (Multiplicative.ofAdd (Pi.single σ 1 - Pi.single (e.symm 0) 1)) = _
        rw [ofAdd_sub, map_div, unitsMonoidHom_single, unitsMonoidHom_single]
      have hcoord : (latticeCoord e a : Fin n → ℤ) = -Pi.single i₀ 1 := by
        funext i
        rw [latticeCoord_apply, Pi.neg_apply]
        show -((Pi.single σ 1 - Pi.single (e.symm 0) 1 : ι → ℤ) (e.symm i.succ)) = -((Pi.single i₀ 1 : Fin n → ℤ) i)
        have hne : ¬ (e.symm i.succ = e.symm 0) := fun hh => Fin.succ_ne_zero i (e.symm.injective hh)
        rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply, Pi.single_apply, if_neg hne, sub_zero]
        congr 1
        simp only [Equiv.symm_apply_eq, h, Fin.succ_inj]
      have hr : ∏ i, z i ^ latticeCoord e a i = (z i₀)⁻¹ := by
        rw [← unitsMonoidHom_ofAdd, hcoord, ofAdd_neg, map_inv, unitsMonoidHom_single]
      rw [hl, hr] at ha
      rw [h, Fin.cases_succ]
      calc (w σ)⁻¹ = (w σ / w (e.symm 0) * w (e.symm 0))⁻¹ := by rw [div_mul_cancel]
        _ = ((z i₀)⁻¹ * w (e.symm 0))⁻¹ := by rw [ha]
        _ = (w (e.symm 0))⁻¹ * z i₀ := by rw [mul_inv_rev, inv_inv]

def univU (n : ℕ) : Fin (n + 1) → Γ(torusScheme k n, ⊤)ˣ :=
  Fin.cases 1 (fun i => Units.map (Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv.hom.toMonoidHom (coordUnit k n i))

@[scoped simp] theorem univU_zero (n : ℕ) : univU (k := k) n 0 = 1 := Fin.cases_zero

@[scoped simp] theorem univU_succ (n : ℕ) (i : Fin n) :
    univU (k := k) n i.succ = Units.map (Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv.hom.toMonoidHom (coordUnit k n i) :=
  Fin.cases_succ _

end AlgebraicGeometry.RelPicard.TorusCoordAssembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective Flat IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.Spec_iff ext_of_apply_closedPoint_eq Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso Scheme.Pullback.exists_preimage_pullback HasRingHomProperty toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusCoordAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

def pullbackAlongCompIso {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    {t'' : T'' ⟶ Spec (CommRingCat.of k)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    (M.pullbackAlong (NeronModelInfra.schemeHomOverComp φ ψ)).L ≅ ((M.pullbackAlong ψ).pullbackAlong φ).L :=
  (RigidifiedLineBundle.pullbackAlongPullbackAlongIso' M ψ φ).symm

section restrict

variable {X C₁ : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} {c₁ : C₁ ⟶ Spec (CommRingCat.of k)}
  (i₁ : SchemeHomOver c₁ x)
  {ε : SchemeHomOver (𝟙 _) x} {ε₁ : SchemeHomOver (𝟙 _) c₁} (hε : ε₁.1 ≫ i₁.1 = ε.1)
  {D : RelativePic0Designation k x} (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
  {D₁ : RelativePic0Designation k c₁} (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)

theorem classify_poincare_pullbackAlong {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    hD.classify t (hD.poincare.pullbackAlong a)
      ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem) = a :=
  (hD.classify_unique t _ _ a ⟨Iso.refl _⟩).symm

include hε in

theorem nonempty_poincare_pullbackAlong_comp_pullbackHom_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    Nonempty ((hD₁.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁))).L ≅
      (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hD.poincare.pullbackAlong a).L) := by
  have h1 : NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁) =
      postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
        (hD.classify t (hD.poincare.pullbackAlong a)
          ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem)) := by
    rw [classify_poincare_pullbackAlong]; rfl
  rw [h1, RepresentsRelSubPic.postComp_pullbackHom_classify]
  exact hD₁.classify_spec t _ _

include hε in

theorem comp_pullbackHom_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ↔
      Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hD.poincare.pullbackAlong a).L ≅
        SheafOfModules.unit (pullback c₁ t).ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_poincare_pullbackAlong_comp_pullbackHom_iso i₁ hε hD hD₁ t a
  obtain ⟨e1⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c₁ ε₁) hD₁ t
  constructor
  · intro h
    rw [h] at e
    exact ⟨e.symm ≪≫ e1⟩
  · rintro ⟨f⟩
    exact hD₁.ext_of_iso t _ _ ⟨e ≪≫ f ≪≫ e1.symm⟩

end restrict
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

section restrict₂

variable {X C₂ : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} {c₂ : C₂ ⟶ Spec (CommRingCat.of k)}
  (i₂ : SchemeHomOver c₂ x)
  {ε : SchemeHomOver (𝟙 _) x} {ε₂ : SchemeHomOver (𝟙 _) c₂}
  {D : RelativePic0Designation k x} (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
  {D₂ : RelativePic0Designation k c₂} (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
  (ν₂ : SchemeHomOver D.toBase D₂.toBase)
  (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
        Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

include hν₂ in

theorem comp_ν₂_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp a ν₂ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t ↔
      Nonempty (Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L) ≅
        SheafOfModules.unit (pullback c₂ t).ringCatSheaf) := by
  obtain ⟨e⟩ := hν₂ t a
  obtain ⟨e1⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c₂ ε₂) hD₂ t
  constructor
  · intro h
    rw [h] at e
    exact ⟨e.symm ≪≫ e1⟩
  · rintro ⟨f⟩
    exact hD₂.ext_of_iso t _ _ ⟨e ≪≫ f ≪≫ e1.symm⟩

end restrict₂
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

end AlgebraicGeometry.RelPicard.TorusCoordAssembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective Flat IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.Spec_iff ext_of_apply_closedPoint_eq Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso Scheme.Pullback.exists_preimage_pullback HasRingHomProperty toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusCoordAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

theorem isIntegral_of_geometricallyIntegral {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [GeometricallyIntegral c] : IsIntegral C :=
  haveI : IsIntegral (pullback c (𝟙 (Spec (CommRingCat.of k)))) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c) (𝟙 _) (pullback.fst c (𝟙 _)) (pullback.snd c (𝟙 _))
      (IsPullback.of_hasPullback c (𝟙 _))
  IsIntegral.of_isIso (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))

theorem appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  have := Scheme.ΓSpecIso_inv_naturality φ
  exact (congrArg (fun f => f.hom r) this).symm

theorem exists_eq_torusPtId (n : ℕ) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k n)) :
    ∃ χ : torusCoord k n →ₐ[k] k, y = torusPtId k n χ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective y.1
  have hcomp : (CommRingCat.ofHom (algebraMap k (torusCoord k n))) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_id]
    exact y.2
  refine ⟨{ φ.hom with commutes' := fun r => ?_ }, ?_⟩
  · exact congrArg (fun f => f.hom r) hcomp
  · apply Subtype.ext
    show y.1 = Spec.map _
    rw [← hφ]
    rfl

theorem algHom_ext_coordUnit (n : ℕ) {A : Type u} [CommRing A] [Algebra k A] (χ χ' : torusCoord k n →ₐ[k] A)
    (h : ∀ j : Fin n, χ (coordUnit k n j : torusCoord k n) = χ' (coordUnit k n j : torusCoord k n)) : χ = χ' := by

  let m : Multiplicative (Fin n → ℤ) →* A := (χ : torusCoord k n →* A).comp (AddMonoidAlgebra.of k (Fin n → ℤ))
  let m' : Multiplicative (Fin n → ℤ) →* A := (χ' : torusCoord k n →* A).comp (AddMonoidAlgebra.of k (Fin n → ℤ))
  have hmm : m = m' := by
    have : MonoidHom.toAdditiveRight m = MonoidHom.toAdditiveRight m' := by
      refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
      have hx : ∀ (g : (Fin n → ℤ) →+ Additive A), g (Pi.single j x) =
          (g.comp (AddMonoidHom.single (fun _ : Fin n => ℤ) j)) x := fun g => rfl
      rw [hx, hx]
      congr 1
      refine AddMonoidHom.ext_int ?_
      show m (Multiplicative.ofAdd (Pi.single j 1)) = m' (Multiplicative.ofAdd (Pi.single j 1))
      exact h j
    exact MonoidHom.toAdditiveRight.injective this
  refine AddMonoidAlgebra.algHom_ext (φ₁ := χ) (φ₂ := χ') (fun v => ?_) (Subsingleton.elim _ _)
  have := congrArg (fun f => f (Multiplicative.ofAdd v)) hmm
  simpa [m, m', AddMonoidAlgebra.of_apply] using this

theorem torusPt_ext (n : ℕ) (y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k n))
    (h : ∀ j : Fin n,
      y.1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n)) =
        y'.1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n))) :
    y = y' := by
  obtain ⟨χ, rfl⟩ := exists_eq_torusPtId n y
  obtain ⟨χ', rfl⟩ := exists_eq_torusPtId n y'
  have hχ : χ = χ' := by
    refine algHom_ext_coordUnit n χ χ' fun j => ?_
    have := h j
    change (Spec.map (CommRingCat.ofHom χ.toRingHom)).appTop _ =
      (Spec.map (CommRingCat.ofHom χ'.toRingHom)).appTop _ at this
    rw [appTop_ΓSpecIso_inv, appTop_ΓSpecIso_inv] at this
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective this
  rw [hχ]

end AlgebraicGeometry.RelPicard.TorusCoordAssembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective Flat IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.Spec_iff ext_of_apply_closedPoint_eq Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso Scheme.Pullback.exists_preimage_pullback HasRingHomProperty toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusCoordAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

theorem exists_torusPt_of_units (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (v : Fin n → Γ(T, ⊤)ˣ) :
    ∃ y : SchemeHomOver t (torusStr k n), ∀ j : Fin n,
      y.1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv
        ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n)) = (v j : Γ(T, ⊤)) := by
  classical
  letI : Algebra k Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom.toAlgebra
  have halg : algebraMap k Γ(T, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom := rfl
  let m : Multiplicative (Fin n → ℤ) →* Γ(T, ⊤) := (Units.coeHom _).comp (unitsMonoidHom v)
  let φ : torusCoord k n →ₐ[k] Γ(T, ⊤) := AddMonoidAlgebra.lift k Γ(T, ⊤) (Fin n → ℤ) m
  refine ⟨⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩, fun j => ?_⟩
  · change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (torusCoord k n))) = t
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.toRingHom.comp (algebraMap k (torusCoord k n)) = algebraMap k Γ(T, ⊤) := φ.comp_algebraMap
    rw [this, halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop _ = _
    rw [Scheme.Hom.comp_appTop]
    change T.toSpecΓ.appTop ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop _) = _
    rw [appTop_ΓSpecIso_inv, Scheme.toSpecΓ_appTop]
    change ((Scheme.ΓSpecIso Γ(T, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(T, ⊤)).hom) (φ _) = _
    rw [Iso.inv_hom_id]
    change φ (coordUnit k n j : torusCoord k n) = _
    simp only [coordUnit, MonoidHom.coe_toHomUnits, φ, AddMonoidAlgebra.lift_of, m, MonoidHom.coe_comp,
      Function.comp_apply, unitsMonoidHom_single, Units.coeHom_apply]

theorem conv_single {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] {M : Type} [AddCommMonoid M]
    (χ ψ : WithConv (AddMonoidAlgebra S M →ₐ[S] T)) (g : M) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
      χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

theorem appTop_torusPtId_coordUnit (n : ℕ) (χ : torusCoord k n →ₐ[k] k) (j : Fin n) :
    (torusPtId k n χ).1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv
        ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv (χ (coordUnit k n j : torusCoord k n)) := by
  change (Spec.map (CommRingCat.ofHom χ.toRingHom)).appTop _ = _
  rw [appTop_ΓSpecIso_inv]
  rfl

end AlgebraicGeometry.RelPicard.TorusCoordAssembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard.TorusCoordAssembly"

open AlgebraicGeometry.RelPicard.TorusCoordAssembly in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (S : Finset (Place k F × Place k F)) (hS : S.card = s)
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (Φ : GluedPic0 k F S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)

    (hadd : ∀ a b, Φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (Φ a) (Φ b))

    (hnode : ∀ w : ↥S → Additive kˣ,
      IsNodeUnitModule x i₁ i₂
        (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
        (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
        (𝟙 (Spec (CommRingCat.of k)))
        (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
        (hD.poincare.pullbackAlong (Φ (GluedPic0.nodeUnit S w))).L)

    (hΦker : ∀ g : GluedPic0 k F S,
      (NeronModelInfra.schemeHomOverComp (Φ g) ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one _ ∧
        NeronModelInfra.schemeHomOverComp (Φ g) ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one _) ↔
        g ∈ (GluedPic0.nodeUnit S).range) :
    ∃ (τ : SchemeHomOver (torusStr k (s - 1)) D.toBase) (B : characterLattice ↥S ≃+ (Fin (s - 1) → ℤ)),
      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord k (s - 1) →ₐ[k] k),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) (χ * χ').ofConv) τ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ'.ofConv) τ)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a) ∧

      (∀ (χ : torusCoord k (s - 1) →ₐ[k] k) (w : ↥S → Additive kˣ),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ) τ = Φ (GluedPic0.nodeUnit S w) ↔
          ∀ a : characterLattice ↥S,
            ((∏ σ, Additive.toMul (w σ) ^ (a : ↥S → ℤ) σ : kˣ) : k) = χ (AddMonoidAlgebra.single (B a) 1)) := by
  classical
  haveI : IsReduced X := hXred
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩

  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  let zc : pullback i₁.1 i₂.1 ⟶ Spec (CommRingCat.of k) := pullback.fst i₁.1 i₂.1 ≫ c₁
  haveI : LocallyOfFiniteType zc := inferInstance
  let p₁ : ↥S → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁ := fun σ =>
    ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩
  let p₂ : ↥S → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂ := fun σ =>
    ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩
  have hndinj : Function.Injective fun σ : ↥S => (nd σ).1.base (IsLocalRing.closedPoint k) := by
    intro σ σ' h
    apply nd.injective
    exact Subtype.ext (ext_of_apply_closedPoint_eq zc (nd σ).2 (nd σ').2 h)
  have hinj : Function.Injective fun σ : ↥S => (p₁ σ).1.base (IsLocalRing.closedPoint k) := by
    intro σ σ' h
    have hinjf := (pullback.fst i₁.1 i₂.1).isClosedEmbedding.injective
    change (pullback.fst i₁.1 i₂.1).base ((nd σ).1.base (IsLocalRing.closedPoint k)) =
      (pullback.fst i₁.1 i₂.1).base ((nd σ').1.base (IsLocalRing.closedPoint k)) at h
    exact hndinj (hinjf h)
  have hpn : ∀ σ, (p₁ σ).1 ≫ i₁.1 = (p₂ σ).1 ≫ i₂.1 := fun σ => by
    change ((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ i₁.1 = ((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ i₂.1
    simp only [Category.assoc, pullback.condition]
  have hScard' : Fintype.card ↥S = n + 1 := by rw [Fintype.card_coe, hS]
  have hScard : Nat.card ↥S = n + 1 := by rw [Nat.card_eq_fintype_card, hScard']
  have hndsurj : Function.Surjective fun σ : ↥S => (nd σ).1.base (IsLocalRing.closedPoint k) :=
    (hndinj.bijective_of_nat_card_le (by rw [hs, hScard])).2
  have hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ σ, q₁ = (p₁ σ).1.base (IsLocalRing.closedPoint k) ∧ q₂ = (p₂ σ).1.base (IsLocalRing.closedPoint k) := by
    intro q₁ q₂ hq
    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁.1) (g := i₂.1) q₁ q₂ hq
    obtain ⟨σ, hσ⟩ := hndsurj t
    have hσ' : (nd σ).1.base (IsLocalRing.closedPoint k) = t := hσ
    refine ⟨σ, ?_, ?_⟩
    · change q₁ = (pullback.fst i₁.1 i₂.1).base ((nd σ).1.base (IsLocalRing.closedPoint k))
      rw [hσ', ht1]
    · change q₂ = (pullback.snd i₁.1 i₂.1).base ((nd σ).1.base (IsLocalRing.closedPoint k))
      rw [hσ', ht2]

  let e₀ : ↥S ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hScard'
  let U : ↥S → Γ(torusScheme k n, ⊤)ˣ := fun σ => univU n (e₀ σ)
  have hU : ∀ σ, U σ = univU n (e₀ σ) := fun σ => rfl
  obtain ⟨MU, hMUinv, hMU⟩ := exists_isInvertible_isNodeUnitModule k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr
    (torusStr k n) U
  obtain ⟨⟨eU₁⟩, ⟨eU₂⟩⟩ := IsNodeUnitModule.nonempty_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj hpn
    hinter hcr hMUinv hMU

  let PU : RigidifiedLineBundle x ε (torusStr k n) :=
    { L := MU
      isInvertible := hMUinv
      rigidified := ⟨(Scheme.Modules.pullbackCongr (rigSection_curveChange i₁.1 i₁.2 hε _).symm).app MU ≪≫
        ((Scheme.Modules.pullbackComp _ _).app MU).symm ≪≫
        (Scheme.Modules.pullback _).mapIso eU₁ ≪≫ Scheme.Modules.pullbackUnitIso _⟩ }
  have hPU : FibrewiseAlgEquivZero PU :=
    IsNodeUnitModule.fibrewiseAlgEquivZero k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr ε PU hMU
  let τ : SchemeHomOver (torusStr k n) D.toBase := hD.classify _ PU hPU
  have hτ : Nonempty ((hD.poincare.pullbackAlong τ).L ≅ MU) := hD.classify_spec _ PU hPU

  have hPy : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t (torusStr k n)),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp y τ)).L ≅
        (Scheme.Modules.pullback (baseChangeSnd x y)).obj MU) := fun y =>
    ⟨pullbackAlongCompIso hD.poincare τ y ≪≫ (Scheme.Modules.pullback _).mapIso hτ.some⟩

  have hhom : ∀ χ χ' : WithConv (torusCoord k n →ₐ[k] k),
      NeronModelInfra.schemeHomOverComp (torusPtId k n (χ * χ').ofConv) τ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId k n χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId k n χ'.ofConv) τ) := by
    intro χ χ'
    apply hD.ext_of_iso (𝟙 _)
    obtain ⟨eL⟩ := hPy (torusPtId k n (χ * χ').ofConv)
    obtain ⟨eχ⟩ := hPy (torusPtId k n χ.ofConv)
    obtain ⟨eχ'⟩ := hPy (torusPtId k n χ'.ofConv)
    obtain ⟨em⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso (P := algEquivZeroGroupCut x ε) hD (𝟙 _)
      (NeronModelInfra.schemeHomOverComp (torusPtId k n χ.ofConv) τ)
      (NeronModelInfra.schemeHomOverComp (torusPtId k n χ'.ofConv) τ)
    have hNχ := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU
      (torusPtId k n χ.ofConv)
    have hNχ' := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU
      (torusPtId k n χ'.ofConv)
    have hNχχ' := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU
      (torusPtId k n (χ * χ').ofConv)
    have hT := IsNodeUnitModule.tensor k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr (hMUinv.pullback _) hNχ
      (hMUinv.pullback _) hNχ'
    have hunits : (fun σ => Units.map (torusPtId k n (χ * χ').ofConv).1.appTop.hom.toMonoidHom (U σ)) =
        (fun σ => Units.map (torusPtId k n χ.ofConv).1.appTop.hom.toMonoidHom (U σ)) *
        (fun σ => Units.map (torusPtId k n χ'.ofConv).1.appTop.hom.toMonoidHom (U σ)) := by
      funext σ
      rcases Fin.eq_zero_or_eq_succ (e₀ σ) with hj | ⟨i, hj⟩
      · simp [hU, hj]
      · apply Units.ext
        simp only [hU, hj, univU_succ, Pi.mul_apply, Units.val_mul, Units.coe_map,
          RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
        rw [appTop_torusPtId_coordUnit, appTop_torusPtId_coordUnit, appTop_torusPtId_coordUnit, ← map_mul]
        congr 1
        exact conv_single χ χ' _
    rw [hunits] at hNχχ'
    obtain ⟨ee⟩ := IsNodeUnitModule.nonempty_iso hNχχ' hT
    exact ⟨eL ≪≫ ee ≪≫ (eχ.symm ⊗ᵢ eχ'.symm) ≪≫ em.symm⟩

  let σ₀ : ↥S := e₀.symm 0
  have he₀σ₀ : e₀ σ₀ = 0 := e₀.apply_symm_apply 0
  have hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
      (NeronModelInfra.schemeHomOverComp a ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
        NeronModelInfra.schemeHomOverComp a ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
      ∃ y : SchemeHomOver t (torusStr k n), NeronModelInfra.schemeHomOverComp y τ = a := by
    intro T t a
    constructor
    · rintro ⟨h1, h2⟩
      rw [hν₁, comp_pullbackHom_eq_one_iff i₁ hε hD hD₁ t] at h1
      obtain ⟨f₁⟩ := h1
      rw [comp_ν₂_eq_one_iff i₂ hD hD₂ ν₂ hν₂ t] at h2
      obtain ⟨g₂⟩ := h2
      have hPinv : Scheme.Modules.IsInvertible (hD.poincare.pullbackAlong a).L := (hD.poincare.pullbackAlong a).isInvertible

      obtain ⟨r⟩ := Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit
        (rigSection c₂ t ε₂) (pullback.snd c₂ t) (hPinv.pullback (curveChange i₂.1 i₂.2 t)) ⟨g₂⟩

      have n12 : nodeSectionFst p₁ t σ₀ ≫ curveChange i₁.1 i₁.2 t =
          nodeSectionSnd p₂ t σ₀ ≫ curveChange i₂.1 i₂.2 t := by
        simp only [nodeSectionFst, nodeSectionSnd]
        rw [rigSection_curveChange i₁.1 i₁.2 (ε := ⟨(p₁ σ₀).1 ≫ i₁.1, by
              rw [Category.assoc, i₁.2]; exact (p₁ σ₀).2⟩) rfl,
          rigSection_curveChange i₂.1 i₂.2 (ε := ⟨(p₁ σ₀).1 ≫ i₁.1, by
              rw [Category.assoc, i₁.2]; exact (p₁ σ₀).2⟩) (hpn σ₀).symm]
      have hN : Nonempty ((Scheme.Modules.pullback (rigSection c₂ t ε₂)).obj
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L) ≅
            SheafOfModules.unit T.ringCatSheaf) := by
        have s₂ : nodeSectionSnd p₂ t σ₀ ≫ pullback.snd c₂ t = 𝟙 T := rigSection_snd _ _
        refine ⟨?_⟩
        refine ((Scheme.Modules.pullbackId _).app _).symm ≪≫ (Scheme.Modules.pullbackCongr s₂.symm).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
          ((Scheme.Modules.pullback (nodeSectionSnd p₂ t σ₀)).mapIso r).symm ≪≫
          (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr n12.symm).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
          (Scheme.Modules.pullback (nodeSectionFst p₁ t σ₀)).mapIso f₁ ≪≫ Scheme.Modules.pullbackUnitIso _
      have f₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L ≅
          SheafOfModules.unit (pullback c₂ t).ringCatSheaf :=
        r ≪≫ (Scheme.Modules.pullback _).mapIso hN.some ≪≫ Scheme.Modules.pullbackUnitIso _

      obtain ⟨u, hu⟩ := exists_isNodeUnitModule_of_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj hpn
        hinter hcr t _ hPinv ⟨f₁⟩ ⟨f₂⟩
      have hu' := IsNodeUnitModule.smul_units hu (u σ₀)⁻¹
      obtain ⟨y, hy⟩ := exists_torusPt_of_units n t (fun i => (u σ₀)⁻¹ * u (e₀.symm i.succ))
      refine ⟨y, hD.ext_of_iso t _ _ ?_⟩
      obtain ⟨e⟩ := hPy y
      have hN4 := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU y
      have huy : (fun σ => Units.map y.1.appTop.hom.toMonoidHom (U σ)) = fun σ => (u σ₀)⁻¹ * u σ := by
        funext σ
        rcases Fin.eq_zero_or_eq_succ (e₀ σ) with hj | ⟨i, hj⟩
        · have hσ : σ = σ₀ := e₀.injective (hj.trans he₀σ₀.symm)
          rw [hσ]
          simp [hU, he₀σ₀]
        · apply Units.ext
          have := hy i
          have hσ : e₀.symm i.succ = σ := by rw [← hj, Equiv.symm_apply_apply]
          rw [hσ] at this
          simp only [hU, hj, univU_succ] at this ⊢
          exact this
      rw [huy] at hN4
      obtain ⟨ee⟩ := IsNodeUnitModule.nonempty_iso hN4 hu'
      exact ⟨e ≪≫ ee⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨e⟩ := hPy y
      have hN := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU y
      obtain ⟨⟨f₁⟩, ⟨f₂⟩⟩ := IsNodeUnitModule.nonempty_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj
        hpn hinter hcr (hMUinv.pullback _) hN
      constructor
      · rw [hν₁, comp_pullbackHom_eq_one_iff i₁ hε hD hD₁ t]
        exact ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ f₁⟩
      · rw [comp_ν₂_eq_one_iff i₂ hD hD₂ ν₂ hν₂ t]
        obtain ⟨ru⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
          (RigidifiedLineBundle.unit (c := c₂) (ε := ε₂) t)
        exact ⟨Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso e ≪≫ f₂) ≪≫ ru⟩

  have hτinj : ∀ y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k n),
      NeronModelInfra.schemeHomOverComp y τ = NeronModelInfra.schemeHomOverComp y' τ → y = y' := by
    intro y y' hyy
    haveI : IsIntegral C₁ := isIntegral_of_geometricallyIntegral c₁
    haveI : IsIntegral C₂ := isIntegral_of_geometricallyIntegral c₂
    have hiso : Nonempty ((Scheme.Modules.pullback (baseChangeSnd x y)).obj MU ≅
        (Scheme.Modules.pullback (baseChangeSnd x y')).obj MU) := by
      obtain ⟨e⟩ := hPy y
      obtain ⟨e'⟩ := hPy y'
      rw [hyy] at e
      exact ⟨e.symm ≪≫ e'⟩
    have hN := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU y
    have hN' := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU y'
    obtain ⟨c, hc'⟩ := IsNodeUnitModule.exists_eq_mul_of_iso k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr
      (hMUinv.pullback _) (hMUinv.pullback _) hN hN' hiso
    have hc0 := hc' σ₀
    simp only [hU, he₀σ₀, univU_zero, map_one] at hc0
    have hc1 : c = 1 := by simpa using hc0.symm
    subst hc1
    refine torusPt_ext n y y' fun j => ?_
    have hj := hc' (e₀.symm j.succ)
    simp only [hU, Equiv.apply_symm_apply, univU_succ, one_mul] at hj
    exact (congrArg Units.val hj).symm

  have hci : IsClosedImmersion τ.1 := by
    obtain ⟨K, j, hj, hK⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_comp_eq_one_iff
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁)
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂) ν₁ ν₂
    haveI := hj
    haveI : IsDomain (torusCoord k n) := inferInstance
    haveI : IsReduced (torusScheme k n) := inferInstance
    haveI : IsSeparated (torusStr k n) := inferInstance
    haveI : LocallyOfFiniteType (torusStr k n) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show RingHom.FiniteType (algebraMap k (torusCoord k n))
      rw [RingHom.finiteType_algebraMap]
      haveI : AddMonoid.FG (Fin n → ℤ) := by
        rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance
      infer_instance
    haveI : Flat (torusStr k n) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      show RingHom.Flat (algebraMap k (torusCoord k n))
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    exact AlgebraicGeometry.SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective
      (torusStr k n) D.toBase τ j (fun t a => (hK t a).symm.trans (hker t a)) hτinj

  have hcoords : ∀ (χ : torusCoord k n →ₐ[k] k) (w : ↥S → Additive kˣ),
      NeronModelInfra.schemeHomOverComp (torusPtId k n χ) τ = Φ (GluedPic0.nodeUnit S w) ↔
        ∀ a : characterLattice ↥S,
          ((∏ σ, Additive.toMul (w σ) ^ (a : ↥S → ℤ) σ : kˣ) : k) = χ (AddMonoidAlgebra.single (latticeCoord e₀ a) 1) := by
    intro χ w
    haveI : IsIntegral C₁ := isIntegral_of_geometricallyIntegral c₁
    haveI : IsIntegral C₂ := isIntegral_of_geometricallyIntegral c₂

    let zχ : Fin n → kˣ := fun i => Units.map (χ : torusCoord k n →* k) (coordUnit k n i)
    let Γe : kˣ ≃* Γ(Spec (CommRingCat.of k), ⊤)ˣ :=
      Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.toMulEquiv
    have hΓe : ∀ v : kˣ, Γe v = Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom v :=
      fun v => Units.ext rfl
    have halg : (∀ a : characterLattice ↥S,
          ((∏ σ, Additive.toMul (w σ) ^ (a : ↥S → ℤ) σ : kˣ) : k) = χ (AddMonoidAlgebra.single (latticeCoord e₀ a) 1)) ↔
        ∃ c : kˣ, ∀ σ, (Additive.toMul (w σ))⁻¹ = c * Fin.cases (1 : kˣ) zχ (e₀ σ) := by
      rw [exists_inv_eq_mul_iff_forall_prod_zpow_eq e₀ (fun σ => Additive.toMul (w σ)) zχ]
      refine forall_congr' fun a => ?_
      rw [algHom_single_eq_prod, Units.val_injective.eq_iff]

    have hNχ := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr hMUinv hMU
      (torusPtId k n χ)
    have hUχ : (fun σ => Units.map (torusPtId k n χ).1.appTop.hom.toMonoidHom (U σ)) =
        fun σ => Γe (Fin.cases (1 : kˣ) zχ (e₀ σ)) := by
      funext σ
      rcases Fin.eq_zero_or_eq_succ (e₀ σ) with hj | ⟨i, hj⟩
      · simp [hU, hj]
      · apply Units.ext
        rw [hΓe]
        simp only [hU, hj, univU_succ, Fin.cases_succ, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
        rw [appTop_torusPtId_coordUnit]
        rfl
    rw [hUχ] at hNχ
    obtain ⟨eχ⟩ := hPy (torusPtId k n χ)
    rw [halg]
    constructor
    · intro hEq
      have hiso : Nonempty ((Scheme.Modules.pullback (baseChangeSnd x (torusPtId k n χ))).obj MU ≅
          (hD.poincare.pullbackAlong (Φ (GluedPic0.nodeUnit S w))).L) := by
        rw [← hEq]
        exact ⟨eχ.symm⟩
      obtain ⟨c', hc'⟩ := IsNodeUnitModule.exists_eq_mul_of_iso k x i₁ i₂ hjs p₁ p₂ hinj hpn hinter hcr
        (hMUinv.pullback _) (hD.poincare.pullbackAlong (Φ (GluedPic0.nodeUnit S w))).isInvertible hNχ (hnode w) hiso
      obtain ⟨c, rfl⟩ := Γe.surjective c'
      refine ⟨c, fun σ => Γe.injective ?_⟩
      rw [map_mul, ← hc' σ, hΓe]
    · rintro ⟨c, hc⟩
      have hu' := IsNodeUnitModule.smul_units hNχ (Γe c)
      have hEqU : (fun σ => Γe c * Γe (Fin.cases (1 : kˣ) zχ (e₀ σ))) =
          fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹ :=
        funext fun σ => by rw [← map_mul, ← hc σ, hΓe]
      rw [hEqU] at hu'
      obtain ⟨ee⟩ := IsNodeUnitModule.nonempty_iso hu' (hnode w)
      exact hD.ext_of_iso (𝟙 _) _ _ ⟨eχ ≪≫ ee⟩
  exact ⟨τ, latticeCoord e₀, hci, hhom, hker, hcoords⟩

end S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves (solution)
