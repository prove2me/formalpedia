-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_crossSections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/08d6a378-95f1-54aa-89be-4becc570f086

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Theorems.Thm_AlgebraicGeometry_RelPicard_existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover

noncomputable section

namespace CoverCross

section Thick

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (A : Type u) [CommRing A] [Algebra R A]

abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

abbrev XD : Scheme.{u} := Limits.pullback c (specMap R (DualNumber A))

abbrev σ : XD c A ⟶ XA c A :=
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A)))

variable {c A}

abbrev ι {U : (XA c A).Opens} {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U') : Γ(XA c A, U) →+* Γ(XD c A, U') :=
  ((σ c A).appLE U U' h.ge).hom

private def _root_.CoverCross.eps (U' : (XD c A).Opens) : Γ(XD c A, U') :=
  letI := algebraOfHom (pullback.snd c (specMap R (DualNumber A))) U'
  algebraMap (DualNumber A) Γ(XD c A, U') DualNumber.eps

p2m_export "CoverCross" "eps"
private theorem _root_.CoverCross.eps_mul_eps (U' : (XD c A).Opens) : eps (c := c) (A := A) U' * eps U' = 0 := by
  letI := algebraOfHom (pullback.snd c (specMap R (DualNumber A))) U'
  change algebraMap (DualNumber A) Γ(XD c A, U') DualNumber.eps * algebraMap (DualNumber A) _ DualNumber.eps = 0
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

p2m_export "CoverCross" "eps_mul_eps"

theorem map_eps {U' V' : (XD c A).Opens} (hV : V' ≤ U') :
    ((XD c A).presheaf.map (homOfLE hV).op).hom (eps U') = eps V' := by
  letI := algebraOfHom (pullback.snd c (specMap R (DualNumber A))) U'
  letI := algebraOfHom (pullback.snd c (specMap R (DualNumber A))) V'
  exact (restrictAlgHom (pullback.snd c (specMap R (DualNumber A))) hV).commutes DualNumber.eps

theorem map_ι {U V : (XA c A).Opens} {U' V' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U') (hV : σ c A ⁻¹ᵁ V = V')
    (hVU : V ≤ U) (hVU' : V' ≤ U') (a : Γ(XA c A, U)) :
    ((XD c A).presheaf.map (homOfLE hVU').op).hom (ι hU a) = ι hV (((XA c A).presheaf.map (homOfLE hVU).op).hom a) := by
  change ((σ c A).appLE U U' hU.ge ≫ (XD c A).presheaf.map (homOfLE hVU').op).hom a =
    ((XA c A).presheaf.map (homOfLE hVU).op ≫ (σ c A).appLE V V' hV.ge).hom a
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem mul_split {U : (XA c A).Opens} {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U') (x y x' y' : Γ(XA c A, U)) :
    (ι h x + eps U' * ι h y) * (ι h x' + eps U' * ι h y') =
      ι h (x * x') + eps U' * ι h (x * y' + x' * y) := by
  have he := eps_mul_eps (c := c) (A := A) U'
  simp only [map_mul, map_add]
  linear_combination (ι h y * ι h y') * he

def cst {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    (u : Γ(XD c A, U')) : Γ(XA c A, U) :=
  (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h u).choose.1

def lin {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    (u : Γ(XD c A, U')) : Γ(XA c A, U) :=
  (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h u).choose.2

theorem split_eq {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    (u : Γ(XD c A, U')) : u = ι h (cst hUa h u) + eps U' * ι h (lin hUa h u) :=
  (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h u).choose_spec.1

theorem split_unique {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    {a b a' b' : Γ(XA c A, U)} (e : ι h a + eps U' * ι h b = ι h a' + eps U' * ι h b') : a = a' ∧ b = b' := by
  have H := (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h
    (ι h a + eps U' * ι h b)).unique (y₁ := (a, b)) (y₂ := (a', b')) rfl e
  exact ⟨congrArg Prod.fst H, congrArg Prod.snd H⟩

end Thick

end CoverCross

namespace CoverCross

section Frames

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_map {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h2).op (M.presheaf.map (homOfLE h1).op s) =
      M.presheaf.map (homOfLE (h2.trans h1)).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

theorem map_map_ring {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (r : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom r) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom r := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem map_homOfLE_refl {U : X.Opens} (s : Γ(M, U)) : M.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, M.presheaf.map_id]
  rfl

theorem restrict_smul_eq {U U' W T : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U') (hTW : T ≤ W)
    {s : Γ(M, U)} {t : Γ(M, U')} {u : Γ(X, W)}
    (h : u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU').op t) :
    (X.presheaf.map (homOfLE hTW).op).hom u • M.presheaf.map (homOfLE (hTW.trans hWU)).op s =
      M.presheaf.map (homOfLE (hTW.trans hWU')).op t := by
  have := congrArg (M.presheaf.map (homOfLE hTW).op) h
  rw [Scheme.Modules.map_smul, map_map, map_map] at this
  exact this

theorem exists_units_of_isFrameOn {U U' W : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U')
    {s : Γ(M, U)} {s' : Γ(M, U')} (hs : Scheme.Modules.IsFrameOn s U) (hs' : Scheme.Modules.IsFrameOn s' U') :
    ∃ v w : Γ(X, W), v • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU').op s' ∧
      w • M.presheaf.map (homOfLE hWU').op s' = M.presheaf.map (homOfLE hWU).op s ∧ v * w = 1 := by
  obtain ⟨v, hv⟩ := (hs hWU hWU).2 (M.presheaf.map (homOfLE hWU').op s')
  obtain ⟨w, hw⟩ := (hs' hWU' hWU').2 (M.presheaf.map (homOfLE hWU).op s)
  beta_reduce at hv hw
  refine ⟨v, w, hv, hw, ?_⟩
  apply (hs hWU hWU).1
  change (v * w) • M.presheaf.map (homOfLE hWU).op s = (1 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s
  rw [one_smul, mul_comm, mul_smul, hv, hw]

theorem cross_identity {P0 P1 Q : X.Opens} {e0 : Γ(M, P0)} {e1 : Γ(M, P1)} {e' : Γ(M, Q)}
    (hF0 : Scheme.Modules.IsFrameOn e0 P0) (g : Γ(X, P0 ⊓ P1))
    (hg : M.presheaf.map (homOfLE inf_le_right).op e1 = g • M.presheaf.map (homOfLE inf_le_left).op e0)
    (u0 : Γ(X, P0 ⊓ Q))
    (hu0 : u0 • M.presheaf.map (homOfLE inf_le_left).op e0 = M.presheaf.map (homOfLE inf_le_right).op e')
    (u1 : Γ(X, P1 ⊓ Q))
    (hu1 : u1 • M.presheaf.map (homOfLE inf_le_left).op e1 = M.presheaf.map (homOfLE inf_le_right).op e') :
    (X.presheaf.map (homOfLE (inf_le_inf_right Q inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ Q)).op).hom u0 =
      (X.presheaf.map (homOfLE (inf_le_inf_right Q inf_le_right : (P0 ⊓ P1) ⊓ Q ≤ P1 ⊓ Q)).op).hom u1 *
      (X.presheaf.map (homOfLE (inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ P1)).op).hom g := by
  have h0 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_right Q inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ Q) hu0
  have h1 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_right Q inf_le_right : (P0 ⊓ P1) ⊓ Q ≤ P1 ⊓ Q) hu1
  have h2 := congrArg (M.presheaf.map (homOfLE (inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ P1)).op) hg
  rw [Scheme.Modules.map_smul, map_map, map_map] at h2
  apply (hF0 (inf_le_left.trans inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0) (inf_le_left.trans inf_le_left)).1
  change _ • _ = (_ * _) • _
  rw [mul_smul]
  erw [h0, ← h2]
  exact h1.symm

theorem cross_identity' {P Q0 Q1 : X.Opens} {e : Γ(M, P)} {e0' : Γ(M, Q0)} {e1' : Γ(M, Q1)}
    (hF : Scheme.Modules.IsFrameOn e P) (g' : Γ(X, Q0 ⊓ Q1))
    (hg' : M.presheaf.map (homOfLE inf_le_right).op e1' = g' • M.presheaf.map (homOfLE inf_le_left).op e0')
    (u0 : Γ(X, P ⊓ Q0))
    (hu0 : u0 • M.presheaf.map (homOfLE inf_le_left).op e = M.presheaf.map (homOfLE inf_le_right).op e0')
    (u1 : Γ(X, P ⊓ Q1))
    (hu1 : u1 • M.presheaf.map (homOfLE inf_le_left).op e = M.presheaf.map (homOfLE inf_le_right).op e1') :
    (X.presheaf.map (homOfLE (inf_le_inf_left P inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ P ⊓ Q1)).op).hom u1 =
      (X.presheaf.map (homOfLE (inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ Q0 ⊓ Q1)).op).hom g' *
      (X.presheaf.map (homOfLE (inf_le_inf_left P inf_le_left : P ⊓ (Q0 ⊓ Q1) ≤ P ⊓ Q0)).op).hom u0 := by
  have h0 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_left P inf_le_left : P ⊓ (Q0 ⊓ Q1) ≤ P ⊓ Q0) hu0
  have h1 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_left P inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ P ⊓ Q1) hu1
  have h2 := congrArg (M.presheaf.map (homOfLE (inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ Q0 ⊓ Q1)).op) hg'
  rw [Scheme.Modules.map_smul, map_map, map_map] at h2
  apply (hF (inf_le_left : P ⊓ (Q0 ⊓ Q1) ≤ P) inf_le_left).1
  change _ • _ = (_ * _) • _
  rw [mul_smul]
  erw [h1, h0, ← h2]

end Frames

end CoverCross

namespace CoverCross

section Transport

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u} [CommRing A] [Algebra R A]

theorem pre_inf {U V : (XA c A).Opens} {U' V' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U') (hV : σ c A ⁻¹ᵁ V = V') :
    σ c A ⁻¹ᵁ (U ⊓ V) = U' ⊓ V' := by
  rw [Scheme.Hom.preimage_inf, hU, hV]

theorem map_split_expr {U T : (XA c A).Opens} {U' T' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U')
    (hT : σ c A ⁻¹ᵁ T = T') (hTU : T ≤ U) (hTU' : T' ≤ U') (a b : Γ(XA c A, U)) :
    ((XD c A).presheaf.map (homOfLE hTU').op).hom (ι hU a + eps U' * ι hU b) =
      ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom a) + eps T' * ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom b) := by
  rw [map_add, map_mul, map_ι hU hT hTU hTU', map_ι hU hT hTU hTU', map_eps]

theorem map_split {U T : (XA c A).Opens} (hUa : IsAffineOpen U) {U' T' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U')
    (hT : σ c A ⁻¹ᵁ T = T') (hTU : T ≤ U) (hTU' : T' ≤ U') (u : Γ(XD c A, U')) :
    ((XD c A).presheaf.map (homOfLE hTU').op).hom u =
      ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom (cst hUa hU u)) +
        eps T' * ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom (lin hUa hU u)) := by
  conv_lhs => rw [split_eq hUa hU u]
  exact map_split_expr hU hT hTU hTU' _ _

theorem cst_mul_cst {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U')
    {u w : Γ(XD c A, U')} (huw : u * w = 1) : cst hUa hU u * cst hUa hU w = 1 := by
  have h := huw
  rw [split_eq hUa hU u, split_eq hUa hU w, mul_split] at h
  have h1 : (1 : Γ(XD c A, U')) = ι hU 1 + eps U' * ι hU 0 := by rw [map_one, map_zero, mul_zero, add_zero]
  rw [h1] at h
  exact (split_unique hUa hU h).1

end Transport

end CoverCross

namespace CoverCross

section Main

theorem coords_of_eq {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u} [CommRing A]
    [Algebra R A] {T : (XA c A).Opens} (hTa : IsAffineOpen T) {T' : (XD c A).Opens} (hT : σ c A ⁻¹ᵁ T = T')
    {a0 b0 a1 b1 f : Γ(XA c A, T)}
    (h : ι hT a0 + eps T' * ι hT b0 = (ι hT a1 + eps T' * ι hT b1) * (1 + eps T' * ι hT f)) :
    a0 = a1 ∧ b0 = a1 * f + b1 := by
  have h1 : (1 : Γ(XD c A, T')) + eps T' * ι hT f = ι hT 1 + eps T' * ι hT f := by rw [map_one]
  rw [h1, mul_split, mul_one, one_mul] at h
  exact split_unique hTa hT h

theorem coords_of_eq' {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u} [CommRing A]
    [Algebra R A] {T : (XA c A).Opens} (hTa : IsAffineOpen T) {T' : (XD c A).Opens} (hT : σ c A ⁻¹ᵁ T = T')
    {a0 b0 a1 b1 f : Γ(XA c A, T)}
    (h : ι hT a1 + eps T' * ι hT b1 = (1 + eps T' * ι hT f) * (ι hT a0 + eps T' * ι hT b0)) :
    a1 = a0 ∧ b1 = a0 * f + b0 := by
  have h1 : (1 : Γ(XD c A, T')) + eps T' * ι hT f = ι hT 1 + eps T' * ι hT f := by rw [map_one]
  rw [h1, mul_split, one_mul, one_mul] at h
  obtain ⟨H1, H2⟩ := split_unique hTa hT h
  exact ⟨H1, by rw [H2]; ring⟩

theorem map_oneAddEpsMul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u} [CommRing A]
    [Algebra R A] (𝒲 : C.TwoAffineOpenCover)
    (hW01 : σ c A ⁻¹ᵁ ((𝒲.pullback c A).U0 ⊓ (𝒲.pullback c A).U1) =
      (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
    {T : (XA c A).Opens} {T' : (XD c A).Opens} (hT : σ c A ⁻¹ᵁ T = T')
    (hTU : T ≤ (𝒲.pullback c A).U0 ⊓ (𝒲.pullback c A).U1)
    (hTU' : T' ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
    (f : Γ(XA c A, (𝒲.pullback c A).U0 ⊓ (𝒲.pullback c A).U1)) :
    ((XD c A).presheaf.map (homOfLE hTU').op).hom
        (show Γ(XD c A, (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒲 c f) =
      1 + eps T' * ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom f) := by
  have e : (show Γ(XD c A, (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
      from oneAddEpsMul A 𝒲 c f) = 1 + eps _ * ι hW01 f := rfl
  rw [e, map_add, map_one, map_mul, map_eps, map_ι hW01 hT hTU hTU']

set_option maxHeartbeats 4000000 in
theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ  : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲}
    {δ' : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲'}
    (hδ : IsDeformationClassMap c ε A 𝒲 δ) (hδ' : IsDeformationClassMap c ε A 𝒲' δ')
    (x : RigKerDualNumber c ε A)
    (s  : ((𝒲.pullback c A).cover  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (s' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0;  let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0; let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom g00
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom g10
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom s ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom g11
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom s ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom g00
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom g11
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom g10
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' := by
  intro X' W0 W1 V0 V1
  simp only [X']

  have pW0 : σ c A ⁻¹ᵁ W0 = (𝒲.pullback c (DualNumber A)).U0 := baseChangeSnd_preimage_U0 𝒲 c _
  have pW1 : σ c A ⁻¹ᵁ W1 = (𝒲.pullback c (DualNumber A)).U1 := baseChangeSnd_preimage_U1 𝒲 c _
  have pV0 : σ c A ⁻¹ᵁ V0 = (𝒲'.pullback c (DualNumber A)).U0 := baseChangeSnd_preimage_U0 𝒲' c _
  have pV1 : σ c A ⁻¹ᵁ V1 = (𝒲'.pullback c (DualNumber A)).U1 := baseChangeSnd_preimage_U1 𝒲' c _
  have pW01 := pre_inf pW0 pW1
  have pV01 := pre_inf pV0 pV1
  have p00 := pre_inf pW0 pV0; have p01 := pre_inf pW0 pV1; have p10 := pre_inf pW1 pV0; have p11 := pre_inf pW1 pV1
  have pT0 := pre_inf pW01 pV0; have pT1 := pre_inf pW01 pV1
  have pS0 := pre_inf pW0 pV01; have pS1 := pre_inf pW1 pV01

  haveI : (XA c A).IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)).mp
      (inferInstance : IsSeparated (pullback.snd c (specMap R A)))
  have aW0 : IsAffineOpen W0 := (𝒲.pullback c A).isAffineOpen_U0
  have aW1 : IsAffineOpen W1 := (𝒲.pullback c A).isAffineOpen_U1
  have aV0 : IsAffineOpen V0 := (𝒲'.pullback c A).isAffineOpen_U0
  have aV1 : IsAffineOpen V1 := (𝒲'.pullback c A).isAffineOpen_U1
  have aW01 : IsAffineOpen (W0 ⊓ W1) := (𝒲.pullback c A).isAffineOpen_inf
  have aV01 : IsAffineOpen (V0 ⊓ V1) := (𝒲'.pullback c A).isAffineOpen_inf
  have af00 := aW0.inf aV0; have af01 := aW0.inf aV1; have af10 := aW1.inf aV0; have af11 := aW1.inf aV1
  have afT0 := aW01.inf aV0; have afT1 := aW01.inf aV1; have afS0 := aW0.inf aV01; have afS1 := aW1.inf aV01

  obtain ⟨M, rfl⟩ := Quotient.exists_rep x
  obtain ⟨e0, e1, f, hF0, hF1, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒲 M
  obtain ⟨e0', e1', f', hF0', hF1', hM'⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒲' M

  have hc : (Submodule.Quotient.mk s : H1StructureSheaf c A 𝒲) = Submodule.Quotient.mk f :=
    hs.symm.trans (hδ M e0 e1 f hF0 hF1 hM)
  have hc' : (Submodule.Quotient.mk s' : H1StructureSheaf c A 𝒲') = Submodule.Quotient.mk f' :=
    hs'.symm.trans (hδ' M e0' e1' f' hF0' hF1' hM')
  obtain ⟨p, hp⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 hc)
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 hc')
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r0_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, Units.val_one, one_mul] at hp hq

  change ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ W1 ≤ W1)).op).hom p.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ W1 ≤ W0)).op).hom p.1 =
      (s : Γ(XA c A, W0 ⊓ W1)) - (f : Γ(XA c A, W0 ⊓ W1)) at hp
  have hp2 : ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ W1 ≤ W1)).op).hom p.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ W1 ≤ W0)).op).hom p.1 + (show Γ(XA c A, W0 ⊓ W1) from f) =
      (show Γ(XA c A, W0 ⊓ W1) from s) := by
    rw [hp]; exact sub_add_cancel s f
  change ((XA c A).presheaf.map (homOfLE (inf_le_right : V0 ⊓ V1 ≤ V1)).op).hom q.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : V0 ⊓ V1 ≤ V0)).op).hom q.1 =
      (s' : Γ(XA c A, V0 ⊓ V1)) - (f' : Γ(XA c A, V0 ⊓ V1)) at hq
  have hq2 : ((XA c A).presheaf.map (homOfLE (inf_le_right : V0 ⊓ V1 ≤ V1)).op).hom q.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : V0 ⊓ V1 ≤ V0)).op).hom q.1 + (show Γ(XA c A, V0 ⊓ V1) from f') =
      (show Γ(XA c A, V0 ⊓ V1) from s') := by
    rw [hq]; exact sub_add_cancel s' f'

  obtain ⟨u00, w00, hu00, -, huw00⟩ := exists_units_of_isFrameOn (M := M.1.L)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲.pullback c (DualNumber A)).U0) (inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲'.pullback c (DualNumber A)).U0) hF0 hF0'
  obtain ⟨u01, w01, hu01, -, huw01⟩ := exists_units_of_isFrameOn (M := M.1.L)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲.pullback c (DualNumber A)).U0) (inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲'.pullback c (DualNumber A)).U1) hF0 hF1'
  obtain ⟨u10, w10, hu10, -, huw10⟩ := exists_units_of_isFrameOn (M := M.1.L)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲.pullback c (DualNumber A)).U1) (inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲'.pullback c (DualNumber A)).U0) hF1 hF0'
  obtain ⟨u11, w11, hu11, -, huw11⟩ := exists_units_of_isFrameOn (M := M.1.L)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲.pullback c (DualNumber A)).U1) (inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲'.pullback c (DualNumber A)).U1) hF1 hF1'

  set a00 := cst af00 p00 u00; set b00 := lin af00 p00 u00; set a00' := cst af00 p00 w00
  set a01 := cst af01 p01 u01; set b01 := lin af01 p01 u01; set a01' := cst af01 p01 w01
  set a10 := cst af10 p10 u10; set b10 := lin af10 p10 u10; set a10' := cst af10 p10 w10
  set a11 := cst af11 p11 u11; set b11 := lin af11 p11 u11; set a11' := cst af11 p11 w11
  have i00 : a00 * a00' = 1 := cst_mul_cst _ p00 huw00
  have i01 : a01 * a01' = 1 := cst_mul_cst _ p01 huw01
  have i10 : a10 * a10' = 1 := cst_mul_cst _ p10 huw10
  have i11 : a11 * a11' = 1 := cst_mul_cst _ p11 huw11

  have X0 := cross_identity (M := M.1.L) hF0 _ hM u00 hu00 u10 hu10
  have X1 := cross_identity (M := M.1.L) hF0 _ hM u01 hu01 u11 hu11
  have Y0 := cross_identity' (M := M.1.L) hF0 _ hM' u00 hu00 u01 hu01
  have Y1 := cross_identity' (M := M.1.L) hF1 _ hM' u10 hu10 u11 hu11
  have E0 : ι pT0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 u00)) + eps (((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0) * ι pT0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (lin af00 p00 u00)) =
      (ι pT0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 u10)) + eps (((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0) * ι pT0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (lin af10 p10 u10))) * (1 + eps (((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0) * ι pT0 (((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom (f))) := by
    rw [← map_split af00 p00 pT0 (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0) (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U0 inf_le_left : ((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U0) u00,
      ← map_split af10 p10 pT0 (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0) (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U0 inf_le_right : ((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U0) u10,
      ← map_oneAddEpsMul 𝒲 pW01 pT0 (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1) (inf_le_left : ((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) f]
    exact X0
  obtain ⟨HAE0, HBE0⟩ := coords_of_eq afT0 pT0 E0
  have E1 : ι pT1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 u01)) + eps (((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1) * ι pT1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (lin af01 p01 u01)) =
      (ι pT1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 u11)) + eps (((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1) * ι pT1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (lin af11 p11 u11))) * (1 + eps (((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1) * ι pT1 (((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom (f))) := by
    rw [← map_split af01 p01 pT1 (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1) (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U1 inf_le_left : ((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) u01,
      ← map_split af11 p11 pT1 (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1) (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U1 inf_le_right : ((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U1) u11,
      ← map_oneAddEpsMul 𝒲 pW01 pT1 (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1) (inf_le_left : ((𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) f]
    exact X1
  obtain ⟨HAE1, HBE1⟩ := coords_of_eq afT1 pT1 E1
  have F0 : ι pS0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 u01)) + eps ((𝒲.pullback c (DualNumber A)).U0 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) * ι pS0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (lin af01 p01 u01)) =
      (1 + eps ((𝒲.pullback c (DualNumber A)).U0 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) * ι pS0 (((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom (f'))) * (ι pS0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 u00)) + eps ((𝒲.pullback c (DualNumber A)).U0 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) * ι pS0 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (lin af00 p00 u00))) := by
    rw [← map_split af00 p00 pS0 (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0) (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U0 inf_le_left : (𝒲.pullback c (DualNumber A)).U0 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U0) u00,
      ← map_split af01 p01 pS0 (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1) (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U0 inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) u01,
      ← map_oneAddEpsMul 𝒲' pV01 pS0 (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1) (inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤ (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) f']
    exact Y0
  obtain ⟨HAF0, HBF0⟩ := coords_of_eq' afS0 pS0 F0
  have F1 : ι pS1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 u11)) + eps ((𝒲.pullback c (DualNumber A)).U1 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) * ι pS1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (lin af11 p11 u11)) =
      (1 + eps ((𝒲.pullback c (DualNumber A)).U1 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) * ι pS1 (((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom (f'))) * (ι pS1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 u10)) + eps ((𝒲.pullback c (DualNumber A)).U1 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) * ι pS1 (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (lin af10 p10 u10))) := by
    rw [← map_split af10 p10 pS1 (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0) (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U1 inf_le_left : (𝒲.pullback c (DualNumber A)).U1 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤ (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U0) u10,
      ← map_split af11 p11 pS1 (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1) (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U1 inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤ (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U1) u11,
      ← map_oneAddEpsMul 𝒲' pV01 pS1 (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1) (inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓ ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤ (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) f']
    exact Y1
  obtain ⟨HAF1, HBF1⟩ := coords_of_eq' afS1 pS1 F1
  have I00a : ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 u00) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom z) i00
    simp only [map_mul, map_one] at this
    exact this
  have I10a : ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 u10) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom z) i10
    simp only [map_mul, map_one] at this
    exact this
  have I01b : ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 u01) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom z) i01
    simp only [map_mul, map_one] at this
    exact this
  have I11b : ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 u11) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom z) i11
    simp only [map_mul, map_one] at this
    exact this
  have I00c : ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 u00) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom z) i00
    simp only [map_mul, map_one] at this
    exact this
  have I01c : ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 u01) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom z) i01
    simp only [map_mul, map_one] at this
    exact this
  have I10d : ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 u10) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom z) i10
    simp only [map_mul, map_one] at this
    exact this
  have I11d : ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 u11) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11) = 1 := by
    have := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom z) i11
    simp only [map_mul, map_one] at this
    exact this
  have HP0 := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom z) hp2
  simp only [map_add, map_sub, map_map_ring] at HP0
  have HP1 := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom z) hp2
  simp only [map_add, map_sub, map_map_ring] at HP1
  have HQ0 := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom z) hq2
  simp only [map_add, map_sub, map_map_ring] at HQ0
  have HQ1 := congrArg (fun z => ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom z) hq2
  simp only [map_add, map_sub, map_map_ring] at HQ1
  refine ⟨lin af00 p00 u00 * cst af00 p00 w00 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ V0 ≤ W0)).op).hom p.1
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ V0 ≤ V0)).op).hom q.1,
          lin af01 p01 u01 * cst af01 p01 w01 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ V1 ≤ W0)).op).hom p.1
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ V1 ≤ V1)).op).hom q.2,
          lin af10 p10 u10 * cst af10 p10 w10 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W1 ⊓ V0 ≤ W1)).op).hom p.2
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ V0 ≤ V0)).op).hom q.1,
          lin af11 p11 u11 * cst af11 p11 w11 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W1 ⊓ V1 ≤ W1)).op).hom p.2
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ V1 ≤ V1)).op).hom q.2, ?_, ?_, ?_, ?_⟩
  ·
    have HC : ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00) = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10) := by
      linear_combination (-(((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00))) * I10a + (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10)) * I00a
        - (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10)) * HAE0
    simp only [map_sub, map_add, map_mul, map_map_ring]
    linear_combination (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00)) * HBE0 + (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (lin af10 p10 u10) + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom (f) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom (cst af10 p10 u10)) * HC + HP0
      + (((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom (f)) * I10a
  ·
    have HC : ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01) = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11) := by
      linear_combination (-(((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01))) * I11b + (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11)) * I01b
        - (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11)) * HAE1
    simp only [map_sub, map_add, map_mul, map_map_ring]
    linear_combination (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01)) * HBE1 + (((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (lin af11 p11 u11) + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom (f) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom (cst af11 p11 u11)) * HC + HP1
      + (((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom (f)) * I11b
  ·
    have HC : ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01) = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00) := by
      linear_combination (-(((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01))) * I00c + (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00)) * I01c
        - (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 w00)) * HAF0
    simp only [map_sub, map_add, map_mul, map_map_ring]
    linear_combination (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom (cst af01 p01 w01)) * HBF0 + (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (lin af00 p00 u00) + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom (f') * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom (cst af00 p00 u00)) * HC + HQ0
      + (((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom (f')) * I00c
  ·
    have HC : ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11) = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10) := by
      linear_combination (-(((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11))) * I10d + (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10)) * I11d
        - (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11) * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 w10)) * HAF1
    simp only [map_sub, map_add, map_mul, map_map_ring]
    linear_combination (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom (cst af11 p11 w11)) * HBF1 + (((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (lin af10 p10 u10) + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom (f') * ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom (cst af10 p10 u10)) * HC + HQ1
      + (((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom (f')) * I10d

end Main

end CoverCross

end

open CoverCross in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ  : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲}
    {δ' : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲'}
    (hδ : IsDeformationClassMap c ε A 𝒲 δ) (hδ' : IsDeformationClassMap c ε A 𝒲' δ')
    (x : RigKerDualNumber c ε A)
    (s  : ((𝒲.pullback c A).cover  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (s' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0;  let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0; let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom g00
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom s ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom g11
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom s ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom g00
          + (X'.presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom g11
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' :=
  CoverCross.main c ε A 𝒲 𝒲' hδ hδ' x s s' hs hs'

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections (solution)
