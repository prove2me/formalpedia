-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_of_forall_pullbackSection_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/25f5ad63-e9f6-58de-be10-9b83dade4304

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app Scheme.Modules.pullback pointOfClosedPoint_apply Scheme.Modules.Hom.comp_app pointOfClosedPoint Scheme.Modules.Hom LocallyOfFiniteType Spec Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp IsReduced Scheme.Modules Scheme.IdealSheafData.support_eq_top_iff Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso"
namespace R4bAux
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} {M : X.Modules}

lemma unitSection_eq_smul (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    m = ofUnitSection U m • toUnitSection U 1 := by
  apply ofUnitSection_injective
  rw [ofUnitSection_smul, ofUnitSection_toUnitSection, mul_one]

lemma app_eq_smul (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    s.app U m = ofUnitSection U m • s.app U (toUnitSection U 1) := by
  conv_lhs => rw [unitSection_eq_smul U m]
  rw [Scheme.Modules.Hom.app_smul]

lemma map_toUnitSection_one {V W : X.Opens} (i : W ⟶ V) :
    (𝟙_ X.Modules).presheaf.map i.op (toUnitSection V 1) = toUnitSection W 1 := by
  apply ofUnitSection_injective
  rw [ofUnitSection_map, ofUnitSection_toUnitSection, ofUnitSection_toUnitSection, map_one]

lemma map_app_one {V W : X.Opens} (i : W ⟶ V) (s : 𝟙_ X.Modules ⟶ M) :
    M.presheaf.map i.op (s.app V (toUnitSection V 1)) = s.app W (toUnitSection W 1) := by
  have h := NatTrans.naturality_apply s.mapPresheaf i.op (toUnitSection V 1)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op] at h
  rw [← h, map_toUnitSection_one]

theorem eq_zero_of_zeroSchemeIdeal_eq_bot (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : zeroSchemeIdeal s = ⊥) : s = 0 := by

  have hloc : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ s.app W (toUnitSection W 1) = 0 := by
    intro x
    obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
    have hideal := ((hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1
    have h0 : (zeroSchemeIdeal s).ideal U = ⊥ := by
      rw [hZ]; exact congrFun Scheme.IdealSheafData.ideal_bot U
    have hc : coeff s U.1 τ.hom = 0 :=
      Ideal.span_singleton_eq_bot.mp (hideal.symm.trans h0)
    have hr : restrictSection s U.1 = 0 := by
      have hinj : Function.Injective (U.1.topIso.hom : Γ(↑U.1, ⊤) → Γ(X, U.1)) :=
        (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).1
      have h2 : ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s U.1)) = 0 :=
        hinj (by rw [map_zero]; exact hc)
      have h3 : τ.hom.app ⊤ (restrictSection s U.1) = 0 := h2
      have h4 := congrArg (τ.inv.app ⊤) h3
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
        Scheme.Modules.Hom.id_app] at h4
      exact h4
    refine ⟨U.1, hxU, ?_⟩
    have hU : U.1.ι ''ᵁ ⊤ = U.1 := U.1.ι_image_top
    rw [← map_app_one (eqToHom hU.symm) s]
    change M.presheaf.map _ (restrictSection s U.1) = 0
    rw [hr]; exact map_zero _

  apply Scheme.Modules.hom_ext
  intro V
  ext m
  rw [Scheme.Modules.Hom.zero_app, app_eq_smul]
  suffices h1 : s.app V (toUnitSection V 1) = 0 by
    rw [h1, smul_zero]; rfl
  choose W hxW hW using hloc
  let 𝒰 : V → X.Opens := fun x => V ⊓ W x.1
  have hcov : V ≤ iSup 𝒰 := fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxW x⟩
  let F : TopCat.Sheaf Ab X.toTopCat := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F 𝒰 V (fun x => homOfLE inf_le_left) hcov _ _ (fun x => ?_)
  show M.presheaf.map (homOfLE (inf_le_left : V ⊓ W x.1 ≤ V)).op (s.app V (toUnitSection V 1)) =
    M.presheaf.map (homOfLE (inf_le_left : V ⊓ W x.1 ≤ V)).op 0
  rw [map_app_one, ← map_app_one (homOfLE inf_le_right : V ⊓ W x.1 ⟶ W x.1), hW, map_zero, map_zero]

end AlgebraicGeometry.R4bAux

open AlgebraicGeometry.R4bAux in

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsReduced X]
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (σ₁ σ₂ : 𝟙_ X.Modules ⟶ L)
    (h : ∀ p : Spec (CommRingCat.of k) ⟶ X, p ≫ f = 𝟙 _ →
      Scheme.Modules.pullbackSection p σ₁ = Scheme.Modules.pullbackSection p σ₂) :
    σ₁ = σ₂ := by
  suffices hz : σ₁ - σ₂ = 0 from sub_eq_zero.mp hz

  have hvan : ∀ p : Spec (CommRingCat.of k) ⟶ X, p ≫ f = 𝟙 _ →
      Scheme.Modules.pullbackSection p (σ₁ - σ₂) = 0 := by
    intro p hp
    have hsub := (Scheme.Modules.pullback p).map_sub (f := σ₁) (g := σ₂)
    have e1 : Scheme.Modules.pullbackSection p (σ₁ - σ₂) =
        Scheme.Modules.pullbackSection p σ₁ - Scheme.Modules.pullbackSection p σ₂ := by
      show (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map (σ₁ - σ₂) = _
      exact (congrArg ((Scheme.Modules.pullbackUnitIso p).inv ≫ ·) hsub).trans (Preadditive.comp_sub _ _ _)
    rw [e1, h p hp, sub_self]
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hcl : closedPoints X ⊆ ((Scheme.Modules.zeroSchemeIdeal (σ₁ - σ₂)).support : Set X) := by
    intro x hx
    have := (hL.pullbackSection_eq_zero_iff_mem_support (σ₁ - σ₂) (pointOfClosedPoint f x hx)).mp
      (hvan _ (pointOfClosedPoint_comp f x hx))
    have hpt : (pointOfClosedPoint f x hx).base (IsLocalRing.closedPoint k) = x :=
      pointOfClosedPoint_apply f x hx _
    rw [hpt] at this
    exact this
  have hsupp : (Scheme.Modules.zeroSchemeIdeal (σ₁ - σ₂)).support = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hx : x ∈ closure (closedPoints X) := by rw [closure_closedPoints]; trivial
    exact (Scheme.Modules.zeroSchemeIdeal (σ₁ - σ₂)).support.isClosed.closure_subset_iff.mpr hcl hx
  exact eq_zero_of_zeroSchemeIdeal_eq_bot hL _ (Scheme.IdealSheafData.support_eq_top_iff.mp hsupp)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq (solution)
