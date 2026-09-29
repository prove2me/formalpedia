-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c8e9e19f-a61e-5379-b61d-ec7625953024

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry"
open AlgebraicGeometry.Scheme.Modules

namespace N2P1

variable {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens}

theorem map_map (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem ihomSection_ext (p : Γ(P, V)) (hp : IsFrameOn p V) {θ θ' : Γ((ihom P).obj Q, V)}
    (h : ihomEval P Q V p θ = ihomEval P Q V p θ') : θ = θ' := by
  apply ihom_sections_ext
  intro W i m
  have hW : W ≤ V := i.le
  obtain ⟨g, rfl⟩ := (hp hW hW).2 m
  simp only
  have hi : i = homOfLE hW := Subsingleton.elim _ _
  subst hi
  rw [ihomEval_smul_left, ihomEval_smul_left, ← map_ihomEval, ← map_ihomEval, h]

noncomputable def coeff (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) :
    Γ(P, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W) Γ(P, W) (P.presheaf.map (homOfLE hW).op p))
    (hp hW hW)).symm

theorem coeff_smul (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) (g : Γ(X, W)) :
    coeff p hp hW (g • P.presheaf.map (homOfLE hW).op p) = g := by
  apply (coeff p hp hW).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem smul_coeff (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) (x : Γ(P, W)) :
    coeff p hp hW x • P.presheaf.map (homOfLE hW).op p = x := by
  obtain ⟨g, rfl⟩ := (hp hW hW).2 x
  simp only
  rw [coeff_smul]

theorem exists_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃ θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q := by
  classical

  let fam : PresheafOfModules.InternalHom.PiFamily ((toPMod X).obj P) ((toPMod X).obj Q) (op V) :=
    fun Y f =>
      (show Γ(P, Y.unop) →ₗ[Γ(X, Y.unop)] Γ(Q, Y.unop) from
        (LinearMap.toSpanSingleton Γ(X, Y.unop) Γ(Q, Y.unop) (Q.presheaf.map (homOfLE f.unop.le).op q)).comp
          (coeff p hp f.unop.le).toLinearMap)
  have fam_apply : ∀ {Y : (X.Opens)ᵒᵖ} (f : op V ⟶ Y) (x : Γ(P, Y.unop)),
      fam f x = coeff p hp f.unop.le x • Q.presheaf.map (homOfLE f.unop.le).op q := fun f x => rfl
  have hfam : PresheafOfModules.InternalHom.IsNatural fam := by
    intro Y Z f g x
    change Q.presheaf.map g (fam f x) = fam (f ≫ g) (P.presheaf.map g x)
    rw [fam_apply f, fam_apply (f ≫ g)]
    have hg : g = (homOfLE g.unop.le).op := Subsingleton.elim _ _
    rw [hg, Q.map_smul, map_map]
    congr 1

    symm
    apply (coeff p hp (f ≫ (homOfLE g.unop.le).op).unop.le).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change _ = (X.presheaf.map (homOfLE g.unop.le).op (coeff p hp f.unop.le x)) •
      P.presheaf.map (homOfLE _).op p
    conv_lhs => rw [← smul_coeff p hp f.unop.le x]
    rw [P.map_smul, map_map]
  let φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj P) ((toPMod X).obj Q) (op V) :=
    ⟨fam, hfam⟩
  refine ⟨(SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property P Q (op V)).symm φ, ?_⟩
  change SheafOfModules.ihomEval X.sheaf.obj X.ringCatSheaf.property P Q (op V) p _ = q
  rw [SheafOfModules.ihomEval_def, AddEquiv.apply_symm_apply]
  change fam (𝟙 (op V)) p = q
  rw [fam_apply (𝟙 (op V))]
  change coeff p hp le_rfl p • Q.presheaf.map (homOfLE le_rfl).op q = q
  have h1 : coeff p hp (le_rfl : V ≤ V) p = 1 := by
    have := coeff_smul p hp (le_rfl : V ≤ V) 1
    rw [one_smul] at this
    have hp1 : P.presheaf.map (homOfLE (le_rfl : V ≤ V)).op p = p := by
      rw [Subsingleton.elim (homOfLE (le_rfl : V ≤ V)) (𝟙 V), op_id, P.presheaf.map_id]; rfl
    rw [hp1] at this
    exact this
  rw [h1, one_smul, Subsingleton.elim (homOfLE (le_rfl : V ≤ V)) (𝟙 V), op_id, Q.presheaf.map_id]
  rfl

theorem exists_unique_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q := by
  obtain ⟨θ, hθ⟩ := exists_ihomSection p hp q
  exact ⟨θ, hθ, fun θ' hθ' => ihomSection_ext p hp (hθ'.trans hθ.symm)⟩

end N2P1

open AlgebraicGeometry in
theorem solution {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens} {p : Γ(P, V)}
    (hp : Scheme.Modules.IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), Scheme.Modules.ihomEval P Q V p θ = q :=
  N2P1.exists_unique_ihomSection p hp q

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq (solution)
