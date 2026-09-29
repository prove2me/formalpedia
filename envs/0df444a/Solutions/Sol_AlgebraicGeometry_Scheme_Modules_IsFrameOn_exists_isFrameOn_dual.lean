-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1f4d6ba0-cc47-538e-bce9-be781a63f70b

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

noncomputable section

namespace DualFrameAux

variable {X : Scheme.{u}}

lemma presheaf_map_map (M : X.Modules) {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x : Γ(M, A)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

variable {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)} (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U)

include hp in
lemma bij {W : X.Opens} (hW : W ≤ V) : Function.Bijective fun g : Γ(X, W) => g • P.presheaf.map (homOfLE ((hW : _ ≤ V).trans hVU)).op p :=
  hp (hW.trans hVU) hW

noncomputable def coef {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) : Γ(X, W) :=
  (Equiv.ofBijective _ (bij hp hVU hW)).symm m

lemma coef_smul_pr {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) : coef hp hVU hW m • P.presheaf.map (homOfLE ((hW : _ ≤ V).trans hVU)).op p = m :=
  Equiv.ofBijective_apply_symm_apply _ (bij hp hVU hW) m

lemma coef_eq_of_smul_eq {W : X.Opens} (hW : W ≤ V) {m : Γ(P, W)} {g : Γ(X, W)} (h : g • P.presheaf.map (homOfLE ((hW : _ ≤ V).trans hVU)).op p = m) :
    coef hp hVU hW m = g :=
  (bij hp hVU hW).1 ((coef_smul_pr hp hVU hW m).trans h.symm)

lemma coef_pr {W : X.Opens} (hW : W ≤ V) : coef hp hVU hW (P.presheaf.map (homOfLE ((hW : _ ≤ V).trans hVU)).op p) = 1 :=
  coef_eq_of_smul_eq hp hVU hW (one_smul _ _)

lemma coef_add {W : X.Opens} (hW : W ≤ V) (m m' : Γ(P, W)) :
    coef hp hVU hW (m + m') = coef hp hVU hW m + coef hp hVU hW m' :=
  coef_eq_of_smul_eq hp hVU hW (by rw [add_smul, coef_smul_pr, coef_smul_pr])

lemma coef_smul {W : X.Opens} (hW : W ≤ V) (r : Γ(X, W)) (m : Γ(P, W)) :
    coef hp hVU hW (r • m) = r * coef hp hVU hW m :=
  coef_eq_of_smul_eq hp hVU hW (by rw [mul_smul, coef_smul_pr])

lemma map_coef {W W' : X.Opens} (hW : W ≤ V) (i : W' ⟶ W) (m : Γ(P, W)) :
    X.presheaf.map i.op (coef hp hVU hW m) = coef hp hVU (i.le.trans hW) (P.presheaf.map i.op m) := by
  symm
  apply coef_eq_of_smul_eq hp hVU (i.le.trans hW)
  have h := congrArg (P.presheaf.map i.op) (coef_smul_pr hp hVU hW m)
  rw [Scheme.Modules.map_smul] at h
  rw [← h]
  congr 1
  exact (presheaf_map_map P _ _ _ p).symm

noncomputable def coefLin {W : X.Opens} (hW : W ≤ V) : Γ(P, W) →ₗ[Γ(X, W)] Γ(𝟙_ X.Modules, W) where
  toFun m := coef hp hVU hW m • Scheme.Modules.unitSection W
  map_add' m m' := by rw [coef_add, add_smul]
  map_smul' r m := by rw [coef_smul, mul_smul, RingHom.id_apply]

lemma coefLin_apply {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) :
    coefLin hp hVU hW m = coef hp hVU hW m • Scheme.Modules.unitSection W := rfl

noncomputable def coefFamily :
    PresheafOfModules.InternalHom.naturalFamilies ((Scheme.Modules.toPMod X).obj P)
      ((Scheme.Modules.toPMod X).obj (𝟙_ X.Modules)) (op V) :=
  ⟨fun W f => coefLin hp hVU (W := W.unop) (f.unop.le : W.unop ≤ V), by
    intro W W' f g m
    change (𝟙_ X.Modules).presheaf.map g (coef hp hVU _ m • Scheme.Modules.unitSection W.unop) =
      coef hp hVU _ (P.presheaf.map g m) • Scheme.Modules.unitSection W'.unop
    rw [show g = g.unop.op from rfl, Scheme.Modules.map_smul, Scheme.Modules.map_unitSection]
    congr 1
    exact map_coef hp hVU _ g.unop m⟩

lemma coefFamily_app {W : (X.Opens)ᵒᵖ} (f : op V ⟶ W) (m : Γ(P, W.unop)) :
    (coefFamily hp hVU).1 f m = coef hp hVU (f.unop.le : W.unop ≤ V) m • Scheme.Modules.unitSection W.unop := rfl

noncomputable def dualSection : Γ(Scheme.Modules.dual P, V) :=
  (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property P (𝟙_ X.Modules) (op V)).symm
    (coefFamily hp hVU)

lemma ihomEval_map_dualSection {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) :
    Scheme.Modules.ihomEval P (𝟙_ X.Modules) W m
        ((Scheme.Modules.dual P).presheaf.map (homOfLE hW).op (dualSection hp hVU)) =
      coef hp hVU hW m • Scheme.Modules.unitSection W := by
  have h := SheafOfModules.ihomSectionsEquivFamily_app_eq_ihomEval X.sheaf.obj X.ringCatSheaf.property
    (M := P) (N := 𝟙_ X.Modules) (homOfLE hW).op (dualSection hp hVU) m
  rw [dualSection, AddEquiv.apply_symm_apply] at h

  exact h.symm

end DualFrameAux

end

open DualFrameAux in
theorem solution
    {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)}
    (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U) :
    ∃ q : Γ(Scheme.Modules.dual P, V), Scheme.Modules.IsFrameOn q V ∧
      Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q =
        Scheme.Modules.unitSection V := by
  classical
  refine ⟨dualSection hp hVU, ?_, ?_⟩
  · intro W hWV hWV'

    have hq : ∀ (g : Γ(X, W)),
        Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p)
          (g • (Scheme.Modules.dual P).presheaf.map (homOfLE hWV).op (dualSection hp hVU)) =
          g • Scheme.Modules.unitSection W := fun g => by
      rw [Scheme.Modules.ihomEval_smul_right, ihomEval_map_dualSection hp hVU hWV (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p)]

      rw [show coef hp hVU hWV (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) = 1 from coef_pr hp hVU hWV', one_smul]
    refine ⟨fun g g' hgg' => ?_, fun t => ?_⟩
    ·
      have h := congrArg (Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p)) hgg'
      change Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) (g • _) =
        Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) (g' • _) at h
      rw [hq, hq] at h
      exact Scheme.Modules.smul_unitSection_bijective.1 h
    ·
      let g : Γ(X, W) := Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) t
      refine ⟨g, ?_⟩
      change g • (Scheme.Modules.dual P).presheaf.map (homOfLE hWV).op (dualSection hp hVU) = t
      apply Scheme.Modules.ihom_sections_ext
      intro W' i m

      have hm : m = coef hp hVU (i.le.trans hWV') m • P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤ V).trans hVU)).op p :=
        (coef_smul_pr hp hVU (i.le.trans hWV') m).symm
      rw [hm, Scheme.Modules.ihomEval_smul_left, Scheme.Modules.ihomEval_smul_left]
      congr 1

      rw [Scheme.Modules.map_smul, DualFrameAux.presheaf_map_map (Scheme.Modules.dual P) _ _ (homOfLE (i.le.trans hWV)),
        Scheme.Modules.ihomEval_smul_right, ihomEval_map_dualSection hp hVU (i.le.trans hWV) (P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤ V).trans hVU)).op p),
        show coef hp hVU (i.le.trans hWV) (P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤ V).trans hVU)).op p) = 1 from coef_pr hp hVU _, one_smul]

      rw [show P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤ V).trans hVU)).op p =
          P.presheaf.map i.op (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) from
        (DualFrameAux.presheaf_map_map P _ _ _ p).symm, ← Scheme.Modules.map_ihomEval]

      rw [Scheme.Modules.smul_unitSection]
      have h2 := Scheme.Modules.map_smul (𝟙_ X.Modules) i g (Scheme.Modules.unitSection W)
      rw [Scheme.Modules.smul_unitSection, Scheme.Modules.map_unitSection, Scheme.Modules.smul_unitSection] at h2
      exact h2.symm
  ·
    have h := ihomEval_map_dualSection hp hVU (le_refl V) (P.presheaf.map (homOfLE ((le_refl V : _ ≤ V).trans hVU)).op p)
    rw [show coef hp hVU (le_refl V) (P.presheaf.map (homOfLE ((le_refl V : _ ≤ V).trans hVU)).op p) = 1 from coef_pr hp hVU _, one_smul] at h

    have hid : (Scheme.Modules.dual P).presheaf.map (homOfLE (le_refl V)).op (dualSection hp hVU) = dualSection hp hVU := by
      rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]; rfl
    rw [hid] at h
    exact h

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual (solution)
