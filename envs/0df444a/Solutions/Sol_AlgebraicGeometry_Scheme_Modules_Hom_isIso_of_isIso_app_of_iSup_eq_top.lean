-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/94e56468-38f7-5b8c-a1b9-a41035e6365d

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ := by

  have cover : ∀ x : X, ∃ i, x ∈ U i := fun x ↦
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial)

  let F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  haveI : (Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat.{u}) :=
    inferInstance
  have hψ : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨?_, ?_⟩
    ·
      refine ⟨fun {W} x y hxy p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W.unop ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W.unop ⊓ U i) inf_le_right
      apply (ConcreteCategory.bijective_of_isIso (φ.app (W.unop ⊓ U i))).1
      change φ.mapPresheaf.app _ (M.presheaf.map _ x) = φ.mapPresheaf.app _ (M.presheaf.map _ y)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg _ hxy
    ·
      refine ⟨fun {W} s p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W ⊓ U i) inf_le_right
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (φ.app (W ⊓ U i))).2
        (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op s)
      exact ⟨t, ht⟩

  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  have : IsIso (ψ.hom.app (Opposite.op V)) := by
    change IsIso (((sheafToPresheaf _ _).map ψ).app (Opposite.op V))
    infer_instance
  exact this

end S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top (solution)
