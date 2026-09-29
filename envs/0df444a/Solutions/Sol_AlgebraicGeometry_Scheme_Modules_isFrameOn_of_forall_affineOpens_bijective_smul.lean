-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isFrameOn_of_forall_affineOpens_bijective_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8ca068fc-67a1-565a-89e3-df3efa3c07f9

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

open TopologicalSpace Opposite in
theorem solution
    {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) (s : Γ(N, U))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      Function.Bijective (fun a : Γ(X, W.1) => a • (N.presheaf.map (homOfLE hW).op s : Γ(N, W.1)))) :
    Scheme.Modules.IsFrameOn s U := by
  classical

  have resN : ∀ {Z W V : X.Opens} (hWZ : W ≤ Z) (hVW : V ≤ W) (t : Γ(N, Z)),
      N.presheaf.map (homOfLE hVW).op (N.presheaf.map (homOfLE hWZ).op t) =
        N.presheaf.map (homOfLE (hVW.trans hWZ)).op t := by
    intro Z W V hWZ hVW t
    rw [← CategoryTheory.comp_apply, ← N.presheaf.map_comp]; rfl

  let ιW : X.Opens → Type u := fun W => {V : X.affineOpens // (V : X.Opens) ≤ W}
  have hcov : ∀ W : X.Opens, W ≤ ⨆ V : ιW W, (V.1 : X.Opens) := by
    intro W x hx
    obtain ⟨V, hV, hxV, hVW⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩

  let shN : TopCat.Sheaf Ab X := ⟨N.presheaf, Scheme.Modules.isSheaf N⟩

  have hinj : ∀ (W : X.Opens) (hWU : W ≤ U),
      Function.Injective (fun a : Γ(X, W) => a • (N.presheaf.map (homOfLE hWU).op s : Γ(N, W))) := by
    intro W hWU a b hab
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun V : ιW W => (V.1 : X.Opens)) W (fun V => homOfLE V.2) (hcov W)
    intro V
    apply (h V.1 (V.2.trans hWU)).1
    show X.presheaf.map (homOfLE V.2).op a • N.presheaf.map (homOfLE (V.2.trans hWU)).op s =
      X.presheaf.map (homOfLE V.2).op b • N.presheaf.map (homOfLE (V.2.trans hWU)).op s
    rw [← resN hWU V.2 s, ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul]
    exact congrArg (N.presheaf.map (homOfLE V.2).op) hab
  intro W hWU _
  refine ⟨hinj W hWU, fun y => ?_⟩

  have hloc : ∀ V : ιW W, ∃ a : Γ(X, V.1),
      a • N.presheaf.map (homOfLE (V.2.trans hWU)).op s = N.presheaf.map (homOfLE V.2).op y :=
    fun V => (h V.1 (V.2.trans hWU)).2 _
  choose a ha using hloc

  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun V : ιW W => (V.1 : X.Opens)) a := by
    intro i j
    apply hinj ((i.1 : X.Opens) ⊓ j.1) ((inf_le_left.trans i.2).trans hWU)
    have e1 : X.presheaf.map (homOfLE (inf_le_left : (i.1 : X.Opens) ⊓ j.1 ≤ i.1)).op (a i) •
        N.presheaf.map (homOfLE ((inf_le_left.trans i.2).trans hWU)).op s =
          N.presheaf.map (homOfLE ((inf_le_left : (i.1 : X.Opens) ⊓ j.1 ≤ i.1).trans i.2)).op y := by
      rw [← resN (i.2.trans hWU) inf_le_left s, ← Scheme.Modules.map_smul, ha i, resN]
    have e2 : X.presheaf.map (homOfLE (inf_le_right : (i.1 : X.Opens) ⊓ j.1 ≤ j.1)).op (a j) •
        N.presheaf.map (homOfLE ((inf_le_left.trans i.2).trans hWU)).op s =
          N.presheaf.map (homOfLE ((inf_le_left : (i.1 : X.Opens) ⊓ j.1 ≤ i.1).trans i.2)).op y := by
      rw [← resN (j.2.trans hWU) inf_le_right s, ← Scheme.Modules.map_smul, ha j, resN]
    exact e1.trans e2.symm
  have hglue : ∃ g : Γ(X, W), ∀ V : ιW W, X.presheaf.map (homOfLE V.2).op g = a V := by
    obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun V : ιW W => (V.1 : X.Opens)) W
      (fun V => homOfLE V.2) (hcov W) a hcompat
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hglue
  refine ⟨g, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' shN (fun V : ιW W => (V.1 : X.Opens)) W (fun V => homOfLE V.2) (hcov W)
  intro V
  show N.presheaf.map (homOfLE V.2).op (g • N.presheaf.map (homOfLE hWU).op s) = N.presheaf.map (homOfLE V.2).op y
  rw [Scheme.Modules.map_smul, resN, ← ha V]
  exact congrArg (fun b : Γ(X, V.1) => b • N.presheaf.map (homOfLE (V.2.trans hWU)).op s) (hg V)

end S_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul (solution)
