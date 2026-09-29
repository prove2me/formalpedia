-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/85df0db9-60f2-50c8-bad1-4a09df1c7eab

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace FrameL1Aux
variable {X : Scheme.{u}} {M : X.Modules}
theorem map_map {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

end FrameL1Aux

open AlgebraicGeometry.Scheme.Modules FrameL1Aux in
theorem solution
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type v} {s : Γ(M, U)}
    (V : ι → X.Opens) (h : ∀ i, Scheme.Modules.IsFrameOn s (V i)) :
    Scheme.Modules.IsFrameOn s (⨆ i, V i) := by
  intro W hWU hWV

  let Wi : ι → X.Opens := fun i => W ⊓ V i
  have hcov : W ≤ ⨆ i, Wi i := by
    intro x hx
    have hx' : x ∈ (⨆ i, V i : X.Opens) := hWV hx
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  let FM : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩
  set sW : Γ(M, W) := M.presheaf.map (homOfLE hWU).op s with hsW
  have key : ∀ i, Function.Bijective fun g : Γ(X, Wi i) =>
      g • (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW : Γ(M, Wi i)) := by
    intro i
    have := h i (W := Wi i) (inf_le_left.trans hWU) inf_le_right
    rw [hsW, map_map]
    exact this
  constructor
  · intro g g' hgg'
    simp only at hgg'
    apply X.sheaf.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcov
    intro i
    apply (key i).1
    change X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op g • _ =
      X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op g' • _
    rw [← M.map_smul, ← M.map_smul]
    exact congrArg _ hgg'
  · intro x

    have hloc : ∀ i, ∃! g : Γ(X, Wi i),
        g • (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW : Γ(M, Wi i)) =
          M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op x :=
      fun i => (Function.bijective_iff_existsUnique _).1 (key i) _
    choose g hg hguniq using hloc

    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Wi g := by
      intro i j

      have hb := h i (W := Wi i ⊓ Wi j) ((inf_le_left.trans inf_le_left).trans hWU)
        (inf_le_left.trans inf_le_right)
      apply hb.1
      simp only
      have e1 : M.presheaf.map (homOfLE ((inf_le_left.trans inf_le_left).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_left : Wi i ⊓ Wi j ≤ Wi i)).op
            (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW) := by
        rw [hsW, map_map, map_map]
      have e2 : M.presheaf.map (homOfLE ((inf_le_left.trans inf_le_left).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_right : Wi i ⊓ Wi j ≤ Wi j)).op
            (M.presheaf.map (homOfLE (inf_le_left : Wi j ≤ W)).op sW) := by
        rw [hsW, map_map, map_map]
      conv_lhs => rw [e1]
      conv_rhs => rw [e2]
      change X.presheaf.map (homOfLE inf_le_left).op (g i) • _ =
        X.presheaf.map (homOfLE inf_le_right).op (g j) • _
      rw [← M.map_smul, ← M.map_smul, hg i, hg j, map_map, map_map]
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' Wi W (fun i => homOfLE inf_le_left) hcov g hcomp
    let G' : Γ(X, W) := G
    refine ⟨G', ?_⟩
    simp only
    apply FM.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcov
    intro i
    change M.presheaf.map (homOfLE inf_le_left).op (G' • sW) = M.presheaf.map (homOfLE inf_le_left).op x
    rw [M.map_smul]
    have : X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op G' = g i := hG i
    rw [this, hg i]

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup (solution)
