-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/93566dac-725c-5abf-b31a-fb394ff93c90

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem solution
    {X : Scheme.{u}} [IsIntegral X] {ι : Type u} (V : ι → X.Opens) (W : X.Opens) (hV : iSup V = W)
    [hW : Nonempty W] [hVi : ∀ i, Nonempty (V i)]
    (f : X.functionField) (s : ∀ i, Γ(X, V i)) (hs : ∀ i, X.germToFunctionField (V i) (s i) = f) :
    ∃! t : Γ(X, W), X.germToFunctionField W t = f ∧
      ∀ i, X.presheaf.map (homOfLE (hV ▸ le_iSup V i : V i ≤ W)).op t = s i := by
  classical
  have hle : ∀ i, V i ≤ W := fun i => hV ▸ le_iSup V i

  have germ_res : ∀ {A B : X.Opens} (hA : Nonempty A) (hB : Nonempty B) (h : A ≤ B) (x : Γ(X, B)),
      @Scheme.germToFunctionField X _ A hA (X.presheaf.map (homOfLE h).op x) = @Scheme.germToFunctionField X _ B hB x := by
    intro A B _ _ h x
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) (genericPoint X) _ x

  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro i j
    by_cases hne : Nonempty ↥(V i ⊓ V j)
    · apply @Scheme.germToFunctionField_injective X _ (V i ⊓ V j) hne
      rw [show X.presheaf.map (Opens.infLELeft (V i) (V j)).op (s i) =
          X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i) from rfl,
        show X.presheaf.map (Opens.infLERight (V i) (V j)).op (s j) =
          X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j) from rfl,
        germ_res hne (hVi i), germ_res hne (hVi j), hs, hs]
    ·
      have hbot : V i ⊓ V j = ⊥ := by
        ext x
        simp only [Opens.coe_inf, Set.mem_inter_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxi hxj
        exact hne ⟨⟨x, ⟨hxi, hxj⟩⟩⟩
      haveI : Subsingleton Γ(X, V i ⊓ V j) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (by rw [hbot]))
      exact Subsingleton.elim _ _
  obtain ⟨t, ht, huniq⟩ := X.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i)) (le_of_eq hV.symm) s hcompat
  have ht' : ∀ i, X.presheaf.map (homOfLE (hle i)).op t = s i := ht
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : W = ⊥ := by rw [← hV, iSup_of_empty]
    obtain ⟨⟨x, hx⟩⟩ := hW
    rw [this] at hx
    exact hx
  refine ⟨t, ⟨?_, fun i => ht' i⟩, ?_⟩
  · rw [← germ_res (hVi i₀) hW (hle i₀) t, ht' i₀, hs]
  · rintro t' ⟨-, ht'⟩
    exact huniq t' ht'

end S_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq (solution)
