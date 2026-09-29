-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/67ac0504-902c-5c4a-b02d-2c67efcf2051

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {X X' : Scheme.{u}} (c : X' ⟶ X) [Surjective c]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) {N : ℕ} (σ : Fin (N + 1) → Γ(L, ⊤))

    (σ' : Fin (N + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (hσ' : ∀ l, σ' l = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤) (σ l))
    {M : ℕ} (ρ : Fin (M + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (U' : Fin (M + 1) → X'.Opens) (hU' : iSup U' = ⊤)
    (hframe' : ∀ (j : Fin (M + 1)) (V' : X'.Opens), V' ≤ U' j →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback c).obj L).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (ρ j) :
          Γ((Scheme.Modules.pullback c).obj L, V')))
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → Γ(X', ⊤), ρ j = ∑ l, a l • σ' l) :
    ∃ U : Fin (N + 1) → X.Opens, iSup U = ⊤ ∧
      ∀ (l : Fin (N + 1)) (V : X.Opens), V ≤ U l →
        Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l) : Γ(L, V)) := by
  classical

  have hpt : ∀ x : X, ∃ (l : Fin (N + 1)) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l) : Γ(L, V)) := by
    intro x
    obtain ⟨x', hx'⟩ := c.surjective x
    have hx'top : x' ∈ (⊤ : X'.Opens) := trivial
    rw [← hU'] at hx'top
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'top
    obtain ⟨a, ha⟩ := hspan j
    obtain ⟨l, U'', hxU'', hfr⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_sum_smul ((Scheme.Modules.pullback c).obj L) a σ' x'
        ⟨U' j, hj, fun V' hV' => by
          have h := hframe' j V' hV'
          rw [ha] at h
          exact h⟩
    obtain ⟨U, hxU, hU⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback c L hL (σ l) x'
        ⟨U'', hxU'', fun V' hV' => by
          have h := hfr V' hV'
          rw [hσ' l] at h
          exact h⟩
    refine ⟨l, U, ?_, hU⟩
    rw [← hx']
    exact hxU

  let good : Fin (N + 1) → Set X.Opens := fun l =>
    {W | ∀ V : X.Opens, V ≤ W →
      Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l) : Γ(L, V))}
  refine ⟨fun l => sSup (good l), ?_, ?_⟩
  · refine le_antisymm le_top fun x _ => ?_
    obtain ⟨l, U, hxU, hU⟩ := hpt x
    have hle : U ≤ sSup (good l) := le_sSup (show U ∈ good l from hU)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, hle hxU⟩
  · intro l V hV
    apply AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul L (σ l) V
    intro x hx
    obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp (hV hx)
    exact ⟨W, hxW, hW⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective (solution)
