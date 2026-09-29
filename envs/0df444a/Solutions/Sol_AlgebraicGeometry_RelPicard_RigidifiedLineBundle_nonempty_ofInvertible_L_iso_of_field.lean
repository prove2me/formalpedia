-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c0abc077-c774-5a28-9969-67d50ccdc34b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry"
open AlgebraicGeometry.RelPicard NeronModelInfra

namespace R2Aux

open AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 1600000 in

theorem nonempty_iso_unit_of_isFrameOn_top {X : Scheme.{u}} {N : X.Modules} (s : Γ(N, ⊤))
    (hs : IsFrameOn s ⊤) : Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨θ, hθ, -⟩ := IsFrameOn.existsUnique_ihomEval_eq
    (isFrameOn_unitSection (X := X) (U := ⊤) ⊤) s
  let μ : 𝟙_ X.Modules ⟶ N := ihomGlobalSectionsEquiv (𝟙_ X.Modules) N θ
  have hμ : μ.app ⊤ (unitSection ⊤) = s := by
    rw [ihomGlobalSectionsEquiv_app_apply]
    have e : ((ihom (𝟙_ X.Modules)).obj N).presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op θ = θ := by
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _), op_id, CategoryTheory.Functor.map_id]; rfl
    rw [e]
    exact hθ
  haveI : IsIso μ := isIso_of_isFrameOn_of_iSup_eq_top μ (fun _ : Unit => (⊤ : X.Opens))
    (by rw [iSup_const]) (fun _ => unitSection ⊤) (fun _ => s)
    (fun _ => isFrameOn_unitSection (X := X) (U := ⊤) ⊤) (fun _ => hs) (fun _ => hμ)
  exact ⟨(asIso μ).symm⟩

set_option maxHeartbeats 1600000 in

theorem nonempty_iso_unit_of_field {K : Type u} [Field K] {N : (Spec (CommRingCat.of K)).Modules}
    (hN : IsInvertible N) : Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) := by
  obtain ⟨U, s, hx, hs⟩ := hN.exists_isFrameOn (IsLocalRing.closedPoint K)
  have hU : U = ⊤ := by
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    have : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [this]; exact hx
  subst hU
  exact nonempty_iso_unit_of_isFrameOn_top s hs

end R2Aux

set_option maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {L : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅ L) := by
  obtain ⟨r⟩ := R2Aux.nonempty_iso_unit_of_field (hL.pullback (rigSection c t ε))
  let M : RigidifiedLineBundle c ε t := ⟨L, hL, ⟨r⟩⟩
  exact RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field (solution)
