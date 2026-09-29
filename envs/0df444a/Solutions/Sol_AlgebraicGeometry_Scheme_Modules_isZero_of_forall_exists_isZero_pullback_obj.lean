-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isZero_of_forall_exists_isZero_pullback_obj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/19edadf3-e0aa-5773-b3cd-05203698078f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom.id_app Hom Γ Hom.app Hom.image_preimage_eq_opensRange_inf restrictFunctor Modules Opens Opens.opensRange_ι"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.zero_app pullback presheaf Hom restrictFunctor Hom.id_app Hom.app restrictFunctorIsoPullback isSheaf"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma sections_eq_zero_of_isZero_pullback_ι {M : X.Modules} (U : X.Opens)
    (hU : IsZero ((Scheme.Modules.pullback U.ι).obj M)) (W : X.Opens) (hWU : W ≤ U)
    (s : Γ(M, W)) : s = 0 := by
  have h1 : IsZero ((restrictFunctor U.ι).obj M) :=
    hU.of_iso ((restrictFunctorIsoPullback U.ι).app M)
  have h2 : (𝟙 ((restrictFunctor U.ι).obj M) :) = 0 := h1.eq_of_src _ _
  have h4 : ∀ t : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)), t = 0 := fun t => by
    have h3 := congrArg (fun ψ => (Hom.app ψ (U.ι ⁻¹ᵁ W) : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) → _) t) h2
    simp only [Hom.id_app, Hom.zero_app] at h3
    exact h3
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  let i : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⟶ W := homOfLE e.le
  let j : W ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := homOfLE e.ge
  have hij : j ≫ i = 𝟙 W := Subsingleton.elim _ _
  calc s = M.presheaf.map (𝟙 (op W)) s := by simp
    _ = M.presheaf.map (j ≫ i).op s := by rw [hij]; rfl
    _ = M.presheaf.map j.op (M.presheaf.map i.op s) := by
      rw [op_comp, M.presheaf.map_comp]; rfl
    _ = 0 := by rw [h4 (M.presheaf.map i.op s), map_zero]

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj.solution (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsZero ((Scheme.Modules.pullback U.ι).obj M)) :
    IsZero M := by
  choose U hxU hU using h
  have hsec : ∀ (W : X.Opens) (s : Γ(M, W)), s = 0 := by
    intro W s
    let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
    let V : W → X.Opens := fun x => W ⊓ U x.1
    refine F.eq_of_locally_eq' V W (fun x => homOfLE inf_le_left)
      (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx, hxU x⟩) s 0 fun x => ?_
    rw [map_zero]
    exact sections_eq_zero_of_isZero_pullback_ι (U x.1) (hU x.1) (W ⊓ U x.1) inf_le_right _
  rw [IsZero.iff_id_eq_zero]
  ext W s
  simpa using hsec W s

#print axioms solution

end AlgebraicGeometry.Scheme.Modules

end S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj (solution)
