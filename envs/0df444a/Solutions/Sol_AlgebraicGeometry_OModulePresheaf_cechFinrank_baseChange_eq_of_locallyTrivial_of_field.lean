-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinrank_baseChange_eq_of_locallyTrivial_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d59da19c-7618-5fba-8459-b299d5452a9f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_baseChange_eq_of_locallyTrivial_of_field
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {k₀ : Type u} [Field k₀] {X : Scheme.{u}} (π : X ⟶ Spec (.of k₀)) [IsSeparated π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (k : Type u) [Field k] [Algebra k₀ k] (n : ℕ) :
    (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k₀ k))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap k₀ k))).obj M)).cechFinrank (𝒰.baseChange π k) n =
      (OModulePresheaf.ofModules π M).cechFinrank 𝒰 n := by
  obtain ⟨-, hflat⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv k
  obtain ⟨⟨e0⟩, eS⟩ := hflat inferInstance
  cases n with
  | zero =>
    rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero, e0.finrank_eq, Module.finrank_baseChange]
  | succ i =>
    obtain ⟨e⟩ := eS i
    rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ, e.finrank_eq, Module.finrank_baseChange]

end S_AlgebraicGeometry_OModulePresheaf_cechFinrank_baseChange_eq_of_locallyTrivial_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_baseChange_eq_of_locallyTrivial_of_field (solution)
