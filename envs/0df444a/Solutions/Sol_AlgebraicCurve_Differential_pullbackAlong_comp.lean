-- Prove2me | solution 1 for AlgebraicCurve.Differential.pullbackAlong_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7317b81c-858c-514b-a5d4-a8b27b43ae49

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Differential_pullbackAlong_comp

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential

theorem solution
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (ψ.comp φ) ω =
      AlgebraicCurve.Differential.pullbackAlong ψ (AlgebraicCurve.Differential.pullbackAlong φ ω) := by
  have key : ∀ ω ∈ Submodule.span F (Set.range (D K F)),
      pullbackAlong (ψ.comp φ) ω = pullbackAlong ψ (pullbackAlong φ ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      rw [pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, AlgHom.comp_apply]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
    | smul a x _ hx => rw [pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, hx, AlgHom.comp_apply]
  exact key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial)

end S_AlgebraicCurve_Differential_pullbackAlong_comp
end P2MW
export P2MW.S_AlgebraicCurve_Differential_pullbackAlong_comp (solution)
