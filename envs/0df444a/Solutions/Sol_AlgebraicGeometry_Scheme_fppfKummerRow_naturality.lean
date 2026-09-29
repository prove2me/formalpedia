-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.fppfKummerRow_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fd1b36cf-4997-5795-b46f-6f608502671c

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_fppfKummerRow_naturality

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem solution
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ)
    (hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact)
    (t : G ⟶ G) :
    ∃ w : (n • 𝟙 G) ≫ t = t ≫ (n • 𝟙 G),
      (∀ x : fppfCohomology specInt G 0,
        (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
            fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1)
          (fppfCohomologyMap specInt t 0 x) =
        fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w) 1
          ((FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
            fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1) x)) ∧
      (∀ y : fppfCohomology specInt (kernel (n • 𝟙 G)) 1,
        fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1
            (fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w) 1 y) =
          fppfCohomologyMap specInt t 1 (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1 y)) := by
  have w : (n • 𝟙 G) ≫ t = t ≫ (n • 𝟙 G) := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]
  refine ⟨w, ?_, ?_⟩
  · intro x
    let S := ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))
    let φ : S ⟶ S :=
      { τ₁ := kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w
        τ₂ := t
        τ₃ := t
        comm₁₂ := by simp [S]
        comm₂₃ := w.symm }
    exact FppfCohomologyLES.cohomologyδ_naturality hS hS φ 0 1 rfl x
  · intro y
    rw [← fppfCohomologyMap_comp, ← fppfCohomologyMap_comp, kernel.lift_ι]

end S_AlgebraicGeometry_Scheme_fppfKummerRow_naturality
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_fppfKummerRow_naturality (solution)
