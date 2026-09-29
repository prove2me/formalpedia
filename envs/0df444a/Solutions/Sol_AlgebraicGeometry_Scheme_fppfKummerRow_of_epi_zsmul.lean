-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.fppfKummerRow_of_epi_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bcb50dc3-f17a-53e7-81d0-2fd07af58c2f

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Abelian"

theorem solution
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (hn : Epi (n • 𝟙 G)) :
    ∃ hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact,
      (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
          fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1).ker =
        (n • AddMonoidHom.id (fppfCohomology specInt G 0)).range ∧
      Function.Exact
        (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
          fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1)
        (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1) ∧
      (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1).range =
        AddMonoidHom.ker (n • AddMonoidHom.id (fppfCohomology specInt G 1)) := by
  haveI := hn
  set S := ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G)) with hSdef
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      (by change Mono (kernel.ι (n • 𝟙 G)); infer_instance) (by change Epi (n • 𝟙 G); infer_instance)
  obtain ⟨-, -, hex3, hex1, hex2⟩ := FppfCohomologyLES.sixTermLES hS

  have hmul : ∀ (k : ℕ) (x : G.H k), FppfCohomologyLES.cohomologyMap (n • 𝟙 G) k x = n • x := by
    intro k x
    let L : (G ⟶ G) →+ G.H k := AddMonoidHom.mk' (fun φ => FppfCohomologyLES.cohomologyMap φ k x)
      (fun a b => by
        simp only [FppfCohomologyLES.cohomologyMap_apply]
        rw [Ext.mk₀_add, Ext.comp_add])
    have h1 : L (n • 𝟙 G) = n • L (𝟙 G) := map_zsmul L n (𝟙 G)
    have h2 : L (𝟙 G) = x := FppfCohomologyLES.cohomologyMap_id G k x
    change L (n • 𝟙 G) = n • x
    rw [h1, h2]
  refine ⟨hS, ?_, ?_, ?_⟩
  ·
    ext x
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (hex3 x).mp hx
      refine ⟨y, ?_⟩
      change n • (AddMonoidHom.id _ y) = x
      rw [AddMonoidHom.id_apply, ← hmul 0 y]
      exact hy
    · rintro ⟨y, rfl⟩
      apply (hex3 _).mpr
      refine ⟨y, ?_⟩
      change FppfCohomologyLES.cohomologyMap (n • 𝟙 G) 0 y = n • (AddMonoidHom.id _ y)
      rw [hmul 0 y, AddMonoidHom.id_apply]
      rfl
  ·
    exact hex1
  ·
    ext x
    rw [AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      have h := (hex2 (FppfCohomologyLES.cohomologyMap S.f 1 y)).mpr ⟨y, rfl⟩
      rw [hmul 1] at h
      exact h
    · intro hx
      have hx' : FppfCohomologyLES.cohomologyMap (n • 𝟙 G) 1 x = 0 := by
        rw [hmul 1 x]; exact hx
      exact (hex2 x).mp hx'

end S_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul (solution)
