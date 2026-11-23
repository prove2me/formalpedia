-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:22.964809+00:00
-- url     : https://prove2.me/theorems/86bb6c16-3edb-4568-aca4-d76d3211b7cd
-- title:
--   Torsion Killed Criterion Holds
-- statement:
--   Definitions and structural lemmas for Torsion Killed Criterion Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/TorsionKilledCriterionHolds.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
section Claim
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
def QS (W : WachMod B M D) : Submodule O D where
  carrier := {y | B.Q ^ M • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.Q ^ M • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.Q ^ M • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.Q ^ M • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy
end Claim
end Formalism.CoboundaryTransfers


