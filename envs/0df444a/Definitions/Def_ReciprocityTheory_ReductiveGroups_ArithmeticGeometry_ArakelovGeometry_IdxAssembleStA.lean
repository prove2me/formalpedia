-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IdxAssembleStA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IdxAssembleStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:28.528546+00:00
-- url     : https://prove2.me/theorems/0257f34f-4af7-4875-9e18-7c9ee2c41744
-- title:
--   Idx Assemble St A
-- statement:
--   Definitions and structural lemmas for Idx Assemble St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IdxAssembleStA.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm
open Filter Asymptotics Finset
noncomputable def gPoly (D : ℕ) (c : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ i ∈ range (D + 1),
    c i * ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm


