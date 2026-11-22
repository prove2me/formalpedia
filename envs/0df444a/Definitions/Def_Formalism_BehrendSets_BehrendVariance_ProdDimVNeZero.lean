-- Prove2me | Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProdDimVNeZero
-- name    : Formalism_BehrendSets_BehrendVariance_ProdDimVNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:28.098805+00:00
-- url     : https://prove2.me/theorems/bcf93790-5373-476c-82d3-8d065ff7e1cb
-- title:
--   Prod Dim VNe Zero
-- statement:
--   Definitions and structural lemmas for Prod Dim VNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProdDimVNeZero.lean

import Definitions.Def_Formalism_BehrendSets_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
namespace Formalism.BehrendSets.Count
def F (n : ℕ) : ℝ := ∑ i ∈ range n, Real.log ((i.factorial : ℕ) : ℝ)
end Formalism.BehrendSets.Count
namespace Formalism.BehrendSets
open Formalism.BehrendSets.Count
end Formalism.BehrendSets


