-- Prove2me | Definitions.Def_Eden_GlobalGrowthLimits
-- name    : Eden_GlobalGrowthLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:38:51.751682+00:00
-- url     : https://prove2.me/theorems/75891882-95ff-4dad-ada3-54416b271c86
-- title:
--   Global Growth Limits
-- statement:
--   Definitions and structural lemmas for Global Growth Limits, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean

import Definitions.Def_Eden_RealSubadditive
set_option autoImplicit true
noncomputable section
open Set Filter Topology
namespace Eden
def globalGrowthRate (c : ℝ) (k : ℕ) : ℝ :=
  limUnder atTop (fun t : ℝ => globalLogGrowth c k t / t)
end Eden


