-- Prove2me | Definitions.Def_Eden_PhysicalRadius
-- name    : Eden_PhysicalRadius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:09:55.645929+00:00
-- url     : https://prove2.me/theorems/15f22ce4-fdc6-5c91-ad4b-edbc1ae3b1f9
-- title:
--   Physical Radius
-- statement:
--   Definitions and structural lemmas for Physical Radius, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
namespace Eden
def radiusEvolution (t r : ℝ) : ℝ := Real.sqrt (squaredRadiusEvolution t (r ^ 2))
end Eden


