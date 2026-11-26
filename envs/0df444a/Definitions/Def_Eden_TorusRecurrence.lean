-- Prove2me | Definitions.Def_Eden_TorusRecurrence
-- name    : Eden_TorusRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:26:04.527894+00:00
-- url     : https://prove2.me/theorems/bfe48eaf-1918-5f63-b05f-a04cf6eaac6c
-- title:
--   Torus Recurrence
-- statement:
--   Definitions and structural lemmas for Torus Recurrence, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusRecurrence.lean

import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy
import Theorems.Thm_Eden_torus_invariant_all_real

set_option autoImplicit true
noncomputable section
open Set Filter Topology
namespace Eden
def torusEvolution (c t : ℝ) (p : torus) : torus :=
  ⟨evolution c t p, torus_invariant_all_real c t p.property⟩
end Eden


