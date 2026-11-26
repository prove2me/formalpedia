-- Prove2me | Definitions.Def_Eden_ScalarCalculus
-- name    : Eden_ScalarCalculus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:19.427393+00:00
-- url     : https://prove2.me/theorems/d25943b1-1860-4922-9cc9-2fc11729724c
-- title:
--   Scalar Calculus
-- statement:
--   Definitions and structural lemmas for Scalar Calculus, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
namespace Eden
def planarAmplitude (t s : ℝ) : ℝ := Real.sqrt (amplitudeSq t s)
end Eden


