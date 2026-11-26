-- Prove2me | Definitions.Def_Eden_Divergence
-- name    : Eden_Divergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:19:08.289691+00:00
-- url     : https://prove2.me/theorems/fff444e1-a112-4250-b9d6-7a78e5c3d03e
-- title:
--   Divergence
-- statement:
--   Definitions and structural lemmas for Divergence, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean

import Definitions.Def_Eden_VectorFieldDerivative
set_option autoImplicit true
noncomputable section
namespace Eden
def divergence (c : ℝ) (p : PhaseSpace) : ℝ :=
  LinearMap.trace ℝ PhaseSpace (fderiv ℝ (vectorField c) p).toLinearMap
end Eden


