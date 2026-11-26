-- Prove2me | Definitions.Def_Eden_InitialDerivative
-- name    : Eden_InitialDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:42.643363+00:00
-- url     : https://prove2.me/theorems/a0ddaf4e-4a91-50de-9d45-a0a73228156a
-- title:
--   Initial Derivative
-- statement:
--   Definitions and structural lemmas for Initial Derivative, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean

import Definitions.Def_Eden_Evolution
set_option autoImplicit true
noncomputable section
namespace Eden
def radialAmplitude (t s : ℝ) : ℝ :=
  Real.exp (-4 * t) /
    (planarAmplitude t s * Real.sqrt (radialDiscriminant t s) ^ 3)
end Eden


