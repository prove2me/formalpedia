-- Prove2me | Definitions.Def_Eden_PlanarVectorField
-- name    : Eden_PlanarVectorField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:19:30.187904+00:00
-- url     : https://prove2.me/theorems/bce838e4-195b-5921-83ba-dd2228726b7b
-- title:
--   Planar Vector Field
-- statement:
--   Definitions and structural lemmas for Planar Vector Field, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarVectorField.lean

import Definitions.Def_Eden_VectorFieldDerivative
set_option autoImplicit true
noncomputable section
namespace Eden
abbrev PlanarSpace := EuclideanSpace ℝ (Fin 2)
def planarVectorField (Ω : ℝ) (p : PlanarSpace) : PlanarSpace :=
  !₂[q (p 0 ^ 2 + p 1 ^ 2) * p 0 - Ω * p 1,
    q (p 0 ^ 2 + p 1 ^ 2) * p 1 + Ω * p 0]
end Eden


