-- Prove2me | Definitions.Def_Eden_VectorFieldDerivative
-- name    : Eden_VectorFieldDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:18:22.585041+00:00
-- url     : https://prove2.me/theorems/bce1039c-9d8e-46bf-a6f7-f470c32b1e89
-- title:
--   Vector Field Derivative
-- statement:
--   Definitions and structural lemmas for Vector Field Derivative, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
set_option autoImplicit true
noncomputable section
namespace Eden
section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}
end Composition
end Eden


