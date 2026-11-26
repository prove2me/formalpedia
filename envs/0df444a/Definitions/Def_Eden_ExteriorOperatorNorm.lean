-- Prove2me | Definitions.Def_Eden_ExteriorOperatorNorm
-- name    : Eden_ExteriorOperatorNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:33:05.348836+00:00
-- url     : https://prove2.me/theorems/b7c3b12d-4336-5b71-a64c-d89d5e168a51
-- title:
--   Exterior Operator Norm
-- statement:
--   Definitions and structural lemmas for Exterior Operator Norm, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def exteriorOperator (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ExteriorSpace k →L[ℝ] ExteriorSpace k :=
  (exteriorPower.map k A).toContinuousLinearMap
end Eden


