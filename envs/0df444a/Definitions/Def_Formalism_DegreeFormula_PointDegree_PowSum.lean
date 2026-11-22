-- Prove2me | Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
-- name    : Formalism_DegreeFormula_PointDegree_PowSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:16.809801+00:00
-- url     : https://prove2.me/theorems/d7bf9ce8-5487-4ec1-88a3-21ec3a19d601
-- title:
--   Pow Sum
-- statement:
--   Definitions and structural lemmas for Pow Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
def sgnP {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) : ℝ :=
  ∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)
end Formalism.DegreeFormula.PPowSum
namespace Formalism.DegreeFormula
end Formalism.DegreeFormula


