-- Prove2me | Definitions.Def_TRSHolderKL_IsIrregular
-- name    : TRSHolderKL_IsIrregular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:54:16.776478+00:00
-- url     : https://prove2.me/theorems/84ed4163-e936-4f50-b47d-bb8274a4a7c9
-- title:
--   Irregular inequality (Definition 3.3)
-- statement:
--   An inequality of a system is **irregular** if it is nonlinear, singular (in the whole system), and contained in no critical subsystem.
--
--   **Formalization Note** A subsystem is any set of indices containing the inequality (the whole system included), judged against its own solution set as in the definition of a critical subsystem.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definition 3.3, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_IsNonlinear
import Definitions.Def_TRSHolderKL_IsSingularIn
import Definitions.Def_TRSHolderKL_IsCritical
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Definition 3.3, Jiang and Li, arXiv:1911.11955v2, p.5: an inequality of the system is
irregular if it is nonlinear, singular, and contained in no critical subsystem.

**Formalization Note.** Singular refers to the whole system `[m]`; a subsystem is any subset
`T ∋ i` of the inequalities (including the whole system), judged as in `IsCritical`. -/
def IsIrregular {n m : ℕ} (q : Fin m → E n → ℝ) (i : Fin m) : Prop :=
  IsNonlinear (q i) ∧ IsSingularIn q Finset.univ i ∧
    ∀ T : Finset (Fin m), i ∈ T → ¬ IsCritical q T

end TRSHolderKL


