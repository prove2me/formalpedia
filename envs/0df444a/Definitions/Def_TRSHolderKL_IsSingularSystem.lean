-- Prove2me | Definitions.Def_TRSHolderKL_IsSingularSystem
-- name    : TRSHolderKL_IsSingularSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:57.74599+00:00
-- url     : https://prove2.me/theorems/cbd9720a-68a5-45d9-970b-9de8c60a50a5
-- title:
--   Singular system (Definition 3.1)
-- statement:
--   A (sub)system of inequalities is **singular** if every inequality in it is singular with respect to the solution set of that (sub)system.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definition 3.1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_IsSingularIn
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Definition 3.1, p.4: the (sub)system indexed by `T` is singular if every inequality in it
is singular. -/
def IsSingularSystem {n m : ℕ} (q : Fin m → E n → ℝ) (T : Finset (Fin m)) : Prop :=
  ∀ i ∈ T, IsSingularIn q T i

end TRSHolderKL


