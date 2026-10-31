-- Prove2me | Definitions.Def_TRSHolderKL_IsCritical
-- name    : TRSHolderKL_IsCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:53:04.836764+00:00
-- url     : https://prove2.me/theorems/68b92a1f-be78-4924-bc93-24cfcb0f5f35
-- title:
--   Critical subsystem (Definition 3.2)
-- statement:
--   A singular (sub)system $S$ of inequalities is **critical** if either
--   1. at most one of its inequalities is nonlinear; or
--   2. after any one of its nonlinear inequalities is deleted, all the remaining nonlinear inequalities become nonsingular.
--
--   **Formalization Note** A subsystem is judged against its own solution set: "become nonsingular" refers to the solutions of the system with the deleted inequality removed. This is the reading under which the paper's own computations hold (p.6: for system (3) "when either inequality in (3) is deleted, the remaining inequality is nonsingular"; p.7: "the only critical subsystem of (3) is the first inequality", giving degree 2).
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definition 3.2, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_IsNonlinear
import Definitions.Def_TRSHolderKL_IsSingularIn
import Definitions.Def_TRSHolderKL_IsSingularSystem
open RBMSensitivity (E)

namespace TRSHolderKL

open Classical in
/-- Definition 3.2, Jiang and Li, arXiv:1911.11955v2, p.5: a singular (sub)system `T` is
critical if at most one of its inequalities is nonlinear, or if after deleting any one
nonlinear inequality every remaining nonlinear inequality becomes nonsingular.

**Formalization Note.** A subsystem is judged against its **own** solution set: after deleting
`j`, nonsingularity of `k` refers to the solutions of the system `T \ {j}`. This is the reading
the paper's own computations use (p.6: in (3) "when either inequality is deleted, the
remaining inequality is nonsingular"; p.7: "the only critical subsystem of (3) is the first
inequality"). -/
def IsCritical {n m : ℕ} (q : Fin m → E n → ℝ) (T : Finset (Fin m)) : Prop :=
  IsSingularSystem q T ∧
    ((T.filter fun i => IsNonlinear (q i)).card ≤ 1 ∨
      ∀ j ∈ T, IsNonlinear (q j) → ∀ k ∈ T.erase j, IsNonlinear (q k) →
        ¬ IsSingularIn q (T.erase j) k)

end TRSHolderKL


