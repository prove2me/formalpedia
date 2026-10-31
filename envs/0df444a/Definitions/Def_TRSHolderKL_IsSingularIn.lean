-- Prove2me | Definitions.Def_TRSHolderKL_IsSingularIn
-- name    : TRSHolderKL_IsSingularIn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:09.306984+00:00
-- url     : https://prove2.me/theorems/8054cb12-9f65-49c0-96fc-18f6eb03f3ab
-- title:
--   Singular inequality (Definition 3.1)
-- statement:
--   In the (sub)system indexed by $T$, the inequality $q_i(x)\le0$ is **singular** if $q_i(x)=0$ for every solution $x$ of that system; it is nonsingular if some solution $x_i$ has $q_i(x_i)<0$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definition 3.1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_solSet
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Definition 3.1, Jiang and Li, arXiv:1911.11955v2, p.4: in the (sub)system indexed by `T`,
the inequality `qᵢ(x) ≤ 0` is singular if `qᵢ(x) = 0` for every solution `x` of that system. -/
def IsSingularIn {n m : ℕ} (q : Fin m → E n → ℝ) (T : Finset (Fin m)) (i : Fin m) : Prop :=
  ∀ x ∈ solSet q T, q i x = 0

end TRSHolderKL


