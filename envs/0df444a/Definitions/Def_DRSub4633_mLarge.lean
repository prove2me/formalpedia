-- Prove2me | Definitions.Def_DRSub4633_mLarge
-- name    : DRSub4633_mLarge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:05.595698+00:00
-- url     : https://prove2.me/theorems/27f16592-49ec-412f-8286-c34f619f814f
-- title:
--   The number $m=|L|$ of large coordinates
-- statement:
--   For the state $x$, $m=|L|=1+\#\{j: x_j>s\}$: the number of large coordinates, counting the dummy coordinate. In particular $m\ge 1$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.10

import Mathlib
import Definitions.Def_DRSub4633_sPar

namespace DRSub4633

/-- **The number `m = |L|` of large coordinates, dummy included.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1,
p.10: "From here on `L` includes the dummy coordinate, so the formulas below have `m = |L| ≥ 1`."
Here `L = {j : x_j > s}` plus the dummy. -/
noncomputable def mLarge {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  1 + (Finset.univ.filter (fun k : Fin n => sPar < x k)).card

end DRSub4633


