-- Prove2me | Definitions.Def_HSElemKernel_IsDHS
-- name    : HSElemKernel_IsDHS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:40.755482+00:00
-- url     : https://prove2.me/theorems/34f3c84b-d7f5-4a34-b761-ab0cba788971
-- title:
--   $d$-Hitting Set instance: $|A| \le d$ for all $A \in \mathcal S$
-- statement:
--   An instance $(U, \mathcal S, k)$ is an instance of **$d$-Hitting Set** if every input set has at most $d$ elements:
--   $$|A| \le d \quad\text{for every } A \in \mathcal S.$$
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3, p.6

import Mathlib
import Definitions.Def_HSElemKernel_HSInstance

namespace HSElemKernel

/-- The instance is an instance of `d`-Hitting Set: every input set has at most `d` elements
(Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…, Section 3, p.6: "An instance of
d-Hitting Set consists of such a set system with |A| ≤ d for every A ∈ S"). -/
def IsDHS (d : ℕ) (I : HSInstance) : Prop :=
  ∀ A ∈ I.S, A.card ≤ d

end HSElemKernel


