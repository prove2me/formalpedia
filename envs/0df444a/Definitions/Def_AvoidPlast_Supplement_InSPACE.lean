-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InSPACE
-- name    : AvoidPlast_Supplement_InSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:47:50.092884+00:00
-- url     : https://prove2.me/theorems/e2451f35-1049-48dc-b273-b670490e4120
-- title:
--   The class $\mathrm{SPACE}[s(n)]$
-- statement:
--   A language $L$ is in $\mathrm{SPACE}[s(n)]=\mathrm{DSPACE}[s(n)]$ if a deterministic machine that halts on every input and uses work space at most $C\cdot(s(n)+1)$ on $n$-bit inputs accepts exactly the strings of $L$. The input and the output tape are not work space.
--
--   **Formalization Note** Space bounds are $O(s(n))$, the mission's convention (reading R2).
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3.4, p.16; Theorems 1.4, 5.10, pp.4, 26

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_SpaceO

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `L ∈ SPACE[s(n)] = DSPACE[s(n)]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3.4, p.16; Theorems 1.4, 5.10, pp.4, 26): a
deterministic machine of space `O(s(n))` (the base `SpaceO`, which halts on every input; reading R2)
decides `L`. -/
def InSPACE (s : ℕ → ℝ) (L : Set (List Bool)) : Prop :=
  ∃ M : Machine 1, SpaceO M s ∧ ∀ x : List Bool, Accepts M ![x] ↔ x ∈ L

end AvoidPlast.Supplement


