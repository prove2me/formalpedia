-- Prove2me | Definitions.Def_AvoidPlast_Supplement_OneWayTape
-- name    : AvoidPlast_Supplement_OneWayTape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:14:23.530108+00:00
-- url     : https://prove2.me/theorems/e3530650-1ca4-43bc-9dca-11cca3c0f529
-- title:
--   One-way read-only tapes
-- statement:
--   The head on a read-only tape only moves right or stays: the co-non-deterministic choices of a space-bounded machine are read once, so storing them costs work space.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.3, p.40

import Mathlib
import Definitions.Def_AvoidPlast_HeadAct
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The head on read-only tape `j` only moves right or stays (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 7.3, p.40): the
co-non-deterministic choices of a space-bounded machine are read once, so storing them costs work
space. -/
def OneWayTape {r : ℕ} (M : Machine r) (j : Fin r) : Prop :=
  ∀ s a b, (M.δ s a b).2.2.1 j = HeadAct.move .stay ∨ (M.δ s a b).2.2.1 j = HeadAct.move .right

end AvoidPlast.Supplement


