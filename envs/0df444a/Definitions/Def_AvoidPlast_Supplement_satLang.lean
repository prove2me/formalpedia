-- Prove2me | Definitions.Def_AvoidPlast_Supplement_satLang
-- name    : AvoidPlast_Supplement_satLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:52:13.371196+00:00
-- url     : https://prove2.me/theorems/c7c04d4a-dd94-4271-b52d-99f1d74bfb15
-- title:
--   SAT under the fixed CNF encoding
-- statement:
--   A string is in SAT if the CNF it encodes (records grouped into clauses at the end-of-clause flags; trailing literals form a last clause) has an assignment $\sigma$ satisfying a literal of every clause. The empty record list is the empty, satisfiable CNF.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.9, p.25

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_cnfRecords

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The language SAT under the fixed encoding `cnfRecords` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.9, p.25): a literal
record with the end-of-clause flag closes its clause (trailing literals form a last clause), and
the CNF is satisfiable, i.e. some assignment `σ` makes a literal `(v, s)` (`σ v = s`) of every
clause true. Every string decodes to a CNF; the empty record list is the empty (true) CNF. -/
def satLang : Set (List Bool) :=
  {c | ∃ σ : ℕ → Bool, ∀ cl ∈ (cnfRecords c).foldr (fun r cls =>
      if r.2.2 then [(r.1, r.2.1)] :: cls else
        match cls with
        | [] => [[(r.1, r.2.1)]]
        | cl :: rest => ((r.1, r.2.1) :: cl) :: rest) [],
      ∃ l ∈ cl, σ l.1 = l.2}

end AvoidPlast.Supplement


