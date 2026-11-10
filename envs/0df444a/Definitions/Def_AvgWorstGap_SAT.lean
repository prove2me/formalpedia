-- Prove2me | Definitions.Def_AvgWorstGap_SAT
-- name    : AvgWorstGap_SAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:58.411418+00:00
-- url     : https://prove2.me/theorems/b567f956-f38e-4c38-b202-4b300bd974f9
-- title:
--   The language SAT
-- statement:
--   A CNF formula is a list of clauses, and a clause is a list of literals (variable index, polarity). A formula is **satisfiable** if some assignment makes at least one literal of every clause true. The formula is encoded as a binary string: a literal is $\mathrm{bin}(\text{variable})$ followed by its polarity bit, a clause is the tuple encoding of its literals, and the formula is the tuple encoding of its clauses. **SAT** is the set of encodings of satisfiable formulas.
--
--   **Formalization Note** One fixed language with one fixed encoding, as the paper uses one language SAT.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemmas 3.4 and 3.8, pp.20, 24

import Mathlib
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_AvgWorstGap_pairStr

namespace AvgWorstGap

open NKtLB

/-- A CNF formula: a list of clauses, each a list of literals `(variable, polarity)`. -/
abbrev CNF := List (List (ℕ × Bool))

/-- A CNF formula is **satisfiable** if some assignment makes a literal of every clause true. -/
def CNF.Satisfiable (φ : CNF) : Prop :=
  ∃ σ : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2

/-- The binary encoding of a CNF formula: each literal is `bin(variable) ++ [polarity]`, a clause
is the `tupleEnc` of its literals, the formula is the `tupleEnc` of its clauses. -/
def encCNF (φ : CNF) : List Bool :=
  tupleEnc (φ.map (fun c => tupleEnc (c.map (fun l => bin l.1 ++ [l.2]))))

/-- **SAT** (arXiv:2610.19162, version of October 30, 2026, Lemmas 3.4 and 3.8, pp.20, 24): the
binary encodings of satisfiable CNF formulas.

**Formalization Note.** One fixed language with the fixed encoding `encCNF` (the paper fixes no
encoding). -/
def SAT : Set (List Bool) := {u | ∃ φ : CNF, u = encCNF φ ∧ φ.Satisfiable}

end AvgWorstGap


