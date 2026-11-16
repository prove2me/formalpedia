-- Prove2me | Definitions.Def_NKtLB_Supplement_CNF
-- name    : NKtLB_Supplement_CNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:34:30.219944+00:00
-- url     : https://prove2.me/theorems/1be0806e-e434-4fcf-b5b0-04e81260a9d1
-- title:
--   CNF formulas, satisfiability and their binary encoding
-- statement:
--   A **CNF formula** is a list of clauses, each a list of literals $(v,b)$ (variable $v\in\mathbb N$; $b=1$ for $x_v$ and $b=0$ for $\neg x_v$). It is **satisfiable** if some assignment makes at least one literal of every clause true. The **encoding** of a formula lists its clauses, each the list of its literals, each the pair (binary representation of $v$, the bit $b$), using the base tuple encoding.
--
--   **Formalization Note** The paper fixes no encoding (p.22: "our results are robust with respect to encoding choices"). This one is uniquely decodable and of linear size.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), pp.8, 39, 96 (standard)

import Mathlib
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **CNF formulas** (for SAT and UNSAT, Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), pp.8, 39, 96; standard, not defined in the paper): a
list of clauses, each a list of literals `(v, b)` (variable `v`, sign `b`; `b = true` is the
positive literal). -/
abbrev CNF : Type := List (List (ℕ × Bool))

/-- A CNF formula is **satisfiable** if some assignment makes a literal of every clause true. -/
def CNF.Sat (φ : CNF) : Prop := ∃ a : ℕ → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2

/-- **The binary encoding of a CNF formula**: the list of clauses, each the list of its literals,
each literal the pair (binary representation of `v`, most significant bit first; the bit `b`), all
encoded with the base `tupleEnc`.

**Formalization Note.** The paper fixes no encoding ("our results are robust with respect to
encoding choices", p.22); this one is uniquely decodable and of linear size. -/
def CNF.enc (φ : CNF) : List Bool :=
  tupleEnc (φ.map (fun C => tupleEnc (C.map (fun l => tupleEnc [(Nat.bits l.1).reverse, [l.2]]))))

end NKtLB.Supplement


