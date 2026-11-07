-- Prove2me | Definitions.Def_DynConnWC_Adversary
-- name    : DynConnWC_Adversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:36:22.884465+00:00
-- url     : https://prove2.me/theorems/cb5e21bc-2de1-4611-a14e-6ebec486de8b
-- title:
--   Adversaries that see the previous answers, and the exact oracle
-- statement:
--   An **adversary** is a strategy that chooses each operation, or the decision to stop, from the operations issued so far and the answers received so far. It sees neither the program's random tape nor its memory.
--
--   Against a program $P$ on tape $\omega$, each round consists of the adversary choosing an operation and $P$ processing it; a query's answer word is added to the history. Against the **exact oracle**, each query $(u,v)$ receives the correct answer for the current graph. Once the adversary stops, later rounds change nothing.
--
--   A fixed sequence of operations is the adversary that issues its $s$-th operation in round $s$. Comparing a run against $P$ with the run against the exact oracle is how Lemma 25 reduces adaptive sequences to fixed ones.
--
--   **Formalization Note** The adversary is deterministic. The source's adversary may use its own randomness; its proof of Lemma 25 fixes that randomness and averages, and an adversary with randomness is a mixture of deterministic ones, so a bound uniform over deterministic adversaries covers it. A round runs the program on exactly the operations issued so far, so its answer depends only on them.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 1, p.1 (PDF 2); proof of Lemma 25, p.24 (PDF 25)

import Mathlib
import Definitions.Def_DynConnWC_Run

set_option autoImplicit false

namespace DynConnWC

/-! # Adversaries that see the previous query answers

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), Theorem 1, p.1: "This also holds when the sequence is chosen by an
adversary that sees the previous query answers, but not the algorithm's randomness or the internal
state"; proof of Lemma 25, p.24: "The adversary is a strategy that chooses each operation, or the
decision to stop, from its own random choices, the operations issued so far, and the answers
received so far. … Run the adversary against an exact connectivity oracle, which answers every
query correctly."

**Formalization Note.** A (deterministic) adversary maps the history so far — the operations it
has issued, each paired with the answer word it received (`none` for an update, and for a query
that got no answer) — to its next operation, or to `none` (stop). It sees neither the random tape
nor the memory. An adversary that also uses its own randomness is a mixture of deterministic ones,
and the bounds below are uniform over deterministic adversaries. `advHist A P W ω N` is the history
after `N` rounds against program `P` on tape `ω`: in each round the adversary chooses an
operation, the program processes it (online, so its answer depends only on the operations issued
so far), and a query's answer word is appended to the history. `oracleHist A N` is the history
against the exact oracle, which answers each query `(u, v)` with `1` if `u` and `v` are connected
in the current graph and `0` otherwise. Once the adversary stops, later rounds change nothing. A
fixed sequence of operations is the adversary that issues its `s`-th operation in round `s`. -/

variable {n : ℕ}

/-- An adversary: from the history of (operation, answer received) pairs, the next operation, or
`none` to stop. -/
def Adversary (n : ℕ) := List (Op n × Option ℕ) → Option (Op n)

/-- The history of `A` after `N` rounds against program `P` with word size `W` on tape `ω`. -/
noncomputable def advHist (A : Adversary n) (P : Program) (W : ℕ) (ω : ℕ → Fin (2 ^ W)) :
    ℕ → List (Op n × Option ℕ)
  | 0 => []
  | N + 1 =>
    let h := advHist A P W ω N
    match A h with
    | none => h
    | some o =>
      h ++ [(o, match o with
                | .query _ _ => answer W P n ω (h.map Prod.fst ++ [o]) (h.length + 1)
                | _ => none)]

/-- The operations `A` issues in its first `N` rounds against `P` on tape `ω`. -/
noncomputable def advOps (A : Adversary n) (P : Program) (W : ℕ) (ω : ℕ → Fin (2 ^ W)) (N : ℕ) :
    List (Op n) :=
  (advHist A P W ω N).map Prod.fst

/-- The history of `A` after `N` rounds against the exact connectivity oracle. -/
noncomputable def oracleHist (A : Adversary n) : ℕ → List (Op n × Option ℕ)
  | 0 => []
  | N + 1 =>
    let h := oracleHist A N
    match A h with
    | none => h
    | some o =>
      h ++ [(o, match o with
                | .query u v => some (correctBit (graphAt (h.map Prod.fst) h.length) u v)
                | _ => none)]

/-- The operations `A` issues in its first `N` rounds against the exact oracle. -/
noncomputable def oracleOps (A : Adversary n) (N : ℕ) : List (Op n) :=
  (oracleHist A N).map Prod.fst

end DynConnWC


