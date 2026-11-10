-- Prove2me | Definitions.Def_ExactOneHS_Counting_DNFCondition
-- name    : ExactOneHS_Counting_DNFCondition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:11:28.16446+00:00
-- url     : https://prove2.me/theorems/73e95757-e56b-4e45-a53c-905431da6f1e
-- title:
--   Terms, explicit DNF conditions $P_j$, the formula $H = B \wedge P_1 \wedge \dots \wedge P_h$ and its model count
-- statement:
--   Fix $n$ declared Boolean variables $x_1, \dots, x_n$. A **term** $T$ is a conjunction of literals, identified with its finite set of literals; it is true under $x$ if all its literals are true, so the empty term is true. A **DNF condition** given by an explicit list $\mathcal T = (T_1, T_2, \dots)$ of terms is
--   $$P(x) = \bigvee_{T \in \mathcal T} \bigwedge_{\ell \in T} \ell,$$
--   true if some listed term is true; the empty list gives the false condition.
--
--   The data of the two-boundary counting reduction is a CNF $B$ on the $n$ declared variables, a number $h \ge 0$, and explicit term lists $\mathcal T_1, \dots, \mathcal T_h$ (repetitions allowed). With $P_j$ the condition of $\mathcal T_j$,
--   $$H := B \wedge \bigwedge_{j=1}^{h} P_j, \qquad \#\mathrm{SAT}(H) = \bigl|\{x \in \{0,1\}^n : H(x) = 1\}\bigr|,$$
--   and $\sum_{j=1}^h |\mathcal T_j|$ is the total number of listed terms. Such data is coded by `encodeCNF` of $B$ (which starts with $n$ in unary), then $h$ in unary, then the $h$ term lists, each term as the increasing list of its literal codes in unary.
--
--   **Formalization Note.** Variables are `Fin n` (0-based), the conditions are indexed by `Fin h` (the paper's $j = 1, \dots, h$ is index $j - 1$), terms are `Finset`s of literals, and term lists are `List`s so that $|\mathcal T_j|$ counts repeated terms.
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 4, Theorem 1.1 (P_j and H); p. 10, §3 Conventions (terms, DNFs, empty term true, empty disjunction false, #SAT)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- A term on `n` declared variables: a conjunction of literals, identified with its set of
literals. -/
abbrev Term (n : ℕ) := Finset (SAT.Literal (Fin n))

/-- A term is true iff all its literals are true; the empty term is true. -/
def Term.eval {n : ℕ} (x : SAT.Assignment (Fin n)) (T : Term n) : Bool :=
  decide (∀ l ∈ T, l.eval x = true)

/-- A DNF condition `P = ⋁_{T ∈ Ts} ⋀_{ℓ ∈ T} ℓ` given by an explicit list of terms is true iff
some term is true; the empty disjunction is false. -/
def dnfEval {n : ℕ} (x : SAT.Assignment (Fin n)) (Ts : List (Term n)) : Bool :=
  decide (∃ T ∈ Ts, Term.eval x T = true)

/-- The data of Theorem 1.1: a CNF `B` on `n` declared variables and `h` explicit term lists
`T_1, …, T_h` (indexed by `Fin h`, from `0`). -/
structure TwoBoundaryInput where
  /-- the number of declared variables -/
  n : ℕ
  /-- the CNF `B` -/
  B : SAT.CNF (Fin n)
  /-- the number `h` of DNF conditions -/
  h : ℕ
  /-- the explicit term list `T_j` of the condition `P_j` -/
  terms : Fin h → List (Term n)

namespace TwoBoundaryInput

variable (P : TwoBoundaryInput)

/-- `H = B ∧ ⋀_{j=1}^{h} P_j`. -/
def H (x : SAT.Assignment (Fin P.n)) : Bool :=
  SAT.CNF.eval x P.B && decide (∀ j, dnfEval x (P.terms j) = true)

/-- `#SAT(H)`: the number of assignments to all `n` declared variables satisfying `H`. -/
def countH : ℕ :=
  (Finset.univ.filter fun x : SAT.Assignment (Fin P.n) => P.H x = true).card

/-- `∑_{j=1}^{h} |T_j|`, the total number of listed terms (repetitions counted). -/
def totalTerms : ℕ := ∑ j, (P.terms j).length

end TwoBoundaryInput

/-- Code of a term: its literal codes `2·v + [positive]` in increasing order, each in unary. -/
def encodeTerm {n : ℕ} (T : Term n) : List Bool :=
  Encoding.encodeList Encoding.encodeNat (Encoding.clauseNumbers T)

/-- Code of the data of Theorem 1.1: `encodeCNF B` (which starts with `n` in unary), `h` in
unary, then the `h` term lists in order. -/
def encodeTwoBoundaryInput (P : TwoBoundaryInput) : List Bool :=
  Encoding.encodeCNF P.B ++ QAlgorithms.Complexity.encNat P.h ++
    Encoding.encodeList (Encoding.encodeList encodeTerm) (List.ofFn P.terms)

end ExactOneHS.Counting


