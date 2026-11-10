-- Prove2me | Definitions.Def_ExactOneHS_Counting_PathQuery
-- name    : ExactOneHS_Counting_PathQuery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:12:11.566926+00:00
-- url     : https://prove2.me/theorems/0726b98a-2835-43e7-a229-46f1a52e01e9
-- title:
--   The two-boundary path queries $Q_\beta$ of Eq. (11) and the extension counts $a_\beta(x)$
-- statement:
--   Let $B$ be a CNF on $n$ declared variables and $\mathcal T_1, \dots, \mathcal T_h$ explicit term lists with $h \ge 1$. Introduce fresh path variables $z_1, \dots, z_{h-1}$ and, for $\beta \in \{0,1\}$, the constant endpoints $z_0 := 0$ and $z_h := \beta$. For a term $T$ put $\overline T := \bigvee_{\ell \in T} \neg \ell$. The **path query** is
--   $$Q_\beta := B \wedge \bigwedge_{j=1}^{h} \bigwedge_{T \in \mathcal T_j} \Bigl( (\overline T \vee \neg z_{j-1} \vee z_j) \wedge (\overline T \vee z_{j-1} \vee \neg z_j) \Bigr),$$
--   after substituting the endpoint constants and deleting tautological clauses: a clause containing a true constant literal, or a literal together with its negation, is deleted, and false constant literals are removed from the remaining clauses. All $n + h - 1$ variables $x_1, \dots, x_n, z_1, \dots, z_{h-1}$ stay declared.
--
--   For an assignment $x \in \{0,1\}^n$ of the original variables, the **extension count** $a_\beta(x)$ is the number of $z \in \{0,1\}^{h-1}$ such that $(x, z)$ satisfies $Q_\beta$.
--
--   **Formalization Note.** The declared variables are `Fin (n + (h - 1))`: indices $0, \dots, n-1$ are $x_1, \dots, x_n$ and index $n + k - 1$ is $z_k$; an assignment of them is `Fin.append x z`. For $h \ge 1$, $n + (h-1) = n + h - 1$. Edge $j$ is the index $e = j - 1$ of `Fin h`. The clauses of $B$ are kept as they are (only renamed into the larger variable set). Duplicate clauses collapse, since a CNF is a finite set of clauses.
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 12, proof of Theorem 1.1, Eqs. (10), (11) and the definition of a_β(x); p. 13, Eq. (14)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ExactOneHS_Counting_DNFCondition

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- A clause is tautological if it contains a literal together with its negation. -/
def isTautological {V : Type} [DecidableEq V] (C : SAT.Clause V) : Bool :=
  decide (∃ l ∈ C, (⟨l.variable, !l.positive⟩ : SAT.Literal V) ∈ C)

/-- The literals contributed by a path endpoint: none for a constant, one for a variable. -/
def endpointLits {V : Type} : Bool ⊕ SAT.Literal V → SAT.Clause V
  | .inl _ => ∅
  | .inr l => {l}

/-- The clause `base ∨ a ∨ b` after substituting constants: deleted (`none`) if a constant
literal is true or the result is tautological; otherwise false constants are dropped. -/
def substClause {V : Type} [DecidableEq V] (base : SAT.Clause V)
    (a b : Bool ⊕ SAT.Literal V) : Option (SAT.Clause V) :=
  if a = .inl true ∨ b = .inl true then none
  else if isTautological (base ∪ endpointLits a ∪ endpointLits b) then none
  else some (base ∪ endpointLits a ∪ endpointLits b)

namespace TwoBoundaryInput

variable (P : TwoBoundaryInput)

/-- The original variable `x_i` as variable `i` of `Fin (n + (h - 1))`. -/
def liftLit (l : SAT.Literal (Fin P.n)) : SAT.Literal (Fin (P.n + (P.h - 1))) :=
  ⟨Fin.castAdd (P.h - 1) l.variable, l.positive⟩

/-- The path node `z_k` (`0 ≤ k ≤ h`) as a literal of sign `pos`, under the boundary `β`:
`z_0 := 0` and `z_h := β` are constants (Eq. (10)), given here by the truth value of the
literal; the internal node `z_k` (`1 ≤ k ≤ h - 1`) is the declared variable `n + k - 1`. -/
def nodeLit (β : Bool) (k : ℕ) (pos : Bool) : Bool ⊕ SAT.Literal (Fin (P.n + (P.h - 1))) :=
  if h0 : k = 0 then .inl (false == pos)
  else if hk : k < P.h then .inr ⟨⟨P.n + (k - 1), by omega⟩, pos⟩
  else .inl (β == pos)

/-- `T̄ = ⋁_{ℓ ∈ T} ¬ℓ`, on the original variables. -/
def negTerm (T : Term P.n) : SAT.Clause (Fin (P.n + (P.h - 1))) :=
  T.image fun l => ⟨Fin.castAdd (P.h - 1) l.variable, !l.positive⟩

/-- The two clauses `(T̄ ∨ ¬z_{j-1} ∨ z_j) ∧ (T̄ ∨ z_{j-1} ∨ ¬z_j)` of edge `j = e + 1`
(`e : Fin h`) for the term `T`, after substitution of the endpoint constants and deletion of
tautological clauses. -/
def edgeClauses (β : Bool) (e : Fin P.h) (T : Term P.n) : SAT.CNF (Fin (P.n + (P.h - 1))) :=
  (substClause (P.negTerm T) (P.nodeLit β e false) (P.nodeLit β (e + 1) true)).toFinset ∪
    (substClause (P.negTerm T) (P.nodeLit β e true) (P.nodeLit β (e + 1) false)).toFinset

/-- The two-boundary path query `Q_β` of Eq. (11) on the declared variables
`x_1, …, x_n, z_1, …, z_{h-1}` (as `Fin (n + (h - 1))`, the `x` first):
`Q_β = B ∧ ⋀_{j=1}^{h} ⋀_{T ∈ T_j} ((T̄ ∨ ¬z_{j-1} ∨ z_j) ∧ (T̄ ∨ z_{j-1} ∨ ¬z_j))`,
with `z_0 := 0`, `z_h := β` substituted and tautological clauses deleted. -/
def pathQuery (β : Bool) : SAT.CNF (Fin (P.n + (P.h - 1))) :=
  P.B.image (fun C => C.image P.liftLit) ∪
    (Finset.univ : Finset (Fin P.h)).biUnion
      (fun e => (P.terms e).toFinset.biUnion (P.edgeClauses β e))

/-- `a_β(x)`: the number of extensions `z ∈ {0,1}^{h-1}` of the original assignment `x` to the
internal path variables that satisfy `Q_β`. -/
def extensionCount (β : Bool) (x : SAT.Assignment (Fin P.n)) : ℕ :=
  (Finset.univ.filter fun z : Fin (P.h - 1) → Bool =>
    SAT.CNF.eval (Fin.append x z) (P.pathQuery β) = true).card

end TwoBoundaryInput

end ExactOneHS.Counting


