-- Prove2me | Definitions.Def_QBFBackdoor_IsBackdoor2CNF
-- name    : QBFBackdoor_IsBackdoor2CNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:13.804995+00:00
-- url     : https://prove2.me/theorems/184f5c57-87e7-4d4d-b0cc-c0ae1c23a1d6
-- title:
--   Strong backdoors to QBF(2-CNF), QBF(HORN) and QBF(AFF)
-- statement:
--   Let $\Phi=Q.\phi$ be a QBF and $\mathcal C$ a class of matrices. A **strong backdoor** to QBF$(\mathcal C)$ is a set $B\subseteq V(\phi)$ of variables of the matrix such that
--
--   $$
--   \Phi[\tau]\in\mathrm{QBF}(\mathcal C)\qquad\text{for every } \tau:B\to\{0,1\}.
--   $$
--
--   Restriction acts atom by atom, and membership is tested atom by atom: an atom made true by $\tau$ is deleted, and every other atom is simplified.
--
--   1. **2-CNF and HORN.** For a CNF matrix, $\phi[\tau]$ removes the clauses satisfied by $\tau$ and removes from the other clauses the literals set to $0$. So $B$ is a strong backdoor to 2-CNF iff, for every $\tau$ and every clause, either some literal of the clause on $B$ is true under $\tau$, or the clause has at most two literals outside $B$. It is a strong backdoor to HORN iff, in the second case, at most one literal outside $B$ is positive.
--   2. **AFF**, for guarded affine atoms $(A,b)\vee T$. Under $\tau$, either a guard literal on $B$ is true and the atom becomes $\top$, or every guard variable lies in $B$, the guard vanishes, and the residual is the affine equation $(A\setminus B,\ b+\sum_{v\in A\cap B}\tau(v))$. An atom whose guard keeps a variable outside $B$ is not an affine atom.
--
--   The mission also fixes the paper's input convention that no clause (and no guard) contains a complementary pair $x_v,\neg x_v$.
--
--   **Formalization Note** `τ` ranges over total assignments `Fin n → Bool`, of which only the values on $B$ are read. The empty residual clause $\bot$ belongs to 2-CNF and to HORN. $V(\phi)$ is the set of variables occurring in the matrix (`matrixVars`, `GAffQBF.vars`). The module defines `IsBackdoor2CNF`, `IsBackdoorHorn`, `IsBackdoorAff` and the two `NonTaut` predicates.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Definition 3.4, p.17; §3.1, pp.14–15 (restriction, 2-CNF, HORN, AFF); §3.2, p.16 (membership constraint by constraint; input clauses)

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_QSAT
import Definitions.Def_QBFBackdoor_GAffQBF

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved

/-- The variables occurring in the matrix of a CNF QBF, `V(ϕ)` (§3.1, p.14). -/
def matrixVars {n m : ℕ} (φ : QBF n m) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => (φ.clause i).image Prod.fst)

/-- **The input convention on clauses.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki,
*Backdoors for Quantified Boolean Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…),
§3.2, p.16: "Input clauses have no repeated literals or complementary pair; tautological clauses
are removed." No clause contains both `x_v` and `¬x_v`. (Repeated literals cannot occur: a clause
is a `Finset`.) -/
def NonTaut {n m : ℕ} (φ : QBF n m) : Prop :=
  ∀ i, ∀ v : Fin n, ¬ ((v, true) ∈ φ.clause i ∧ (v, false) ∈ φ.clause i)

/-- **Strong backdoor to QBF(2-CNF).** Definition 3.4, p.17: "For a QBF formula Φ = Q.ϕ we define a
(strong) backdoor to C as a set B ⊆ V (ϕ) where Φ[τ] ∈ C for every τ : B → {0, 1}." Here C is
2-CNF, "formulas in CNF where each clause has at most [2] literals" (p.14), and, for CNF, "ϕ[τ] is
the formula obtained from ϕ by removing all clauses satisfied by τ and removing all literals from
clauses that are set to 0 by τ" (p.14). Membership is "tested constraint by constraint" (p.16).

So `B ⊆ V(ϕ)` and, for every assignment `τ` and every clause, either a literal of the clause on
`B` is true under `τ` (the clause is removed), or the literals of the clause off `B` (the residual
clause) number at most two.

**Formalization Note** `τ` ranges over total assignments `Fin n → Bool`; only its values on `B`
are read, so this is the same as ranging over `τ : B → {0,1}`. The empty residual clause `⊥` is in
2-CNF. Prefix restrictions play no role: 2-CNF is a matrix class. -/
def IsBackdoor2CNF {n m : ℕ} (φ : QBF n m) (B : Finset (Fin n)) : Prop :=
  B ⊆ matrixVars φ ∧
    ∀ τ : Fin n → Bool, ∀ i : Fin m,
      (∃ l ∈ φ.clause i, l.1 ∈ B ∧ τ l.1 = l.2) ∨
        ((φ.clause i).filter (fun l => l.1 ∉ B)).card ≤ 2

/-- **Strong backdoor to QBF(HORN).** Definition 3.4, p.17, with C = HORN, "formulas in CNF where
each clause has at most one positive literal" (p.14): `B ⊆ V(ϕ)` and, for every assignment `τ` and
every clause, either a literal on `B` is true under `τ`, or the residual clause (its literals off
`B`) has at most one positive literal.

**Formalization Note** As for `IsBackdoor2CNF`: `τ` is total but only read on `B`; the empty
residual clause is Horn. -/
def IsBackdoorHorn {n m : ℕ} (φ : QBF n m) (B : Finset (Fin n)) : Prop :=
  B ⊆ matrixVars φ ∧
    ∀ τ : Fin n → Bool, ∀ i : Fin m,
      (∃ l ∈ φ.clause i, l.1 ∈ B ∧ τ l.1 = l.2) ∨
        ((φ.clause i).filter (fun l => l.1 ∉ B ∧ l.2 = true)).card ≤ 1

/-- The variables occurring in the matrix of a guarded-affine QBF: those of the equations and of
the guards. -/
def GAffQBF.vars {n m : ℕ} (ψ : GAffQBF n m) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => (ψ.atom i).eqv ∪ (ψ.atom i).guard.image Prod.fst)

/-- The input convention of p.16 for the clausal guards: no guard contains both `x_v` and
`¬x_v`. -/
def GAffQBF.NonTaut {n m : ℕ} (ψ : GAffQBF n m) : Prop :=
  ∀ i, ∀ v : Fin n, ¬ ((v, true) ∈ (ψ.atom i).guard ∧ (v, false) ∈ (ψ.atom i).guard)

/-- **Strong backdoor to QBF(AFF)** for guarded-affine QBFs. Definition 3.4, p.17, with C = AFF,
"conjunctive formulas with atoms of the form (ℓ1 ⊕ ℓ2 ⊕ · · · ⊕ ℓk) = b" (p.15), where
"C[τ] [is] the atom (A \ V (τ), b + A[τ])" (p.15) and a guarded atom `R ∨ T` simplifies, once all
guard variables are assigned, "to ⊤ or to the original atom" (p.14).

So `B ⊆ V(ϕ)` and, for every assignment `τ` and every atom, either a guard literal on `B` is true
under `τ` (the atom becomes `⊤` and is deleted), or every guard variable lies in `B` (all guard
literals are false, the guard vanishes, and the residual is the affine equation
`(A \ B, b + τ(A ∩ B))`). An atom whose guard keeps an unassigned literal is not an affine atom.

**Formalization Note** `τ` is total but only read on `B`. Membership is syntactic, atom by atom
(p.16): only atoms made true by `τ` are deleted. -/
def IsBackdoorAff {n m : ℕ} (ψ : GAffQBF n m) (B : Finset (Fin n)) : Prop :=
  B ⊆ ψ.vars ∧
    ∀ τ : Fin n → Bool, ∀ i : Fin m,
      (∃ l ∈ (ψ.atom i).guard, l.1 ∈ B ∧ τ l.1 = l.2) ∨ (∀ l ∈ (ψ.atom i).guard, l.1 ∈ B)

end QBFBackdoor


