-- Prove2me | Definitions.Def_AC02Frege_Supplement_ResPC
-- name    : AC02Frege_Supplement_ResPC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:55:57.690208+00:00
-- url     : https://prove2.me/theorems/ad1bc0a3-f985-4d17-b4c9-ada1e63714ea
-- title:
--   $\mathrm{Res}(\mathrm{PC}_r)$ and $\mathrm{Res}(\mathrm{PC})$ refutations over $\mathbb F_2$, line size and total size
-- statement:
--   **Resolution over polynomial equations** over $\mathbb F_2$, in the equation convention $u=1$ (the polynomial $u$ is the truth indicator of its equation; its complement is $\bar u=1+u$).
--
--   A **line** is a disjunction
--   $$
--   L=(u_1=1)\vee\cdots\vee(u_s=1)
--   $$
--   of polynomial equations; it is true at a Boolean assignment when some $u_i$ takes the value one. The empty line is false. The **default axioms** are the true equation $1=1$ and, for each variable $y$, the line $(y=1)\vee(\bar y=1)$. The **input clause** of a clause $C$ is the disjunction of the degree-one equations $\lambda=1$, one per literal $\lambda$ of $C$. The **rules** are weakening, contraction, deletion of the false constant equation $0=1$,
--   $$
--   \frac{A\vee(u=1)\qquad B\vee(v=1)}{A\vee B\vee(w=1)},\ \ \bar w=\bar u+\bar v,
--   \qquad\qquad
--   \frac{A\vee(u=1)}{A\vee(w=1)},\ \ \bar w=\bar u\,v\ \ (v \text{ any polynomial}).
--   $$
--   Products are formal: the system knows $y^2=y$ only through the default axioms. A **refutation** of a CNF $\Gamma$ is a sequence of lines, each an axiom, an input clause, or inferred from earlier lines by a rule, ending with the empty line. In $\mathrm{Res}(\mathrm{PC}_r)$ every polynomial of every line (conclusions of rules included) has formal degree at most $r$; without a bound the system is $\mathrm{Res}(\mathrm{PC})$.
--
--   The **line size** $S(\Pi)$ is the number of lines. The **total size** $T(\Pi)$ is the number of monomial occurrences, every polynomial $u$ of every equation $u=1$ being written as an explicit sum of monomials.
--
--   These are the proof systems of Theorems 3.14, 4.20, 6.3 and 1.5.
--
--   **Formalization Note** A line is a `Finset` of polynomials in `MvPolynomial V (ZMod 2)`, so contraction and reordering are built in. A refutation is a `List` of lines with the rules as an inductive predicate on strictly earlier lines; the degree parameter is in `ℕ∞`, with `⊤` for $\mathrm{Res}(\mathrm{PC})$. The total size counts the monomials of the displayed $u$ (not of $\bar u$) and is floored at $1$, so a refutation with no monomial occurrence at all (only possible when $\Gamma$ contains the empty clause) has total size $1$ rather than $0$.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition 2.6, p.10; Definition 2.7, p.11

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC

namespace AC02Frege.Supplement

open MvPolynomial LiftSAParity

/-- A **line** of `Res(PC)` (Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on
AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Definition 2.6, p.10): a disjunction
`(u_1 = 1) ∨ ⋯ ∨ (u_s = 1)` of polynomial equations over `𝔽₂`, represented by the finite set of its
polynomials `u_i`. The empty line is the empty (false) disjunction.

**Formalization Note** The equation convention is the paper's `u = 1`: the polynomial of an
equation is its truth indicator. Representing a line as a `Finset` builds in contraction and
reordering. -/
abbrev RLine (V : Type*) := Finset (MvPolynomial V (ZMod 2))

/-- One **inference** of `Res(PC)` refuting the CNF `Γ` (Definition 2.6, p.10): the line `L` is a
default axiom, an input clause, or follows by one rule from lines satisfying `E` (the earlier
lines). Writing `A ∨ (u = 1)` for `insert u A`:

* default axioms: the true equation `1 = 1`, and for each variable the line `(y_v = 1) ∨ (ȳ_v = 1)`,
  i.e. `{y_v, 1 + y_v}`;
* input clauses: for `C ∈ Γ`, the disjunction of the degree-one equations `λ = 1`, one per literal;
* weakening (`L' ⊆ L`);
* deletion of the false constant equation: `A ∨ (0 = 1) ⊢ A`;
* linear combination `A ∨ (u = 1), B ∨ (v = 1) ⊢ A ∨ B ∨ (w = 1)` with `w̄ = ū + v̄`, i.e.
  `w = 1 + u + v`;
* multiplication `A ∨ (u = 1) ⊢ A ∨ (w = 1)` with `w̄ = ū v`, i.e. `w = 1 + (1 + u) v`, for every
  polynomial `v`.

**Formalization Note** Products are **formal** (no multilinearization): the system knows the
Boolean relation `y² = y` only through the default axioms, exactly as on p.10. Degree bounds are
imposed globally in `IsResRefutation`, on every polynomial of every line (conclusions included), so
there is no separate bound on the multiplier `v`. -/
inductive ResInfers {V : Type*} [DecidableEq V] (Γ : CNF V) (E : RLine V → Prop) : RLine V → Prop
  | axOne : ResInfers Γ E {1}
  | axBool (v : V) : ResInfers Γ E {X v, 1 + X v}
  | input (C : Clause V) : C ∈ Γ → ResInfers Γ E (C.image litPoly)
  | weaken (L L' : RLine V) : E L' → L' ⊆ L → ResInfers Γ E L
  | del (A : RLine V) : E (insert 0 A) → ResInfers Γ E A
  | lin (A B : RLine V) (u v : MvPolynomial V (ZMod 2)) : E (insert u A) → E (insert v B) →
      ResInfers Γ E (insert (1 + u + v) (A ∪ B))
  | mul (A : RLine V) (u v : MvPolynomial V (ZMod 2)) : E (insert u A) →
      ResInfers Γ E (insert (1 + (1 + u) * v) A)

/-- A **syntactic `Res(PC_r)` refutation** of the CNF `Γ` (Definition 2.6, p.10), with
`r : ℕ∞`: every polynomial of every line has formal (total) degree at most `r`; every line is an
axiom, an input clause, or follows from strictly earlier lines by a rule; and the last line is the
empty disjunction. `r = ⊤` is `Res(PC)`, with no bound on the degree of its polynomials. The number
of lines `S(π)` (Definition 2.7, p.11) is `π.length`. -/
def IsResRefutation {V : Type*} [DecidableEq V] (r : ℕ∞) (Γ : CNF V) (π : List (RLine V)) :
    Prop :=
  (∀ L ∈ π, ∀ u ∈ L, (u.totalDegree : ℕ∞) ≤ r) ∧
  (∀ (k : ℕ) (hk : k < π.length),
    ResInfers Γ (fun L' => ∃ j < k, π[j]? = some L') π[k]) ∧
  π.getLast? = some ∅

/-- The **total size** `T(π)` of a `Res(PC)` refutation (Definition 2.7, p.11): the number of
monomial occurrences in `π`, every polynomial `u` of every equation `u = 1` being written as an
explicit sum of monomials.

**Formalization Note** Monomials are counted on the displayed polynomial `u` of the equation
`u = 1` (its support). The count is floored at `1`: a refutation all of whose lines are `∅` or
`{0}` has no monomial occurrence at all, and the paper's statements that divide or compare with `T`
(for instance "with probability at least `1 − Tq^{−d}`", "at most `T(n′)^{Cd}` lines") presuppose
`T ≥ 1`; every other refutation is unaffected. -/
def totalSize {V : Type*} (π : List (RLine V)) : ℕ :=
  max 1 (π.map (fun L => ∑ u ∈ L, u.support.card)).sum

end AC02Frege.Supplement


