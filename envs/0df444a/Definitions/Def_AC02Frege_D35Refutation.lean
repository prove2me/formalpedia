-- Prove2me | Definitions.Def_AC02Frege_D35Refutation
-- name    : AC02Frege_D35Refutation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:02.97688+00:00
-- url     : https://prove2.me/theorems/6034889a-ef0f-48ce-b68d-73c52c6a8c24
-- title:
--   Depth-3.5 AC0[2]-Frege refutations with bottom degree $b$ and their total size
-- statement:
--   Fix $b\ge1$. A **term** is a conjunction $T=\bigwedge_{j\in I_T}(u_{T,j}=1)$ of polynomial equations, where every $u_{T,j}$ is a multilinear polynomial over $\mathbb F_2$ of degree at most $b$; order and repetition of equations are immaterial, a singleton equation is a term and the empty term $\top$ is true. A **line** is a disjunction of terms. The polynomial of an equation $u=1$ is its truth indicator.
--
--   The rules, with $A,B$ disjunctions of terms, are weakening and contraction,
--   $$
--   \frac{A\vee T}{A\vee U}\ (U\subseteq T),\qquad \frac{A\vee T\quad B\vee U}{A\vee B\vee(T\wedge U)},\qquad \frac{A\vee T\quad B\vee\bigvee_{j\in I_T}(1+u_{T,j}=1)}{A\vee B},
--   $$
--   linear combination $A\vee(u=1),\ B\vee(v=1)\vdash A\vee B\vee(w=1)$ with $\overline w=\overline u+\overline v$, i.e. $w=1+u+v$; multiplication $A\vee(u=1)\vdash A\vee\bigl(1+\mathrm{ML}((1+u)v)=1\bigr)$ for any $v$, provided the conclusion has degree at most $b$; and deletion of a singleton false constant equation $0=1$. The default axioms are $(1=1)$, the empty true term, and $(u=1)\vee(1+u=1)$ for every allowed $u$. The input clause of a clause $C$ is the disjunction of the singleton terms $(\lambda(x)=1)$, $\lambda\in C$.
--
--   A **refutation** of a CNF $\Gamma$ is a sequence of lines each of which is an axiom, an input clause, or follows from earlier lines by a rule, and whose final line is the empty disjunction. Its **total size** $T$ counts all term occurrences and all monomial occurrences, every polynomial written as an explicit sum of monomials: a term occurrence with equations $u_1,\dots,u_s$ contributes $1+\sum_j\#\mathrm{monomials}(u_j)$.
--
--   **Formalization Note** Terms are finite sets of polynomials and lines finite sets of terms, so contraction is built in and a list refutation maps to one of no larger total size. The degree bound $b$ is a global condition on every polynomial in every line, which is how the multiplication rule's side condition and the restriction of the default axioms are enforced.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition D.1, p.47; Definition 2.6, p.10; Definition 2.7, p.11; §5, pp.28–29

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- A **term** of depth-3.5 AC0[2]-Frege (Definition D.1, p.47; §5.1, p.29): a conjunction
`⋀_{j ∈ I_T} (u_{T,j} = 1)` of polynomial equations, represented by the finite set of its
polynomials `u_{T,j}` ("ordering and repetition of equations within a term are immaterial"). The
empty term is true. -/
abbrev Term (V : Type*) := Finset (MvPolynomial V (ZMod 2))

/-- A **line** of depth-3.5 AC0[2]-Frege: a disjunction of terms, represented by the finite set of
its terms (contraction is built in). The empty line is false. -/
abbrev Line (V : Type*) := Finset (Term V)

/-- A polynomial allowed in an equation of a line with bottom degree `b` (Definition D.1, p.47):
multilinear over `𝔽₂` with degree at most `b`. -/
def Allowed {V : Type*} (b : ℕ) (u : MvPolynomial V (ZMod 2)) : Prop :=
  IsMultilinear u ∧ u.totalDegree ≤ b

/-- The line of an input clause `C` (Definition 2.6, p.10; Definition D.1): the disjunction of the
singleton terms `(λ(x) = 1)`, one per literal `λ ∈ C`. -/
noncomputable def inputLine {V : Type*} [DecidableEq V] (C : Clause V) : Line V :=
  C.image (fun l => ({litPoly l} : Term V))

/-- One **inference** of depth-3.5 AC0[2]-Frege refuting the CNF `Γ` (Definition D.1, p.47, with
the polynomial rules of Definition 2.6, p.10): the line `L` is a default axiom, an input clause,
or follows by one rule from lines satisfying `E` (the earlier lines). Writing `A ∨ T` for the line
`insert T A`:

* default axioms `(1 = 1)`, the empty true term `⊤`, and `(u = 1) ∨ (1 + u = 1)`;
* input clauses `inputLine C`, `C ∈ Γ`;
* weakening (`L' ⊆ L`);
* projection `A ∨ T ⊢ A ∨ U` when every equation of `U` occurs in `T`;
* conjunction `A ∨ T, B ∨ U ⊢ A ∨ B ∨ (T ∧ U)`;
* cut `A ∨ T, B ∨ ⋁_{j ∈ I_T} (1 + u_{T,j} = 1) ⊢ A ∨ B`;
* linear combination `A ∨ (u = 1), B ∨ (v = 1) ⊢ A ∨ B ∨ (w = 1)` with `w̄ = ū + v̄`, i.e.
  `w = 1 + u + v`;
* multiplication `A ∨ (u = 1) ⊢ A ∨ (1 + ML((1 + u) v) = 1)` for every polynomial `v`;
* deletion of the singleton false constant equation `0 = 1`.

**Formalization Note** Contraction is implicit since lines and terms are finite sets. The
equation convention is `u = 1`: the polynomial of an equation is its truth indicator. Degree
bounds are imposed globally in `IsRefutation`, so a rule applies only when its conclusion is a
line of the system; in particular there is no separate bound on the multiplier `v`. -/
inductive Infers {V : Type*} [DecidableEq V] (Γ : CNF V) (E : Line V → Prop) : Line V → Prop
  | axOne : Infers Γ E {{1}}
  | axTop : Infers Γ E {∅}
  | axEM (u : MvPolynomial V (ZMod 2)) : Infers Γ E {{u}, {1 + u}}
  | input (C : Clause V) : C ∈ Γ → Infers Γ E (inputLine C)
  | weaken (L L' : Line V) : E L' → L' ⊆ L → Infers Γ E L
  | proj (A : Line V) (T U : Term V) : E (insert T A) → U ⊆ T → Infers Γ E (insert U A)
  | conj (A B : Line V) (T U : Term V) : E (insert T A) → E (insert U B) →
      Infers Γ E (insert (T ∪ U) (A ∪ B))
  | cut (A B : Line V) (T : Term V) : E (insert T A) →
      E (B ∪ T.image (fun u => ({1 + u} : Term V))) → Infers Γ E (A ∪ B)
  | lin (A B : Line V) (u v : MvPolynomial V (ZMod 2)) : E (insert {u} A) → E (insert {v} B) →
      Infers Γ E (insert {1 + u + v} (A ∪ B))
  | mul (A : Line V) (u v : MvPolynomial V (ZMod 2)) : E (insert {u} A) →
      Infers Γ E (insert {1 + ML ((1 + u) * v)} A)
  | del (A : Line V) : E (insert {0} A) → Infers Γ E A

/-- A **depth-3.5 AC0[2]-Frege refutation** of the CNF `Γ` with bottom degree `b`
(Definition D.1, p.47; Definition 2.6, p.10): `b ≥ 1`; every polynomial occurring in every line is
multilinear of degree at most `b`; each line is an axiom, an input clause, or follows from earlier
lines by a rule; and the final line is the empty disjunction. -/
def IsRefutation {V : Type*} [DecidableEq V] (b : ℕ) (Γ : CNF V) (π : List (Line V)) : Prop :=
  1 ≤ b ∧
  (∀ L ∈ π, ∀ T ∈ L, ∀ u ∈ T, Allowed b u) ∧
  (∀ (k : ℕ) (hk : k < π.length), Infers Γ (fun L' => ∃ j < k, π[j]? = some L') π[k]) ∧
  π.getLast? = some ∅

/-- The **total size** `T` of a refutation (Definition 2.7, p.11; Definition D.1, p.47): all term
occurrences plus all monomial occurrences, every polynomial being written as an explicit sum of
monomials. A term occurrence with equations `u_1, …, u_s` contributes `1 + Σ_j #monomials(u_j)`. -/
def totalSize {V : Type*} (π : List (Line V)) : ℕ :=
  (π.map (fun L => ∑ T ∈ L, (1 + ∑ u ∈ T, u.support.card))).sum

end AC02Frege


