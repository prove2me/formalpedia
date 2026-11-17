-- Prove2me | Definitions.Def_CoRSuccGap_Supplement_AnnotatedRelationalAlgebra
-- name    : CoRSuccGap_Supplement_AnnotatedRelationalAlgebra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:38:29.554814+00:00
-- url     : https://prove2.me/theorems/5421c92b-fa1c-4e35-919d-182b58ac4e67
-- title:
--   Semiring-valued $G_k$, positive $ARA(3)$ and finite join breadth
-- statement:
--   Let $S$ be a commutative semiring and $V$ a finite nonempty common index set. For inputs $P_i,Q_i:V^2\to S$, the semiring-valued query is
--
--   $$
--   G_k(x,y)=\bigoplus_{z\in V}\ \bigotimes_{i=1}^k
--   \big[(P_i(x,y)\otimes Q_i(x,z))\oplus(Q_i(x,y)\otimes P_i(x,z))\big].
--   $$
--
--   Positive $ARA(3)$ expressions use only the three attributes $x,y,z$: renamed binary inputs, annotation-adding union, annotation-multiplying natural join, and projection by summing over exactly the eliminated attributes. The module records schemas, well-formedness, semantics and syntax-tree size.
--
--   For idempotent addition, a natural number $\beta$ is the **finite join breadth** when every finite join is determined by at most $\beta$ summands and $\beta$ is the least such bound. The natural and integer tropical semirings are represented as Mathlib tropicalizations of $\mathbb N\cup\{+\infty\}$ and $\mathbb Z\cup\{+\infty\}$; the Boolean semiring is the two-element powerset semiring of a singleton.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Section 7.1 pp.37--38 (PDF 39--40), Section 7.3 pp.39--40 (PDF 41--42)

import Mathlib
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.Data.Set.Semiring
import Definitions.Def_CoRSuccGap_Gk

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-!
# The semiring-valued query and positive ARA(3)

Uezato--Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Section 7.1,
pp.37--38 (PDF 39--40), and Section 7.3, p.40 (PDF 42).

Attributes are the three names `0=x`, `1=y`, `2=z`.  Inputs may be renamed onto any ordered pair
of attributes.  Union adds annotations, natural join multiplies them, and projection sums over
exactly the eliminated attributes.  The syntax has no complement, difference, or universal
quantifier, so every expression is positive and every intermediate schema has at most three
attributes by construction.
-/

/-- A positive annotated-relational-algebra expression using at most the attributes `x,y,z`. -/
inductive ARA3Expr (σ : Type*) where
  | input (R : σ) (a b : Fin 3)
  | union (p q : ARA3Expr σ)
  | join (p q : ARA3Expr σ)
  | project (keep : Finset (Fin 3)) (p : ARA3Expr σ)

/-- The attributes carried by an ARA(3) expression. -/
def ARA3Expr.schema {σ : Type*} : ARA3Expr σ → Finset (Fin 3)
  | .input _ a b => {a, b}
  | .union p _ => p.schema
  | .join p q => p.schema ∪ q.schema
  | .project keep _ => keep

namespace ARA3Expr

variable {σ : Type*}

/-- Schema correctness: union operands have the same attributes and projection retains a subset
of the source attributes. -/
def WellFormed : ARA3Expr σ → Prop
  | .input _ _ _ => True
  | .union p q => p.WellFormed ∧ q.WellFormed ∧ p.schema = q.schema
  | .join p q => p.WellFormed ∧ q.WellFormed
  | .project keep p => p.WellFormed ∧ keep ⊆ p.schema

/-- Syntax-tree node count of a positive ARA(3) expression. -/
def numNodes : ARA3Expr σ → ℕ
  | .input _ _ _ => 1
  | .union p q => p.numNodes + q.numNodes + 1
  | .join p q => p.numNodes + q.numNodes + 1
  | .project _ p => p.numNodes + 1

/-- Semiring semantics on total assignments to `x,y,z`.  Projection fixes the retained attributes
and also fixes attributes outside the source schema, hence sums once over precisely the eliminated
source attributes. -/
noncomputable def eval {V S : Type*} [Fintype V] [DecidableEq V] [CommSemiring S]
    (M : σ → V → V → S) : ARA3Expr σ → (Fin 3 → V) → S
  | .input R a b, s => M R (s a) (s b)
  | .union p q, s => p.eval M s + q.eval M s
  | .join p q, s => p.eval M s * q.eval M s
  | .project keep p, s =>
      ∑ t : Fin 3 → V,
        if (∀ i, i ∈ keep → t i = s i) ∧ (∀ i, i ∉ p.schema → t i = s i)
        then p.eval M t else 0

end ARA3Expr

/-- The scalar semiring-valued query
`⊕_z ⊗_i ((P_i(x,y)⊗Q_i(x,z)) ⊕ (Q_i(x,y)⊗P_i(x,z)))`. -/
def semiringGk (k : ℕ) {V S : Type*} [Fintype V] [CommSemiring S]
    (M : GSym k → V → V → S) : V → V → S :=
  fun x y => Finset.univ.sum (fun z : V =>
    Finset.univ.prod (fun i : Fin k =>
      (M (GSym.P i) x y * M (GSym.Q i) x z) +
        (M (GSym.Q i) x y * M (GSym.P i) x z)))

/-- A well-formed positive ARA(3) expression with output attributes `(x,y)` represents the
semiring-valued query `G_k` on every finite nonempty common index set. -/
def ARA3RepresentsGk (S : Type*) [CommSemiring S] (k : ℕ) (e : ARA3Expr (GSym k)) : Prop :=
  e.WellFormed ∧ e.schema = ({0, 1} : Finset (Fin 3)) ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (M : GSym k → V → V → S) (s : Fin 3 → V),
        e.eval M s = semiringGk k M (s 0) (s 1)

/-- Every finite join in `S` is determined by at most `b` of its summands. -/
def FiniteJoinBound (S : Type*) [AddCommMonoid S] (b : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : ι → S), ∃ t : Finset ι,
    t.card ≤ b ∧ ∑ i, f i = ∑ i ∈ t, f i

/-- `β` is the least finite join bound, i.e. the semilattice's finite join breadth. -/
def HasJoinBreadth (S : Type*) [AddCommMonoid S] (β : ℕ) : Prop :=
  FiniteJoinBound S β ∧ ∀ b, FiniteJoinBound S b → β ≤ b

/-- The natural min--plus semiring `ℕ ∪ {+∞}`. -/
abbrev TropNat := Tropical (WithTop ℕ)

/-- The integer min--plus semiring `ℤ ∪ {+∞}`. -/
abbrev TropInt := Tropical (WithTop ℤ)

/-- A two-element realization of the Boolean semiring as the subsets of a singleton.  Addition is
union (disjunction), multiplication is set product (conjunction on a singleton), zero is empty and
one is the singleton. -/
abbrev BoolSemiring := SetSemiring PUnit

end Supplement
end CoRSuccGap


