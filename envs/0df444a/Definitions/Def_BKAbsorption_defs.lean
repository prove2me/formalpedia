-- Prove2me | Definitions.Def_BKAbsorption_defs
-- name    : BKAbsorption_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-11-07T14:12:22.207083+00:00
-- url     : https://prove2.me/theorems/22ef97dc-dfa0-4ed3-a21f-6413b3d97c4c
-- title:
--   Absorption, linked relations, Taylor term data, smooth digraphs, cyclic terms
-- statement:
--   `prodStructure`: coordinatewise operations on $A\times B$. `IsIdempotent L A`: $f(a,\dots,a)=a$ for every basic operation. `IsSubuniverse L S`: $S$ closed under basic operations. `IsAbsorbing L B` ($B\trianglelefteq A$): a subuniverse with a term $t$ such that $t(a)\in B$ whenever all $a_i$ but at most one are in $B$. `MinAbsorbing L B` ($B\trianglelefteq\!\!\trianglelefteq A$): nonempty, absorbing, no proper nonempty absorbing subset of $B$. `HasProperAbsorbing L A`: an absorbing $B$ with $\emptyset\neq B\neq A$. `Subdirect R`: both projections onto. `LinkStep R a a'`: common $R$-neighbour; `Linked R`: any two elements of the first projection are joined by `LinkStep`-chains. `LinkAdj R`: adjacency of the bipartite graph of $R$ on $A\oplus B$; `InMinAbs L x`: $x$ lies in a minimal absorbing subuniverse of $A$ or of $B$. `TaylorDatum L`: a $k$-ary term with patterns $\sigma_j,\tau_j\in\{x,y\}^k$ (`false`$=x$), $\sigma_j(j)=x$, $\tau_j(j)=y$; `IsTaylorAlg T A`: idempotent and $t(\sigma_j)\approx t(\tau_j)$ for all $j$. `Smooth E`: every vertex has an outgoing and an incoming edge. `Walk E a b z`: an oriented path from $a$ to $b$ of algebraic length $z$. `HasCyclicTermOp L A k`: an idempotent $k$-ary term operation invariant under $x\mapsto x\circ$`finRotate k`. `IsSubpower L R`: $R\subseteq A^k$ closed coordinatewise; `IsCyclicRel R`: closed under rotation.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Sections 1-4 (Defs 2.1, 2.2, 2.14, 4.3; Section 3.1)

import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Absorbing subalgebras and cyclic terms (Barto–Kozik, LMCS 8(1:07) 2012, arXiv:1201.0557)

Setting, built on Mathlib's first-order model theory (same shape as the `UAVariety` and
`HigherComm` settings):

* An *algebra* of signature `L` is a type `A` with an `L.Structure`; theorems assume
  `[L.IsAlgebraic]`.  Term operations (`Clo(A)`) are the maps `a ↦ t.realize a` for
  `t : L.Term (Fin n)`.
* `IsSubuniverse L S`: `S` is closed under every basic operation (it may be empty).
  The product `A × B` carries the coordinatewise structure `prodStructure`, so a subuniverse
  of `A × B` is an `L.Substructure (A × B)`, and `↥R` is the algebra `R` (Mathlib's induced
  structure).  Subuniverses of the power `A^k` are sets of tuples `Fin k → A` closed under
  coordinatewise basic operations (`IsSubpower L`).
* `IsAbsorbing L B` (paper Def 2.1, `B ⊴ A`): `B` is a subuniverse and some term operation `t` (of positive arity)
  satisfies `t(a₀,…,a_{n-1}) ∈ B` whenever all `aᵢ` except at most one lie in `B`.
  `MinAbsorbing L B` (Def 2.14, `B ⊴⊴ A`): `B` is a nonempty absorbing subuniverse and no proper
  subalgebra of `B` absorbs `A`.  `HasProperAbsorbing L A`: `A` has an absorbing subuniverse
  `B` with `∅ ≠ B ≠ A`.
* `Subdirect R` (`R ≤_S A × B`), `Linked R` (Def 2.2, via the relation `a ~ a'` iff `a, a'`
  have a common `R`-neighbour), and `LinkAdj R`, the adjacency of the bipartite graph of `R` on
  `A ⊕ B` (used for linking elements of `A` and `B`); `InMinAbs L x` for `x : A ⊕ B` says that
  `x` lies in a minimal absorbing subuniverse of `A` (if `x ∈ A`) or of `B` (if `x ∈ B`).
* *Taylor varieties.*  The paper works with finite algebras in a fixed Taylor variety `V`
  (idempotent with a Taylor term).  A `TaylorDatum L` is a `k`-ary term `t` with, for each
  `j < k`, two patterns `σ j, τ j : Fin k → Bool` (`false = x`, `true = y`) with `σ j j = x` and
  `τ j j = y`.  `IsTaylorAlg T A`: `A` is idempotent (every basic operation satisfies
  `f(a,…,a) = a`) and satisfies the `k` Taylor identities `t(σ j) ≈ t(τ j)`.  The class of such
  `A` is the Taylor variety axiomatized by these identities, and every algebra of a Taylor
  variety lies in such a class; "finite algebras in a Taylor variety" = finite `A` (and `B`)
  with `IsTaylorAlg T` for one common datum `T`.
* Digraphs `G = (A, E)` with `E ≤ A²` (`E : L.Substructure (A × A)`): `Smooth E`;
  `Walk E a b z` means `a` is connected to `b` by an oriented path of algebraic length `z`
  (forward edges count `+1`, backward edges `-1`).  `G` has algebraic length `1` iff some
  vertex `a` has `Walk E a a 1`; the weak component of `a` is `{b | ∃ z, Walk E a b z}`.
* `HasCyclicTermOp L A k`: a `k`-ary idempotent term operation `t` with
  `t(x₀,…,x_{k-1}) = t(x₁,…,x_{k-1},x₀)`; `IsCyclicRel R` for `R ⊆ A^k` (Def 4.3).
-/

universe u v w w'

namespace BKAbsorption

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {L : FirstOrder.Language.{u, v}}

/-- The product algebra `A × B`: operations (and relations) computed coordinatewise. -/
instance prodStructure (A : Type w) (B : Type w') [L.Structure A] [L.Structure B] :
    L.Structure (A × B) where
  funMap f x := (funMap f (fun i => (x i).1), funMap f (fun i => (x i).2))
  RelMap r x := RelMap r (fun i => (x i).1) ∧ RelMap r (fun i => (x i).2)

section algebra

variable (L) (M : Type w) [L.Structure M]

/-- Every basic operation is idempotent: `f(a, …, a) = a`. -/
def IsIdempotent : Prop :=
  ∀ (n : ℕ) (f : L.Functions n) (a : M), funMap f (fun _ => a) = a

variable {M}

/-- `S` is a subuniverse (closed under all basic operations; possibly empty). -/
def IsSubuniverse (S : Set M) : Prop :=
  ∀ (n : ℕ) (f : L.Functions n) (x : Fin n → M), (∀ i, x i ∈ S) → funMap f x ∈ S

/-- `B ⊴ M` (paper Def 2.1): `B` is a subuniverse absorbing `M` with respect to some term
operation `t ∈ Clo(M)` of positive arity. -/
def IsAbsorbing (B : Set M) : Prop :=
  IsSubuniverse L B ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
    ∀ (k : Fin n) (a : Fin n → M), (∀ i, i ≠ k → a i ∈ B) → t.realize a ∈ B

/-- `B ⊴⊴ M` (paper Def 2.14): `B` is a nonempty absorbing subuniverse and no proper
subalgebra of `B` absorbs `M`. -/
def MinAbsorbing (B : Set M) : Prop :=
  B.Nonempty ∧ IsAbsorbing L B ∧
    ∀ C : Set M, C.Nonempty → C ⊆ B → IsAbsorbing L C → C = B

variable (M) in
/-- `M` has a proper absorbing subuniverse `B` (`∅ ≠ B ≠ M`). -/
def HasProperAbsorbing : Prop :=
  ∃ B : Set M, IsAbsorbing L B ∧ B.Nonempty ∧ B ≠ Set.univ

end algebra

section relations

variable {A : Type w} {B : Type w'}

/-- `R ⊆ A × B` is subdirect: both projections are onto. -/
def Subdirect (R : Set (A × B)) : Prop :=
  Prod.fst '' R = Set.univ ∧ Prod.snd '' R = Set.univ

/-- `a ~ a'` iff `a` and `a'` have a common `R`-neighbour; its reflexive-transitive closure is
"`a, a'` are `R`-linked" (paper Def 2.2). -/
def LinkStep (R : Set (A × B)) (a a' : A) : Prop :=
  ∃ b, (a, b) ∈ R ∧ (a', b) ∈ R

/-- `R` is linked (paper Def 2.2): any two elements of the first projection are `R`-linked. -/
def Linked (R : Set (A × B)) : Prop :=
  ∀ a a', a ∈ Prod.fst '' R → a' ∈ Prod.fst '' R → Relation.ReflTransGen (LinkStep R) a a'

/-- Adjacency in the bipartite graph of `R` on the disjoint union `A ⊕ B`
(`a ∈ A` and `b ∈ B` are adjacent iff `(a, b) ∈ R`). -/
def LinkAdj (R : Set (A × B)) : A ⊕ B → A ⊕ B → Prop
  | Sum.inl a, Sum.inr b => (a, b) ∈ R
  | Sum.inr b, Sum.inl a => (a, b) ∈ R
  | _, _ => False

end relations

section minabsSum

variable (L) {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]

/-- An element of `A ⊕ B` lies in some minimal absorbing subuniverse of `A` (left summand) or
of `B` (right summand). -/
def InMinAbs : A ⊕ B → Prop
  | Sum.inl a => ∃ C : Set A, MinAbsorbing L C ∧ a ∈ C
  | Sum.inr b => ∃ D : Set B, MinAbsorbing L D ∧ b ∈ D

end minabsSum

section taylor

/-- A Taylor term datum: a `k`-ary term `t` and, for every `j < k`, an identity
`t(σ j) ≈ t(τ j)` in the variables `x` (`false`) and `y` (`true`), with `x` at position `j` on
the left and `y` at position `j` on the right. -/
structure TaylorDatum (L : FirstOrder.Language.{u, v}) where
  k : ℕ
  t : L.Term (Fin k)
  σ : Fin k → Fin k → Bool
  τ : Fin k → Fin k → Bool
  σ_self : ∀ j, σ j j = false
  τ_self : ∀ j, τ j j = true

/-- `A` lies in the Taylor variety given by `T`: `A` is idempotent and satisfies the Taylor
identities of `T`. -/
def IsTaylorAlg (T : TaylorDatum L) (A : Type w) [L.Structure A] : Prop :=
  IsIdempotent L A ∧ ∀ (j : Fin T.k) (x y : A),
    T.t.realize (fun i => cond (T.σ j i) y x) = T.t.realize (fun i => cond (T.τ j i) y x)

end taylor

section digraph

variable {A : Type w}

/-- The digraph `(A, E)` is smooth: every vertex has an outgoing and an incoming edge. -/
def Smooth (E : Set (A × A)) : Prop :=
  ∀ a, (∃ b, (a, b) ∈ E) ∧ (∃ b, (b, a) ∈ E)

/-- `Walk E a b z`: `a` is connected to `b` via an oriented path of algebraic length `z`
(number of forward edges minus number of backward edges). -/
inductive Walk (E : Set (A × A)) : A → A → ℤ → Prop
  | refl (a : A) : Walk E a a 0
  | fwd {a b c : A} {z : ℤ} : Walk E a b z → (b, c) ∈ E → Walk E a c (z + 1)
  | bwd {a b c : A} {z : ℤ} : Walk E a b z → (c, b) ∈ E → Walk E a c (z - 1)

end digraph

section cyclic

variable (L) (A : Type w) [L.Structure A]

/-- `A` has a `k`-ary cyclic term operation: an idempotent term operation `t` with
`t(x₀, x₁, …, x_{k-1}) = t(x₁, …, x_{k-1}, x₀)`. -/
def HasCyclicTermOp (k : ℕ) : Prop :=
  ∃ t : L.Term (Fin k), (∀ a : A, t.realize (fun _ => a) = a) ∧
    ∀ x : Fin k → A, t.realize x = t.realize (x ∘ finRotate k)

variable {A}

/-- `R ⊆ A^k` is a subuniverse of the power algebra `A^k` (closed under coordinatewise basic
operations). -/
def IsSubpower {k : ℕ} (R : Set (Fin k → A)) : Prop :=
  ∀ (n : ℕ) (f : L.Functions n) (x : Fin n → Fin k → A), (∀ i, x i ∈ R) →
    (fun j => funMap f (fun i => x i j)) ∈ R

/-- `R ⊆ A^k` is cyclic (paper Def 4.3): closed under the cyclic shift
`(a₀, …, a_{k-1}) ↦ (a₁, …, a_{k-1}, a₀)`. -/
def IsCyclicRel {k : ℕ} (R : Set (Fin k → A)) : Prop :=
  ∀ x ∈ R, x ∘ finRotate k ∈ R

end cyclic

end BKAbsorption


