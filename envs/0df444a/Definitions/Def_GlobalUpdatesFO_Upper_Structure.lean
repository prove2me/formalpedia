-- Prove2me | Definitions.Def_GlobalUpdatesFO_Upper_Structure
-- name    : GlobalUpdatesFO_Upper_Structure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:19:49.484565+00:00
-- url     : https://prove2.me/theorems/b9ade709-7c9f-494e-ade9-dc0ac1851bef
-- title:
--   Relational signatures with nullary relations, Σ-structures, Gaifman graph, treedepth, induced substructures, disjoint unions, components and structure codes
-- statement:
--   A **signature** $\Sigma$ is a finite list of nonnegative integers: the relation names are $0, 1, \dots, |\Sigma|-1$ and the $R$-th entry is $\mathrm{arity}(R)$. Arity $0$ is allowed (a **nullary relation** is a truth value). $\mathrm{maxarity}(\Sigma)$ is the largest arity ($0$ for the empty signature).
--
--   A **$\Sigma$-structure** $A$ on a universe $U$ assigns to each relation $R$ a set $R(A) \subseteq U^{\mathrm{arity}(R)}$ of ordered tuples; a tuple is a map $\{0,\dots,\mathrm{arity}(R)-1\} \to U$, and entries may repeat.
--
--   The **Gaifman graph** $G(A)$ has vertex set $U$ and an edge between distinct $u, v$ whenever some tuple of some relation contains both. The **treedepth** of $A$ is
--   $$\mathrm{td}(A) = \mathrm{td}(G(A)),$$
--   the minimum height of an elimination forest of $G(A)$ (the published graph treedepth `SNPTreedepth.treedepth`; the empty graph has treedepth $0$).
--
--   For $K \subseteq U$, the **induced substructure** $A[K]$ has universe $K$ and keeps the tuples all of whose entries lie in $K$ (nullary relations keep their value); $A \setminus K = A[U \setminus K]$. The **disjoint union** of structures $A_i$ ($i \in \iota$) lives on the tagged universe $\{(i, u) : u \in U(A_i)\}$; its positive-arity relations are the unions of the tagged relations. The **component structure** $A[C]$ of a connected component $C$ of $G(A)$ is the substructure induced by $C$.
--
--   A list of numbers $c$ is a **code** of a structure $A$ on $\{0,\dots,n-1\}$ if it is $n$ followed, for $R = 0, 1, \dots$ in turn, by the number of tuples of $R(A)$ and then these tuples written entrywise, each tuple listed exactly once and in any order. Finally, $\mathrm{td}$ of an induced subgraph $G[S]$ is provided for the graph $G(A) \setminus K$ of §4.1.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** A universe is a Lean type with a `Fintype` instance where finiteness matters. The paper requires the summands of a disjoint union to agree on nullary relations; here a nullary relation holds in the union iff it holds in some summand, which is the paper's value whenever they agree and there is at least one summand.
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), pp. 16–17, §3.3; p. 15, §3.1 (treedepth); p. 24, §3.8; p. 2 and p. 46 (input lists)

import Mathlib
import Definitions.Def_SNPTreedepth_treedepth

set_option autoImplicit false

namespace GlobalUpdatesFO.Upper

/-- A **relational signature** (Korhonen, Sokołowski, *On efficient global updates in first-order
logic*, STOC 2027 submission, §3.3, p. 16): finitely many relation names, each with a nonnegative
arity. The relation names are `0, 1, …, |Σ| − 1` and `Σ` is the list of their arities; arity `0`
(a nullary relation, i.e. a truth value) is allowed. -/
abbrev Signature := List ℕ

/-- `maxarity(Σ)`: the maximum arity of a relation of `Σ`, or `0` for the empty signature. -/
def Signature.maxarity (σ : Signature) : ℕ := σ.foldr max 0

/-- A **`Σ`-structure** on the universe `U` (§3.3, p. 16): for each relation `R ∈ Σ` its
interpretation `R(A) ⊆ U^{arity(R)}`, a set of ordered tuples (entries may repeat). A tuple is a map
`Fin (arity R) → U`. -/
structure Structure (σ : Signature) (U : Type*) where
  /-- the interpretation `R(A)` of each relation `R` -/
  rel : (R : Fin σ.length) → Set (Fin (σ.get R) → U)

namespace Structure

variable {σ : Signature} {U : Type*}

/-- The **Gaifman graph** `G(A)` (§3.3, p. 16): vertex set `U(A)`, and an edge between two distinct
vertices `u, v` if some tuple of some relation contains both. -/
def gaifman (A : Structure σ U) : SimpleGraph U where
  Adj u v := u ≠ v ∧ ∃ (R : Fin σ.length) (t : Fin (σ.get R) → U),
    t ∈ A.rel R ∧ u ∈ Set.range t ∧ v ∈ Set.range t
  symm := ⟨fun _ _ h => ⟨fun e => h.1 e.symm, by
    obtain ⟨R, t, ht, hu, hv⟩ := h.2
    exact ⟨R, t, ht, hv, hu⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The **treedepth** `td(A) = td(G(A))` (§3.3, p. 16), with the graph treedepth of p. 15 (minimum
height of an elimination forest; `0` for the empty graph). -/
noncomputable def td [Fintype U] (A : Structure σ U) : ℕ :=
  SNPTreedepth.treedepth A.gaifman

/-- The **induced substructure** `A[K]` (§3.3, p. 16): universe `K`, containing the tuples all of
whose members belong to `K`. Nullary relations keep their truth value. -/
def induced (A : Structure σ U) (K : Set U) : Structure σ K where
  rel R := {t | (fun i => (t i : U)) ∈ A.rel R}

/-- `A \ K := A[U(A) \ K]` (§3.3, p. 16). -/
def remove (A : Structure σ U) (K : Set U) : Structure σ ↥(Kᶜ) :=
  A.induced Kᶜ

/-- The **disjoint union** `A₁ ⊎ … ⊎ A_t` (§3.8, p. 24) of structures indexed by `ι`, on the sigma
type `Σ i, V i` (the universes are made disjoint by tagging). A positive-arity relation is the union
of the tagged relations of the summands.

**Formalization Note** The paper requires all nullary predicates to agree in the summands; here a
nullary relation holds in the union iff it holds in some summand, which is the paper's value whenever
the summands agree and the index set is nonempty. -/
def disjointUnion {ι : Type*} {V : ι → Type*} (A : (i : ι) → Structure σ (V i)) :
    Structure σ (Σ i, V i) where
  rel R := {t | ∃ (i : ι) (s : Fin (σ.get R) → V i), s ∈ (A i).rel R ∧ t = fun j => ⟨i, s j⟩}

/-- The substructure `A[C]` induced by a **connected component** `C` of `A`, i.e. of `G(A)`
(§3.8, p. 24). -/
def component (A : Structure σ U) (C : A.gaifman.ConnectedComponent) :
    Structure σ ↥{u : U | A.gaifman.connectedComponentMk u = C} :=
  A.induced {u : U | A.gaifman.connectedComponentMk u = C}

/-- `c` is a **code of the structure** `A` on `Fin n` given by the lists of its relation tuples
(§1, p. 3; §5.1, p. 46): the number `n`, then for each relation `R = 0, 1, …, |Σ| − 1` in turn the
number of its tuples followed by the tuples, each tuple of `R(A)` listed exactly once and in any
order, each tuple written entrywise. -/
def IsCode {n : ℕ} (A : Structure σ (Fin n)) (c : List ℕ) : Prop :=
  ∃ L : (R : Fin σ.length) → List (Fin (σ.get R) → Fin n),
    (∀ R, (L R).Nodup ∧ ∀ t, t ∈ L R ↔ t ∈ A.rel R) ∧
    c = n :: (List.finRange σ.length).flatMap
      (fun R => (L R).length :: (L R).flatMap (fun t => List.ofFn (fun i => (t i).val)))

end Structure

/-- Treedepth of the induced subgraph `G[S]` of a finite graph (used for `G(A) \ K`, §4.1, p. 26). -/
noncomputable def tdInduce {U : Type*} [Fintype U] (G : SimpleGraph U) (S : Set U) : ℕ := by
  classical
  exact SNPTreedepth.treedepth (G.induce S)

end GlobalUpdatesFO.Upper


