-- Prove2me | Definitions.Def_SNPTreedepth_Structure
-- name    : SNPTreedepth_Structure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:27.664202+00:00
-- url     : https://prove2.me/theorems/31ce46cf-3c84-4148-8889-255eabae4562
-- title:
--   Signatures, relational structures, size $|R|$, Gaifman graph, induced substructures
-- statement:
--   A **signature** is a sequence $(\mathrm{ar}(E_1),\dots,\mathrm{ar}(E_b))$ of positive arities. A **relational structure** $R=(V,E_1,\dots,E_b)$ over it consists of a domain $V$ and relations $E_i\subseteq V^{\mathrm{ar}(E_i)}$; tuples are ordered and may repeat entries. Its **size** is
--   $$
--   |R| \;=\; |V| + \sum_{i=1}^{b}\sum_{\bar u\in E_i}|\bar u| \;=\; |V|+\sum_{i=1}^{b}\mathrm{ar}(E_i)\,|E_i| .
--   $$
--   The **Gaifman graph** of $R$ has vertex set $V$ and an edge $\{v,w\}$, $v\neq w$, whenever $v$ and $w$ occur together in some tuple of some relation. For $U\subseteq V$ the **induced substructure** $R[U]=(U,E_1\cap U^{\mathrm{ar}(E_1)},\dots,E_b\cap U^{\mathrm{ar}(E_b)})$ keeps exactly the tuples with all entries in $U$. Two structures over the same signature are **isomorphic** if a bijection of the domains preserves and reflects every relation, and $W$ **embeds as an induced substructure** in $R$ if an injective map does so, i.e. $R$ contains an induced substructure isomorphic to $W$.
--
--   These are the objects on which the whole mission runs: the input of SNP Model Checking, the measure $|R|$ of its running times, and the induced-substructure order behind obstruction sets.
--
--   **Formalization Note** Relations are indexed by $\mathrm{Fin}\,b$ and tuples are functions $\mathrm{Fin}\,a\to V$. Positivity of the arities is part of the signature (the paper's standing assumption, Definition 12). Finiteness and non-emptiness of the domain, and the paper's fixed total order on $V$, are imposed by the statements that need them; an input structure on $\mathrm{Fin}\,n$ carries the order of $\mathrm{Fin}\,n$. $R[U]$ lives on the subtype $U$ with the inherited order.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definitions 12 and 13, p.14 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace SNPTreedepth

/-- A **signature** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict
NP on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…),
Definition 13, p.14): the sequence `(ar(E₁), …, ar(E_b))` of the arities of the relations of a
relational structure.

**Formalization Note** Relations are indexed by `Fin b` (the paper's `[b]`, shifted to start at
`0`). The field `ar_pos` is the paper's standing assumption of Definition 12, p.14: "Throughout the
paper we assume that all relations have positive arity." -/
structure Signature where
  /-- the number `b` of relations -/
  b : ℕ
  /-- the arity `ar(E_i)` of each relation -/
  ar : Fin b → ℕ
  /-- every relation has positive arity (Definition 12) -/
  ar_pos : ∀ i, 0 < ar i

/-- A **relational structure** `R = (V, E₁, …, E_b)` over the signature `σ`
(Depian et al., STOC 2027 submission (manuscript sha256 98e4e1a9…), Definition 12, p.14): a domain
`V` and, for every `i`, a relation `E_i ⊆ V^{ar(E_i)}`.

**Formalization Note** The domain is the type `V`; a tuple of length `a` is a function
`Fin a → V` (tuples are ordered and may repeat entries, p.14). The paper's requirement that the
domain be non-empty and finite is imposed where a statement needs it, by `[Fintype V]` and
`[Nonempty V]` binders. The paper's fixed total order on `V(R)` (p.14) is a `[LinearOrder V]`
binder wherever it is used; for an input structure on `Fin n` it is the order of `Fin n`. -/
structure Structure (σ : Signature) (V : Type*) where
  /-- the relation `E_i` -/
  rel : (i : Fin σ.b) → Set (Fin (σ.ar i) → V)

namespace Structure

variable {σ : Signature} {V : Type*}

/-- The **size** `|R| := |V| + Σ_{i=1}^{b} Σ_{u ∈ E_i} |u|` of a relational structure
(Depian et al., Definition 12, p.14). Each tuple of `E_i` has `|u| = ar(E_i)` entries, so the
inner sum is `ar(E_i) · |E_i|`.

**Formalization Note** Cardinalities are `Nat.card` / `Set.ncard`; every statement that uses the
size has a finite domain, where these are the ordinary cardinalities. -/
noncomputable def size (R : Structure σ V) : ℕ :=
  Nat.card V + ∑ i : Fin σ.b, σ.ar i * (R.rel i).ncard

/-- The **Gaifman graph** of a relational structure (Depian et al., Definition 12, p.14): vertex set
`V`, and an edge `{v, w}` for `v ≠ w` exactly when `v` and `w` appear together in at least one
tuple of a relation, that is, there are `i` and `ū ∈ E_i` with `v ∈ ū` and `w ∈ ū`. -/
def gaifman (R : Structure σ V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ i : Fin σ.b, ∃ u ∈ R.rel i, (∃ j, u j = v) ∧ (∃ j, u j = w)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim fun i hi => ⟨i, hi.elim fun u hu =>
    ⟨u, hu.1, hu.2.2, hu.2.1⟩⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The **substructure induced** by a set `U ⊆ V` (Depian et al., Definition 13, p.14):
`R[U] = (U, E₁ ∩ U^{ar(E₁)}, …, E_b ∩ U^{ar(E_b)})`, keeping exactly the tuples all of whose
entries lie in `U`.

**Formalization Note** The domain of `R[U]` is the subtype `↥U`; with a `[LinearOrder V]` it carries
the restricted order, so the induced structure keeps the inherited total order. -/
def induce (R : Structure σ V) (U : Set V) : Structure σ U where
  rel i := {u | (fun j => (u j : V)) ∈ R.rel i}

/-- An **isomorphism** of relational structures over the same signature: a bijection `e` of the
domains that preserves and reflects every relation, `ū ∈ E_i ↔ e ∘ ū ∈ E'_i`. The paper uses the
standard notion (Definition 30, p.30, "isomorphism class"; Lemma 32, p.30). -/
def IsIso {W : Type*} (X : Structure σ V) (Y : Structure σ W) : Prop :=
  ∃ e : V ≃ W, ∀ (i : Fin σ.b) (u : Fin (σ.ar i) → V), u ∈ X.rel i ↔ (e ∘ u) ∈ Y.rel i

/-- `W` **embeds as an induced substructure** into `R`: there is an injective map `f` of the domains
with `ū ∈ E_i^W ↔ f ∘ ū ∈ E_i^R` for every relation and tuple. Equivalently, `R` contains an induced
substructure (on the image of `f`) isomorphic to `W` (Depian et al., Lemma 32, p.30: "R contains an
induced substructure isomorphic to W"). -/
def EmbedsInduced {W : Type*} (X : Structure σ W) (R : Structure σ V) : Prop :=
  ∃ f : W → V, Function.Injective f ∧
    ∀ (i : Fin σ.b) (u : Fin (σ.ar i) → W), u ∈ X.rel i ↔ (f ∘ u) ∈ R.rel i

end Structure

end SNPTreedepth


