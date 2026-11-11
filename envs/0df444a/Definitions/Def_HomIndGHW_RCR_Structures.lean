-- Prove2me | Definitions.Def_HomIndGHW_RCR_Structures
-- name    : HomIndGHW_RCR_Structures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:00:10.379953+00:00
-- url     : https://prove2.me/theorems/1dfaea4d-d72a-491e-a2c6-5bec1f12b466
-- title:
--   Signatures, σ-structures, coloured tuples, homomorphisms, #Hom, Gaifman graph, connectivity, no isolated elements
-- statement:
--   A **finite relational signature** $\sigma$ is a finite set of relation symbols $R$, each with a positive integer arity $\mathrm{ar}(R)$; $\mathrm{ar}(\sigma)$ is the maximum arity, and $\sigma$ is **binary** when every arity is at most $2$. A **$\sigma$-structure** $\mathcal A$ consists of a domain $A$ and, for every $R\in\sigma$, a relation $R^{\mathcal A}\subseteq A^{\mathrm{ar}(R)}$ of ordered tuples (entries may repeat). A **coloured tuple** $R(\bar t)$ is a symbol together with a tuple $\bar t\in R^{\mathcal A}$; $\mathrm{CT}(\mathcal A)$ is the set of them, and $\mathrm{set}(\bar t)$ is the set of entries of $\bar t$.
--
--   A map $h:A\to B$ is a **homomorphism** $\mathcal A\to\mathcal B$ if $h(\bar t)\in R^{\mathcal B}$ for every $R$ and every $\bar t\in R^{\mathcal A}$; $\mathrm{Hom}(\mathcal A,\mathcal B)$ is the set of them and
--   $$\#\mathrm{Hom}(\mathcal A,\mathcal B)=|\mathrm{Hom}(\mathcal A,\mathcal B)| .$$
--   The **Gaifman graph** has vertex set $A$ and joins $x\neq y$ when some tuple of some relation contains both; $\mathcal A$ is **connected** when its Gaifman graph is. $\mathcal A$ has **no isolated elements** (Remark 2.1) when every $x\in A$ occurs in some tuple of some relation.
--
--   These are the basic objects of every statement of the mission.
--
--   **Formalization Note.** Symbols form an arbitrary finite type `Sym` with `ar_pos`; the total order $\preceq_\sigma$ used by profiles is a separate `[LinearOrder σ.Sym]` binder. A tuple of length $a$ is a function `Fin a → V`; finiteness of domains is imposed by `[Fintype V]` binders. `homCount` is `Nat.card` of the subtype of homomorphisms, the ordinary cardinality for finite domains. Connectivity uses Mathlib's `SimpleGraph.Connected`, which also requires a nonempty domain. The published `SNPTreedepth_Structure` is not reused: the $k$-exploded signature $\hat\sigma_k$ is naturally a sum type of profiles and index pairs, not `Fin b`.
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), pp. 4–6 and 13–15, §1.2, §1.3.1, §2 (Remark 2.1)

import Mathlib

set_option autoImplicit false

namespace HomIndGHW.RCR

/-!
# Signatures, relational structures, coloured tuples, homomorphisms, connectivity

Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, *Homomorphism Indistinguishability Beyond
Graphs*, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), §2, pp. 14–15
(and §1.2, p. 5; §1.3.1, p. 6).
-/

/-- A **finite relational signature** (p. 14): a finite set of relation symbols, each with a
positive arity `ar R`.

**Formalization Note** The symbols form an arbitrary finite type `Sym`; `ar_pos` is the paper's
standing assumption that every arity is a positive integer (p. 5, p. 14). The total order `⪯σ`
on symbols that §1.3 and §3 fix is supplied separately as a `[LinearOrder σ.Sym]` binder wherever
it is used. -/
structure Sig where
  /-- the relation symbols -/
  Sym : Type
  /-- there are finitely many relation symbols -/
  [fin : Fintype Sym]
  /-- the arity `ar(R)` -/
  ar : Sym → ℕ
  /-- every arity is positive -/
  ar_pos : ∀ R, 0 < ar R

attribute [instance] Sig.fin

/-- The arity `ar(σ)` of a signature: the maximum arity of its symbols (p. 14). -/
def Sig.maxAr (σ : Sig) : ℕ := Finset.univ.sup σ.ar

/-- A signature is **binary** when every symbol has arity at most `2` (§2, p. 15). -/
def Sig.IsBinary (σ : Sig) : Prop := ∀ R, σ.ar R ≤ 2

/-- A **σ-structure** with domain `V` (p. 14): for every symbol `R` a relation
`R^A ⊆ V^{ar(R)}` of ordered tuples (entries may repeat).

**Formalization Note** A tuple of length `a` is a function `Fin a → V`. Finiteness of the domain is
imposed by `[Fintype V]` binders in the statements. -/
structure Structure (σ : Sig) (V : Type*) where
  /-- the relation `R^A` -/
  rel : (R : σ.Sym) → Set (Fin (σ.ar R) → V)

namespace Structure

variable {σ : Sig} {V : Type*} {W : Type*}

/-- **No isolated elements** (Remark 2.1, p. 14; Remark 3.1, p. 18): every domain element occurs in
some tuple of some relation. -/
def NoIsolated (A : Structure σ V) : Prop :=
  ∀ x : V, ∃ R : σ.Sym, ∃ t ∈ A.rel R, ∃ j, t j = x

/-- A map `h : V → W` is a **homomorphism** `A → B` (p. 15): `h(t̄) ∈ R^B` for every symbol `R`
and every `t̄ ∈ R^A`. -/
def IsHom (A : Structure σ V) (B : Structure σ W) (h : V → W) : Prop :=
  ∀ (R : σ.Sym) (t : Fin (σ.ar R) → V), t ∈ A.rel R → h ∘ t ∈ B.rel R

/-- `#Hom(A, B)`, the number of homomorphisms `A → B` (p. 15). It is a finite cardinality whenever
the domains are finite, which every statement assumes. -/
noncomputable def homCount (A : Structure σ V) (B : Structure σ W) : ℕ :=
  Nat.card {h : V → W // IsHom A B h}

/-- The **Gaifman graph** (p. 14): vertices the domain, `x ~ y` iff `x ≠ y` and some tuple of some
relation contains both. -/
def gaifman (A : Structure σ V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ R : σ.Sym, ∃ t ∈ A.rel R, (∃ i, t i = x) ∧ (∃ j, t j = y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim fun R hR => ⟨R, hR.elim fun t ht =>
    ⟨t, ht.1, ht.2.2, ht.2.1⟩⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A structure is **connected** when its Gaifman graph is connected.

**Formalization Note** The paper does not define connectivity; this is the standard reading. Mathlib's
`SimpleGraph.Connected` also requires a nonempty domain, so the empty structure is not connected
(it has exactly one homomorphism into every structure, so it never separates two structures). -/
def Connected (A : Structure σ V) : Prop := (gaifman A).Connected

/-- A **coloured tuple** `R(t̄)` of `A` (p. 6, p. 14): a symbol `R` together with a tuple
`t̄ ∈ R^A`. `CT(A)` is the type of them. -/
def CT (A : Structure σ V) : Type _ :=
  {p : (Σ R : σ.Sym, Fin (σ.ar R) → V) // p.2 ∈ A.rel p.1}

namespace CT

variable {A : Structure σ V}

/-- the relation symbol `R` of `R(t̄)` -/
def sym (c : CT A) : σ.Sym := c.1.1

/-- the tuple `t̄` of `R(t̄)` -/
def tup (c : CT A) : Fin (σ.ar c.sym) → V := c.1.2

/-- the tuple `t̄` as a list `[t̄[1], …, t̄[ar R]]` -/
def toList (c : CT A) : List V := List.ofFn c.tup

/-- `x ∈ set(t̄)`: the element `x` occurs in the tuple (p. 14). -/
def Mem (c : CT A) (x : V) : Prop := ∃ j, c.tup j = x

end CT

instance instFiniteCT [Finite V] (A : Structure σ V) : Finite (CT A) := by
  unfold CT; infer_instance

noncomputable instance instFintypeCT [Finite V] (A : Structure σ V) : Fintype (CT A) :=
  Fintype.ofFinite _

end Structure

end HomIndGHW.RCR


