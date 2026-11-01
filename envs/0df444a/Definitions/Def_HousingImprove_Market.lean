-- Prove2me | Definitions.Def_HousingImprove_Market
-- name    : HousingImprove_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:18.361087+00:00
-- url     : https://prove2.me/theorems/c7a9a788-d0b3-4b8c-b87c-3b48fefce2d6
-- title:
--   Housing markets with partial-order preferences, allocations and the core
-- statement:
--   A **housing market** $H=(N,\{\prec_a\}_{a\in N})$ consists of a set $N$ of agents, each owning one house, and for each agent $c$ an irreflexive partial ordering $\prec_c$ of the agents (an irreflexive, antisymmetric and transitive relation). We read $a\prec_c b$ as: agent $c$ prefers the house of $b$ to the house of $a$.
--
--   Agent $a$ finds the house of $b$ **acceptable** if $b\not\prec_a a$, i.e. $a\preceq_a b$; the set of such $b$ is $A(a)$, and the arcs $(a,b)$, $b\in A(a)$, form the acceptability graph $G^H$, which contains every loop $(a,a)$. An **allocation** is a permutation $X$ of $N$ such that every agent $a$ finds $X(a)$, the house it obtains, acceptable. An arc $(a,b)$ is **$X$-augmenting** if $X(a)\prec_a b$, and $X$ is in the **core** of $H$ if the graph of $X$-augmenting arcs (the envy graph $G^H_{X\prec}$) has no cycle, i.e. no set of agents can trade among themselves so that every one of them obtains a house it strictly prefers.
--
--   For $W\subseteq N$, the **submarket** $H_W$ has agent set $W$ and the orders $\prec_a$, $a\in W$, restricted to $W$.
--
--   These are the basic objects of the whole mission.
--
--   **Formalization Note** `H.lt c a b` is $a\prec_c b$; each relation is an `IsStrictOrder` on all of $N$, with no comparability assumed. An allocation is an `Equiv.Perm N` together with acceptability; acyclicity of the envy graph is `¬ Relation.TransGen r a a` for every $a$, with $r\,a\,b :\Leftrightarrow X(a)\prec_a b$.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §2.1–2.2, pp.6–7 (partial orderings, housing market, acceptability, allocation, core, submarket)

import Mathlib

namespace HousingImprove

universe u

/-- A **housing market** with partial-order preferences (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, §2.1–2.2, p.6): every agent `c ∈ N` owns one house and ranks the houses of all
agents by an (irreflexive) partial ordering `≺_c`. `H.lt c a b` is `a ≺_c b`: **agent `c` prefers the
house of `b` to the house of `a`**.

**Formalization Note.** An irreflexive partial ordering ("an irreflexive, antisymmetric and
transitive relation", p.6) is `IsStrictOrder` (antisymmetry follows from irreflexivity and
transitivity). Each relation is on all of `N`; no totality or comparability is assumed. -/
structure Market (N : Type u) where
  /-- `lt c a b` means `a ≺_c b`: agent `c` prefers the house of `b` to the house of `a`. -/
  lt : N → N → N → Prop
  /-- Each `≺_c` is an irreflexive partial ordering. -/
  isStrictOrder : ∀ c, IsStrictOrder N (lt c)

variable {N : Type u}

/-- Agent `a` finds the house of `b` **acceptable** if `a ⪯_a b`, that is, `b ⊀_a a`
(arXiv:2110.06875v3, p.6: "`A(a) = {b ∈ N : a ⪯_a b}`"). A house incomparable to `a`'s own house is
acceptable; `(a, b)` is then an arc of the acceptability graph `G^H`, and `(a, a)` always is. -/
def Market.Acceptable (H : Market N) (a b : N) : Prop :=
  ¬ H.lt a b a

/-- An **allocation** (p.6): a permutation `X` of `N` (agent `a` obtains the house of `X a`) whose
arcs `(a, X a)` lie in `G^H`, i.e. every agent finds the house it obtains acceptable.

**Formalization Note.** "A subset `X ⊆ E` with `δ⁻_X(a) = δ⁺_X(a) = 1` for each `a`" is a
permutation all of whose arcs are acceptable. -/
def Market.IsAllocation (H : Market N) (X : Equiv.Perm N) : Prop :=
  ∀ a, H.Acceptable a (X a)

/-- An allocation `X` is in the **core** of `H` (pp.6–7) if its envy graph `G^H_{X≺}`, whose arcs are
the `X`-augmenting arcs `(a, b)` with `X(a) ≺_a b`, is acyclic: no cycle `C` exists on which every
agent prefers `C(a)` to `X(a)`.

**Formalization Note.** Acyclicity is `¬ TransGen r a a` for every `a`, where `r a b := X(a) ≺_a b`.
An `X`-augmenting arc is automatically an arc of `G^H`, since `X(a)` is acceptable to `a` and `≺_a`
is transitive. -/
def Market.IsCore (H : Market N) (X : Equiv.Perm N) : Prop :=
  H.IsAllocation X ∧ ∀ a, ¬ Relation.TransGen (fun a b => H.lt a (X a) b) a a

/-- The **submarket** `H_W` (p.6): agents in `W`, each `≺_a` (`a ∈ W`) restricted to `W`. -/
def Market.restrict (H : Market N) (W : Set N) : Market W where
  lt c a b := H.lt c a b
  isStrictOrder c :=
    { irrefl := fun a => (H.isStrictOrder c).irrefl a.1
      trans := fun a b d h₁ h₂ => (H.isStrictOrder c).trans a.1 b.1 d.1 h₁ h₂ }

end HousingImprove


