-- Prove2me | Definitions.Def_ChvatalPolytopes_Substitution_substitute
-- name    : ChvatalPolytopes_Substitution_substitute
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:56:41.164229+00:00
-- url     : https://prove2.me/theorems/bc202131-690a-45d5-b2ae-b7ffd24b6051
-- title:
--   Substituting a graph $G_2$ for a vertex $v$ of $G_1$ (§5)
-- statement:
--   Let $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ be graphs without common vertices, and let $v$ be a vertex of $G_1$. The graph obtained from $G_1$ by **substituting $G_2$ for $v$** is the disjoint union of $G_1-v$ and $G_2$ together with additional edges that join each vertex of $G_2$ to each neighbour of $v$.
--
--   Its vertex set is $(V_1-\{v\})\cup V_2$, and two vertices $p,q$ are adjacent exactly when
--
--   1. $p,q\in V_1-\{v\}$ and $pq\in E_1$; or
--   2. $p,q\in V_2$ and $pq\in E_2$; or
--   3. one of them, say $p$, lies in $V_1-\{v\}$ and is adjacent to $v$ in $G_1$, and the other lies in $V_2$.
--
--   Duplicating a vertex is substitution of the edgeless graph on two vertices, the join $G_1+G_2$ is obtained by two substitutions into $K_2$, and substituting the same graph for every vertex gives the lexicographic product. Theorem 5.1 shows that substitution has a matching operation on defining linear systems of stable set polytopes.
--
--   **Formalization Note** The vertex type is the disjoint sum $\{u\in V_1 : u\neq v\}\oplus V_2$ (left summand $=V_1-\{v\}$, right summand $=V_2$), so the paper's hypothesis $V_1\cap V_2=\emptyset$ is built into the construction. Four `simp` lemmas record the adjacency relation case by case.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), pp. 144–145, §5 (definition of substitution)

import Mathlib

namespace ChvatalPolytopes.Substitution

/-- **Substitution** (Chvátal 1975, pp. 144–145). Let `G₁`, `G₂` be graphs without common
vertices and let `v` be a vertex of `G₁`. The graph obtained from `G₁` by *substituting `G₂`
for `v`* is the (disjoint) union of `G₁ − v` and `G₂` together with additional edges that join
each vertex of `G₂` to each neighbor of `v`.

Its vertex set is the disjoint sum `(V₁ − {v}) ⊕ V₂`, written `{u : V₁ // u ≠ v} ⊕ V₂`; the
disjointness `V₁ ∩ V₂ = ∅` of the paper is built into the sum type. Adjacency:
* `inl a ~ inl b` iff `a ~ b` in `G₁` (this is `G₁ − v`);
* `inr a ~ inr b` iff `a ~ b` in `G₂`;
* `inl a ~ inr w` (and `inr w ~ inl a`) iff `a` is a neighbor of `v` in `G₁`. -/
def substitute {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁) (G₂ : SimpleGraph V₂) :
    SimpleGraph ({u : V₁ // u ≠ v} ⊕ V₂) where
  Adj
    | .inl a, .inl b => G₁.Adj a b
    | .inr a, .inr b => G₂.Adj a b
    | .inl a, .inr _ => G₁.Adj a v
    | .inr _, .inl b => G₁.Adj b v
  symm := by
    constructor
    rintro (a | a) (b | b) h
    · exact G₁.adj_symm h
    · exact h
    · exact h
    · exact G₂.adj_symm h
  loopless := by
    constructor
    rintro (a | a) h
    · exact G₁.loopless.irrefl a h
    · exact G₂.loopless.irrefl a h

@[simp] theorem substitute_adj_inl_inl {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (a b : {u : V₁ // u ≠ v}) :
    (substitute G₁ v G₂).Adj (.inl a) (.inl b) ↔ G₁.Adj a b := Iff.rfl

@[simp] theorem substitute_adj_inr_inr {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (a b : V₂) :
    (substitute G₁ v G₂).Adj (.inr a) (.inr b) ↔ G₂.Adj a b := Iff.rfl

@[simp] theorem substitute_adj_inl_inr {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (a : {u : V₁ // u ≠ v}) (w : V₂) :
    (substitute G₁ v G₂).Adj (.inl a) (.inr w) ↔ G₁.Adj a v := Iff.rfl

@[simp] theorem substitute_adj_inr_inl {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (w : V₂) (b : {u : V₁ // u ≠ v}) :
    (substitute G₁ v G₂).Adj (.inr w) (.inl b) ↔ G₁.Adj b v := Iff.rfl

end ChvatalPolytopes.Substitution


