-- Prove2me | Definitions.Def_FewInnerTSP_State
-- name    : FewInnerTSP_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:11.896597+00:00
-- url     : https://prove2.me/theorems/c69de1b4-c50f-459a-8e93-f2cf9f316ce7
-- title:
--   Recursive states, feasible path covers, induced matchings and completion domination (Definition 5.1)
-- statement:
--   A **state** on a skeleton $\Gamma$ is $S=(V=A\sqcup H,B,E,F)$ with edge weights $w$: core vertices $A$, skeleton vertices $H$, terminals $B\subseteq V$, allowed edges $E$ (with identities) and mandatory edges $F\subseteq E$. It is **well-formed** when $A$ avoids the skeleton, $H$ lies on it, every allowed free edge has distinct endpoints in $V$ with one in $A$, and every allowed skeleton edge has both endpoints in $V$. The weights are arbitrary reals. The required degree is $r(v)=1$ for $v\in B$ and $r(v)=2$ otherwise.
--
--   1. A **feasible cover** is an edge set $C$ with $F\subseteq C\subseteq E$, degree $r(v)$ at every $v\in V$, and no closed component (every vertex is connected to a terminal). It is a spanning disjoint union of nontrivial paths with endpoints exactly $B$.
--   2. Its **matching** $M(C)$ pairs the two terminals of each path. An **external matching** $X$ is a perfect matching on $B$; $M$ and $X$ are **compatible** if the multigraph $M\cup X$ is connected on $B$.
--   3. **Completion domination** (Definition 5.1): a family $\mathcal R$ dominates packing-compliant covers of $S$ if every member is a feasible cover of $S$, and for every feasible cover $C$ with packing-compliant free edges and every external matching $X$ compatible with $M(C)$ there is $R\in\mathcal R$ with
--   $$w(R)\le w(C),\qquad M(R)\cup X\ \text{connected}.$$
--
--   These conventions give the page's: the empty state has the one empty cover, and a nonempty state with $B=\emptyset$ or $|B|$ odd has none.
--
--   **Formalization Note** Feasibility of every representative is part of domination, as the page says; without it a family of arbitrary edge sets would qualify.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §5.1 and Definition 5.1, p.9 (PDF p.11); §4, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_FewInnerTSP_Packing

namespace FewInnerTSP

/-- **A recursive state** `S = (V = A ⊔ H, B, E, F)`: the core vertices `A`, the skeleton vertices `H`,
the terminals `B`, the remaining allowed edges `E` with their identities, the remaining mandatory edges
`F`, and the assigned edge weights `w`.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), §5.1, p.9 (PDF p.11).

**Formalization Note** The weights are arbitrary here, because Lemma 5.4 is claimed for arbitrary
assigned weights. The geometry stays that of the fixed points `P`. -/
structure State (n m : ℕ) where
  A : Finset (Fin n)
  H : Finset (Fin n)
  B : Finset (Fin n)
  E : Finset (Edge n m)
  F : Finset (Edge n m)
  w : Edge n m → ℝ

/-- The vertex set `V = A ∪ H` of a state. -/
def State.V {n m : ℕ} (S : State n m) : Finset (Fin n) := S.A ∪ S.H

/-- The required residual degree: `r(v) = 1` for `v ∈ B` and `r(v) = 2` otherwise.
Source: Li, Ma, Gong, §5.1, p.9 (PDF p.11). -/
def State.req {n m : ℕ} (S : State n m) (v : Fin n) : ℕ := if v ∈ S.B then 1 else 2

/-- The weight of a set of edges under the state's weights. -/
noncomputable def State.wtOf {n m : ℕ} (S : State n m) (C : Finset (Edge n m)) : ℝ :=
  ∑ e ∈ C, S.w e

/-- **A well-formed state on the skeleton `Γ`.** `A` and `H` are disjoint; `H` consists of skeleton
vertices and `A` of non-skeleton vertices; `B ⊆ V`, `F ⊆ E`; an allowed free edge has distinct endpoints
in `V` and at least one in `A`, and an allowed skeleton edge has both endpoints in `V`.
Source: Li, Ma, Gong, §4, p.5 (PDF p.7): "Allowed free edges are always incident to A"; §5.1, p.9
(PDF p.11). -/
structure IsState {n m : ℕ} (Γ : Skeleton n m) (S : State n m) : Prop where
  disjoint : Disjoint S.A S.H
  H_sub : ∀ v ∈ S.H, ∃ j, Γ.vert j = v
  A_not : ∀ v ∈ S.A, ∀ j, Γ.vert j ≠ v
  B_sub : S.B ⊆ S.V
  F_sub : S.F ⊆ S.E
  free_ok : ∀ e, Edge.free e ∈ S.E → ¬ e.IsDiag ∧ (∀ v ∈ e, v ∈ S.V) ∧ ∃ v ∈ e, v ∈ S.A
  skel_ok : ∀ j, Edge.skel j ∈ S.E → ∀ v ∈ Γ.ends (Edge.skel j), v ∈ S.V

/-- **A feasible cover**: a spanning disjoint union of nontrivial paths with endpoints exactly `B`. It
includes `F`, uses only `E`, has the residual degree `r(v)` at every `v ∈ V`, and has no closed
component.
Source: Li, Ma, Gong, §5.1, p.9 (PDF p.11).

**Formalization Note** With these degrees a component is a path or a closed cycle, and it is a path
exactly when it contains a terminal; so "no closed component" reads: every vertex reaches a terminal.
This gives the page's conventions: the empty state has the one empty cover, and a nonempty state with
`B = ∅` or odd `|B|` has none. -/
structure IsFeasibleCover {n m : ℕ} (Γ : Skeleton n m) (S : State n m) (C : Finset (Edge n m)) :
    Prop where
  sub_E : C ⊆ S.E
  F_sub : S.F ⊆ C
  degree : ∀ v ∈ S.V, edgeDeg Γ C v = S.req v
  no_closed : ∀ v ∈ S.V, ∃ b ∈ S.B, edgeReach Γ C v b

open Classical in
/-- The perfect matching `M(C)` on `B` induced by a cover: the two endpoints of each path are paired.
Source: Li, Ma, Gong, §5.1, p.9 (PDF p.11). -/
noncomputable def matchingOf {n m : ℕ} (Γ : Skeleton n m) (S : State n m)
    (C : Finset (Edge n m)) : Finset (Sym2 (Fin n)) :=
  ((S.B ×ˢ S.B).filter fun p => p.1 ≠ p.2 ∧ edgeReach Γ C p.1 p.2).image fun p => s(p.1, p.2)

/-- `X` is a perfect matching on `B`: its pairs have distinct endpoints in `B`, and every element of
`B` lies in exactly one pair. An external matching is a perfect matching on the terminals.
Source: Li, Ma, Gong, §5.1, p.9 (PDF p.11). -/
def IsPerfectMatching {α : Type*} (B : Finset α) (X : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ X, ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ B) ∧ ∀ v ∈ B, ∃! e, e ∈ X ∧ v ∈ e

/-- **Compatibility**: the multigraph `M ∪ X` on `B` is connected.
Source: Li, Ma, Gong, §5.1, p.9 (PDF p.11). -/
def Compatible {α : Type*} (B : Finset α) (M X : Finset (Sym2 α)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, Relation.ReflTransGen (fun a b => s(a, b) ∈ M ∨ s(a, b) ∈ X) x y

/-- **Completion domination (Definition 5.1).** Every member of `ℛ` is a feasible cover of `S`, and for
every feasible cover `C` with packing-compliant free edges and every external matching `X` compatible
with `C` there is `R ∈ ℛ` with `w(R) ≤ w(C)` and `M(R) ∪ X` connected. The representatives need not be
packing-compliant.
Source: Li, Ma, Gong, Definition 5.1, p.9 (PDF p.11).

**Formalization Note** Without feasibility of the representatives a family of junk edge sets would
qualify, so it is part of the definition, as the page says. -/
def Dominates {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (S : State n m)
    (ℛ : Finset (Finset (Edge n m))) : Prop :=
  (∀ R ∈ ℛ, IsFeasibleCover Γ S R) ∧
  ∀ C, IsFeasibleCover Γ S C → IsPackingCompliant P (freeEdges C) →
    ∀ X, IsPerfectMatching S.B X → Compatible S.B (matchingOf Γ S C) X →
      ∃ R ∈ ℛ, S.wtOf R ≤ S.wtOf C ∧ Compatible S.B (matchingOf Γ S R) X

end FewInnerTSP


