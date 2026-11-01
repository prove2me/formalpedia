-- Prove2me | Definitions.Def_FairFlows_Network
-- name    : FairFlows_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:18.923829+00:00
-- url     : https://prove2.me/theorems/27b05677-4797-4e77-8073-9138f19de2d3
-- title:
--   Digraphs, modular flows, bounds in $\mathbb Z\cup\{\pm\infty\}$, the sets $Q(f,g;m)$ and Q⃛$(f,g;m)$
-- statement:
--   A **digraph** $D=(V,A)$ is a finite node set $V$ and a finite edge set $A$, each edge $e$ having a tail and a head; parallel edges and loops are allowed. An edge $e$ **enters** $Z\subseteq V$ if its head is in $Z$ and its tail is not, and **leaves** $Z$ if its tail is in $Z$ and its head is not. For $x\in\mathbb R^A$ (or $\mathbb Z^A$) write $\varrho_x(Z)$ and $\delta_x(Z)$ for the sums of $x$ over the edges entering and leaving $Z$, and for $m:V\to\mathbb Z$ write $\widetilde m(Z)=\sum_{v\in Z}m(v)$.
--
--   1. A **modular flow** ($m$-flow) is a finite real vector $x\in\mathbb R^A$ with $\varrho_x(v)-\delta_x(v)=m(v)$ for every node $v$, where $\varrho_x(v)$ sums $x$ over the edges with head $v$ and $\delta_x(v)$ over the edges with tail $v$.
--   2. Bounds are $f:A\to\mathbb Z\cup\{-\infty\}$ and $g:A\to\mathbb Z\cup\{+\infty\}$; $f\le g$ means $f(e)\le g(e)$ in $\mathbb Z\cup\{\pm\infty\}$. A flow is **$(f,g)$-bounded** (feasible) if $f\le x\le g$, i.e. it lies in the box $T(f,g)$.
--   3. $Q=Q(f,g;m)$ is the set of $(f,g)$-bounded $m$-flows and $Q⃛=Q\cap\mathbb Z^A$ the set of its integral members.
--   4. An edge is **$(f,g)$-tight** if $f(e)=g(e)$; the condition $\varrho_g(Z)-\delta_f(Z)<+\infty$ means that every edge entering $Z$ has finite $g$ and every edge leaving $Z$ has finite $f$.
--   5. $g+\delta\chi_X$ changes $g$ by the integer $\delta$ on the edges of $X$ (so $g^-=g-\chi_L$), and the box is **narrow** at $e$ if $f(e)$, $g(e)$ are finite with $0\le g(e)-f(e)\le1$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** $\mathbb Z\cup\{-\infty\}$ is `WithBot ℤ` and $\mathbb Z\cup\{+\infty\}$ is `WithTop ℤ`; every comparison with a real or integer value is written termwise ("for every integer $k$, if $f(e)=k$ then $k\le x(e)$"), so no infinite arithmetic decides any case. Shifting $g$ uses `WithTop` addition, $+\infty+\delta=+\infty$; the mission only shifts edges with finite $g$.
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §1 p.3 (ϱ_x(v), δ_x(v)), §2.1 p.5 (digraph, bounds, tight edges, box, m̃, mod-flows, feasibility), §2.1 p.6 (Q, (2.3) Q⃛), Theorem 2.1 p.6 (narrow), pp.10, 13 (ϱ_g(Z) − δ_f(Z) < +∞), (4.1) p.10 (g − χ_L)

import Mathlib

set_option autoImplicit false

namespace FairFlows

open Finset

/-- A finite digraph `D = (V, A)` given by the tail and head of each edge (Frank, Murota,
*Fair integral network flows*, arXiv:1907.02673v5, §1 p.3 and §2.1 p.5).

**Formalization Note** Edges form a type `A` of their own with maps `tail head : A → V`, so
parallel edges are allowed (the paper's §§6, 8 add parallel copies); loops are allowed and are
harmless: a loop neither enters nor leaves any set, and it contributes to both `ϱ_x(v)` and
`δ_x(v)` at its node. -/
structure Digraph (V A : Type) where
  /-- the tail `u` of the edge `uv` -/
  tail : A → V
  /-- the head `v` of the edge `uv` -/
  head : A → V

variable {V A : Type}

/-- The edge `e` enters `Z ⊆ V`: its head is in `Z` and its tail is not (arXiv:1907.02673v5,
used from p.6 on). -/
def Digraph.Enters (D : Digraph V A) (e : A) (Z : Finset V) : Prop :=
  D.head e ∈ Z ∧ D.tail e ∉ Z

/-- The edge `e` leaves `Z ⊆ V`: its tail is in `Z` and its head is not. -/
def Digraph.Leaves (D : Digraph V A) (e : A) (Z : Finset V) : Prop :=
  D.tail e ∈ Z ∧ D.head e ∉ Z

instance [DecidableEq V] (D : Digraph V A) (e : A) (Z : Finset V) : Decidable (D.Enters e Z) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableEq V] (D : Digraph V A) (e : A) (Z : Finset V) : Decidable (D.Leaves e Z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `ϱ_x(Z) = Σ[x(e) : e enters Z]`, the in-sum of `x` on `Z` (arXiv:1907.02673v5, p.3, p.6).
It is generic in the value type (`ℝ`, `ℤ`). -/
def Digraph.inSum [Fintype A] [DecidableEq V] {R : Type} [AddCommMonoid R] (D : Digraph V A)
    (x : A → R) (Z : Finset V) : R :=
  ∑ e ∈ univ.filter (fun e => D.Enters e Z), x e

/-- `δ_x(Z) = Σ[x(e) : e leaves Z]`, the out-sum of `x` on `Z`. -/
def Digraph.outSum [Fintype A] [DecidableEq V] {R : Type} [AddCommMonoid R] (D : Digraph V A)
    (x : A → R) (Z : Finset V) : R :=
  ∑ e ∈ univ.filter (fun e => D.Leaves e Z), x e

/-- `m̃(Z) = Σ[m(v) : v ∈ Z]` (arXiv:1907.02673v5, p.5). -/
def demandSum (m : V → ℤ) (Z : Finset V) : ℤ :=
  ∑ v ∈ Z, m v

/-- A modular flow with respect to `m` (an `m`-flow): a finite real vector `x ∈ ℝ^A` with
`ϱ_x(v) − δ_x(v) = m(v)` for every node `v`, where `ϱ_x(v) = Σ[x(uv) : uv ∈ A]` and
`δ_x(v) = Σ[x(vu) : vu ∈ A]` (arXiv:1907.02673v5, p.3 and p.5).

**Formalization Note** `ϱ_x(v)` sums over all edges with head `v` and `δ_x(v)` over all edges
with tail `v`, literally as on p.3, so a loop at `v` appears in both and cancels. -/
def IsModFlow [Fintype A] [DecidableEq V] (D : Digraph V A) (m : V → ℤ) (x : A → ℝ) : Prop :=
  ∀ v : V, (∑ e ∈ univ.filter (fun e => D.head e = v), x e)
    - (∑ e ∈ univ.filter (fun e => D.tail e = v), x e) = (m v : ℝ)

/-- A lower bound `a ∈ ℤ ∪ {−∞}` is at most the real number `r`.

**Formalization Note** `ℤ ∪ {−∞}` is `WithBot ℤ`; the bound `−∞` imposes nothing. No
infinite arithmetic is involved. -/
def LowerLE (a : WithBot ℤ) (r : ℝ) : Prop :=
  ∀ k : ℤ, a = (k : WithBot ℤ) → (k : ℝ) ≤ r

/-- The real number `r` is at most an upper bound `b ∈ ℤ ∪ {+∞}` (`WithTop ℤ`; `+∞` imposes
nothing). -/
def LeUpper (r : ℝ) (b : WithTop ℤ) : Prop :=
  ∀ k : ℤ, b = (k : WithTop ℤ) → r ≤ (k : ℝ)

/-- A lower bound `a ∈ ℤ ∪ {−∞}` is at most an upper bound `b ∈ ℤ ∪ {+∞}`: the comparison
`a ≤ b` in `ℤ ∪ {±∞}`, which holds whenever one of them is infinite. -/
def BoundLE (a : WithBot ℤ) (b : WithTop ℤ) : Prop :=
  ∀ k l : ℤ, a = (k : WithBot ℤ) → b = (l : WithTop ℤ) → k ≤ l

/-- `f ≤ g` for bounding functions `f : A → ℤ ∪ {−∞}`, `g : A → ℤ ∪ {+∞}` (p.5). -/
def BoundsLE (f : A → WithBot ℤ) (g : A → WithTop ℤ) : Prop :=
  ∀ e : A, BoundLE (f e) (g e)

/-- `x` is `(f, g)`-bounded: `f ≤ x ≤ g`, i.e. `x` lies in the box
`T(f, g) = {x : f ≤ x ≤ g}` (arXiv:1907.02673v5, p.5). -/
def IsBounded (f : A → WithBot ℤ) (g : A → WithTop ℤ) (x : A → ℝ) : Prop :=
  ∀ e : A, LowerLE (f e) (x e) ∧ LeUpper (x e) (g e)

/-- `Q = Q(f, g; m)`, the set of `(f, g)`-bounded (feasible) real `m`-flows
(arXiv:1907.02673v5, p.6). -/
def feasFlows [Fintype A] [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ)
    (g : A → WithTop ℤ) (m : V → ℤ) : Set (A → ℝ) :=
  {x | IsModFlow D m x ∧ IsBounded f g x}

/-- `Q⃛ = Q⃛(f, g; m) := Q ∩ ℤ^A`, the set of integral `(f, g)`-bounded `m`-flows
(arXiv:1907.02673v5, p.6, (2.3)).

**Formalization Note** An integral flow is a function `z : A → ℤ`; it belongs to `Q⃛` when its
real image belongs to `Q`. -/
def intFlows [Fintype A] [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ)
    (g : A → WithTop ℤ) (m : V → ℤ) : Set (A → ℤ) :=
  {z | (fun e => (z e : ℝ)) ∈ feasFlows D f g m}

/-- The edge `e` is `(f, g)`-tight: `f(e) = g(e)` (p.5). Both values are then finite. -/
def IsTight (f : A → WithBot ℤ) (g : A → WithTop ℤ) (e : A) : Prop :=
  ∃ k : ℤ, f e = (k : WithBot ℤ) ∧ g e = (k : WithTop ℤ)

/-- "`ϱ_g(Z) − δ_f(Z) < +∞`": every edge entering `Z` has a finite upper bound and every edge
leaving `Z` has a finite lower bound (arXiv:1907.02673v5, pp.10, 11, 13).

**Formalization Note** The sum `ϱ_g(Z) − δ_f(Z)` takes values in `ℤ ∪ {+∞}` and is `< +∞`
exactly when no term is infinite; the finiteness is stated termwise, with no `∞` arithmetic. -/
def FiniteCut [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ)
    (Z : Finset V) : Prop :=
  (∀ e : A, D.Enters e Z → g e ≠ ⊤) ∧ (∀ e : A, D.Leaves e Z → f e ≠ ⊥)

/-- `g + δ·χ_X`: the upper bound `g` changed by the integer `δ` on the edges of `X`
(`g − χ_L` in (4.1) is `shiftOn g L (-1)`; `g⁻ + χ_X` in Lemma 4.1 is `shiftOn g⁻ X 1`).

**Formalization Note** The addition is that of `WithTop ℤ`, so `+∞ + δ = +∞`; every use in
the mission shifts only edges with finite `g`. -/
def shiftOn [DecidableEq A] (g : A → WithTop ℤ) (X : Finset A) (δ : ℤ) : A → WithTop ℤ :=
  fun e => if e ∈ X then g e + (δ : WithTop ℤ) else g e

/-- The box `T(f, g)` is narrow at the edge `e`: `f(e)` and `g(e)` are finite and
`0 ≤ g(e) − f(e) ≤ 1` (arXiv:1907.02673v5, Theorem 2.1, p.6; Theorem 5.3, p.14). -/
def NarrowAt (f : A → WithBot ℤ) (g : A → WithTop ℤ) (e : A) : Prop :=
  ∃ a : ℤ, f e = (a : WithBot ℤ) ∧ (g e = (a : WithTop ℤ) ∨ g e = ((a + 1 : ℤ) : WithTop ℤ))

end FairFlows


