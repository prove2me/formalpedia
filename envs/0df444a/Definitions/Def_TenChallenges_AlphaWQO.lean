-- Prove2me | Definitions.Def_TenChallenges_AlphaWQO
-- name    : TenChallenges_AlphaWQO
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:25:13.086617+00:00
-- url     : https://prove2.me/theorems/993ca6f4-11db-4447-af6e-83e07931100a
-- title:
--   Well-quasi-orders, the cumulative hierarchy $V^*_\alpha(Q)$, $\alpha$-well-quasi-ordering, finite and planar graphs under minors
-- statement:
--   The definitions behind Challenge 6 of the Ten Challenges benchmark.
--
--   1. **Well-quasi-ordering.** A relation $\le$ on a type $Q$ is a *WQO* if for every sequence $q_0,q_1,\dots$ in $Q$ there are indices $i<j$ with $q_i\le q_j$.
--   2. **The cumulative hierarchy.** For an ordinal $o$, the type $V^*_o(Q)$ is defined by transfinite recursion: $V^*_0(Q)=Q$; $V^*_{o+1}(Q)$ is the type of nonempty subsets of $V^*_o(Q)$; for a limit ordinal $o$, $V^*_o(Q)$ is the disjoint union of the $V^*_{\beta}(Q)$ over $\beta<o$. Three lemmas record these equations.
--   3. **The game relation $\le^*$.** For $X\in V^*_a(Q)$ and $Y\in V^*_b(Q)$, $X\le^* Y$ is defined by recursion on the ordinals $a$ and $b$: if $a=b=0$ it is $X\le Y$ in $Q$; if $a=0$ and $b$ is a successor, it holds when some element $y$ of the set $Y$ satisfies $X\le^* y$; if $a$ is a successor and $b=0$, when every element $x$ of the set $X$ satisfies $x\le^* Y$; if both are successors, when for every $x\in X$ there is $y\in Y$ with $x\le^* y$; and an element of a limit level is replaced by its underlying element of the lower level. This is the relation under which Player II has a winning strategy in Nash-Williams's game.
--   4. **$\alpha$-well-quasi-ordering.** $(Q,\le)$ is *$\alpha$-WQO* if $\le^*$ restricted to $V^*_\alpha(Q)$ is a WQO. Level $0$ is ordinary WQO.
--   5. **Graphs.** A *finite graph* is a pair $(n,G)$ with $G$ a simple graph on $\{0,\dots,n-1\}$; $G\preceq H$ if $G$ is a minor of $H$. A *planar graph* is a finite graph that is Wagner-planar (no $K_5$ or $K_{3,3}$ minor), with the same relation.
--
--   **Formalization Note.** The recursion uses Mathlib's `Ordinal.limitRecOn`, and the equations for the three kinds of levels are transported with `cast`. Ordinals and $Q$ live in a common universe `u`; for graphs this is universe $0$.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/AlphaWQO.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/AlphaWQO.lean; the hierarchy and game relation follow C. St. J. A. Nash-Williams, On well-quasi-ordering infinite trees, Proc. Cambridge Philos. Soc. 61 (1965), in the formulation of the Ten Challenges website (challenge 6).

import Mathlib.SetTheory.Ordinal.Arithmetic
import Definitions.Def_TenChallenges_Minor

open SimpleGraph Ordinal

universe u

/-- A quasi-order is well-quasi-ordered when every infinite sequence
contains an increasing pair. -/
def IsWQO {Q : Type u} (le : Q → Q → Prop) : Prop :=
  ∀ f : ℕ → Q, ∃ i j : ℕ, i < j ∧ le (f i) (f j)

/-- Level `o` of the cumulative hierarchy over `Q`: `VStar Q 0 = Q`,
`VStar Q (succ o)` is the nonempty subsets of `VStar Q o`, and at a limit
`o` it is the disjoint union of all lower levels. -/
noncomputable def VStar (Q : Type u) (o : Ordinal.{u}) : Type u :=
  Ordinal.limitRecOn o
    Q
    (fun _ ih => {S : Set ih // S.Nonempty})
    (fun o _ ih => Σ i : o.ToType, ih (Ordinal.typein (α := o.ToType) (· < ·) i)
      (Ordinal.typein_lt_self i))

/-- Level zero is the base quasi-order. -/
theorem VStar_zero (Q : Type u) : VStar Q 0 = Q :=
  Ordinal.limitRecOn_zero ..

/-- Successor levels consist of nonempty subsets of the preceding level. -/
theorem VStar_succ (Q : Type u) (o : Ordinal.{u}) :
    VStar Q (Order.succ o) = {S : Set (VStar Q o) // S.Nonempty} :=
  Ordinal.limitRecOn_add_one ..

/-- Limit levels are disjoint unions of the preceding levels. -/
theorem VStar_limit (Q : Type u) {o : Ordinal.{u}} (h : Order.IsSuccLimit o) :
    VStar Q o = Σ i : o.ToType, VStar Q (Ordinal.typein (α := o.ToType) (· < ·) i) :=
  Ordinal.limitRecOn_limit _ _ _ _ h

/-- The Nash–Williams game relation `≤*`, as a *heterogeneous* relation
comparing an element of level `a` with an element of level `b`.

A limit-level element is identified with its underlying lower-level element
(the disjoint union is transparent), so `≤*` unwraps limit tags for free; at
successor levels it is the `∀`-Player-I / `∃`-Player-II lift, and at level
`0` it bottoms out in `le`. Well-founded because every unwrap/descent
strictly decreases the ordinal level on the side it acts on. -/
noncomputable def leStar {Q : Type u} (le : Q → Q → Prop) (a : Ordinal.{u}) :
    VStar Q a → ∀ b : Ordinal.{u}, VStar Q b → Prop :=
  Ordinal.limitRecOn (motive := fun a => VStar Q a → ∀ b : Ordinal.{u}, VStar Q b → Prop) a
    -- a = 0 : X is in Q, Player I cannot move; recurse on b (Player II descends).
    (fun X b => Ordinal.limitRecOn (motive := fun b => VStar Q b → Prop) b
      (fun Y => le (cast (VStar_zero Q) X) (cast (VStar_zero Q) Y))
      (fun β ibh Y => ∃ y ∈ (cast (VStar_succ Q β) Y).val, ibh y)
      (fun β hb ibh Y =>
        let Y' := cast (VStar_limit Q hb) Y
        ibh (Ordinal.typein (α := β.ToType) (· < ·) Y'.1) (Ordinal.typein_lt_self _) Y'.2))
    -- a = succ α : Player I picks x ∈ X, then Player II answers from b.
    (fun α ih X b => Ordinal.limitRecOn (motive := fun b => VStar Q b → Prop) b
      (fun Y => ∀ x ∈ (cast (VStar_succ Q α) X).val, ih x 0 Y)
      (fun β _ Y => ∀ x ∈ (cast (VStar_succ Q α) X).val,
        ∃ y ∈ (cast (VStar_succ Q β) Y).val, ih x β y)
      (fun β hb ibh Y =>
        let Y' := cast (VStar_limit Q hb) Y
        ibh (Ordinal.typein (α := β.ToType) (· < ·) Y'.1) (Ordinal.typein_lt_self _) Y'.2))
    -- a limit : X is a disjoint-union
    (fun a ha iha X =>
      let X' := cast (VStar_limit Q ha) X
      iha (Ordinal.typein (α := a.ToType) (· < ·) X'.1) (Ordinal.typein_lt_self _) X'.2)

/-- `(Q, le)` is `α`-well-quasi-ordered when level `α` of
 the cumulative hierarchy over `Q` is well-quasi-ordered under `≤*`. -/
def IsAlphaWQO {Q : Type u} (le : Q → Q → Prop) (a : Ordinal.{u}) : Prop :=
  IsWQO (fun X Y : VStar Q a => leStar le a X a Y)

/-- A finite simple graph, given as a graph on `Fin n` for some `n`. -/
def FiniteGraph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The minor order on finite graphs. -/
def FiniteGraph.MinorLE (G H : FiniteGraph) : Prop :=
  Nonempty (Minor G.2 H.2)

/-- A finite planar simple graph. -/
def PlanarGraph : Type :=
  {G : FiniteGraph // G.2.IsWagnerPlanar}

/-- The minor order on finite planar graphs. -/
def PlanarGraph.MinorLE (G H : PlanarGraph) : Prop :=
  FiniteGraph.MinorLE G.val H.val


