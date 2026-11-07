-- Prove2me | Definitions.Def_ImplicitParityWL_PebbleGame
-- name    : ImplicitParityWL_PebbleGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:37.432272+00:00
-- url     : https://prove2.me/theorems/50bedd7b-3c3f-49dd-9d8c-4cd095cb56f9
-- title:
--   The bijective pebble game, its color-first variant, and forcing
-- statement:
--   In the **bijective $m$-pebble game** $\mathrm{BP}_m(G,H)$ a game state is a partial map from the pebble indices to $V(G)\times V(H)$, and the game starts in the empty state. If $|V(G)|\ne|V(H)|$, Spoiler wins immediately. Otherwise each round has three steps:
--
--   1. Spoiler chooses $i$ and lifts the $i$-th pebble pair;
--   2. Duplicator chooses a bijection $f:V(G)\to V(H)$;
--   3. Spoiler chooses $p$ and places the $i$-th pair on $p$ and $f(p)$.
--
--   Spoiler wins after a round if the placed pairs do not form a partial isomorphism (equalities, adjacencies and colors must agree). Duplicator **survives** $r$ rounds if Spoiler has no strategy that wins within the first $r$ rounds.
--
--   In the **color-first variant**, Spoiler lifts a pair and announces a color $A$, Duplicator answers with a bijection $f_A$ between the two color classes of $A$, and Spoiler chooses $p$ and sets $S(i)=(p,f_A(p))$, or chooses $q$ and sets $S(i)=(f_A^{-1}(q),q)$.
--
--   The module also defines the phrase of Lemmas 5.5 and 5.6: from a state $S$, Spoiler can **either win or reach a state satisfying $Q$ within $t$ moves**.
--
--   All round bounds of the paper are proved in this game and transferred to $k$-WL by Theorem 3.1.
--
--   **Formalization Note** "Duplicator survives" is defined by recursion on $r$, as the negation of Spoiler's winning strategy in a finite game of perfect information; `Survives 0` holds exactly when the vertex counts agree.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §3, p.15; Lemmas 5.5–5.6, pp.27–28

import Mathlib
import Definitions.Def_ImplicitParityWL_ColoredGraph

namespace ImplicitParityWL

variable {K V W : Type*}

/-- A game state of the bijective `m`-pebble game (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds
for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, §3,
p.15): a partial map from the pebble indices to `V(G) × V(H)`. -/
abbrev GameState (V W : Type*) (m : ℕ) := Fin m → Option (V × W)

/-- The empty game state, in which the game starts. -/
def GameState.empty {m : ℕ} : GameState V W m := fun _ => none

/-- The state after the `i`-th pebble pair is lifted and placed on `x`. -/
def GameState.place {m : ℕ} (S : GameState V W m) (i : Fin m) (x : V × W) : GameState V W m :=
  Function.update S i (some x)

/-- The placed pairs of `S` form a **partial isomorphism** (§3, p.14): equality, adjacency and
colors of the placed vertices agree on both sides. -/
def PartialIso {m : ℕ} (G : ColoredGraph K V) (H : ColoredGraph K W) (S : GameState V W m) : Prop :=
  ∀ (i j : Fin m) (p p' : V) (q q' : W), S i = some (p, q) → S j = some (p', q') →
    (p = p' ↔ q = q') ∧ (G.graph.Adj p p' ↔ H.graph.Adj q q') ∧ G.χ p = H.χ q

/-- **Duplicator survives `r` rounds** of the bijective `m`-pebble game `BP_m(G, H)` from the state
`S` (§3, p.15). If `|V(G)| ≠ |V(H)|` Spoiler wins immediately. Otherwise, for every pebble index
Spoiler lifts, Duplicator has a bijection `f` such that for every vertex `p` Spoiler chooses, the
placement `(p, f p)` leaves a partial isomorphism and Duplicator survives `r - 1` further rounds.

**Formalization Note** The game is finite with perfect information, so "Duplicator survives" is the
negation of "Spoiler has a strategy that wins within `r` rounds" (`SpoilerWinsWithin`), as on the
page. The winning condition is checked after each round only, so a state `S` that is not a partial
isomorphism loses only at the next placement. -/
def Survives [Fintype V] [Fintype W] {m : ℕ} (G : ColoredGraph K V) (H : ColoredGraph K W) :
    ℕ → GameState V W m → Prop
  | 0, _ => Fintype.card V = Fintype.card W
  | r + 1, S => Fintype.card V = Fintype.card W ∧ ∀ i : Fin m, ∃ f : V ≃ W, ∀ p : V,
      PartialIso G H (S.place i (p, f p)) ∧ Survives G H r (S.place i (p, f p))

/-- **Spoiler wins `BP_m(G, H)` within `r` rounds** (§3, p.15). -/
def SpoilerWinsWithin [Fintype V] [Fintype W] (m : ℕ) (G : ColoredGraph K V)
    (H : ColoredGraph K W) (r : ℕ) : Prop :=
  ¬ Survives G H r (GameState.empty : GameState V W m)

/-- **Duplicator survives `r` rounds of the color-first variant** of `BP_m(G, H)` from the state `S`
(§3, p.15): Spoiler lifts the `i`-th pair and announces a color `A`; Duplicator answers with a
bijection `f_A` of the two color classes of `A`; Spoiler either chooses `p` in the class of `G` and
sets `S(i) := (p, f_A p)`, or chooses `q` in the class of `H` and sets `S(i) := (f_A⁻¹ q, q)`.

**Formalization Note** The page defines the variant for graphs whose corresponding color classes
have equal sizes, so round `0` has no cardinality clause. A color with empty classes gives Spoiler no
placement, and that branch is won by Duplicator: Spoiler has no reason to announce it. -/
def SurvivesCF {m : ℕ} (G : ColoredGraph K V) (H : ColoredGraph K W) :
    ℕ → GameState V W m → Prop
  | 0, _ => True
  | r + 1, S => ∀ (i : Fin m) (A : K), ∃ f : {p : V // G.χ p = A} ≃ {q : W // H.χ q = A},
      (∀ p, PartialIso G H (S.place i (p.1, (f p).1)) ∧ SurvivesCF G H r (S.place i (p.1, (f p).1))) ∧
      (∀ q, PartialIso G H (S.place i ((f.symm q).1, q.1)) ∧
        SurvivesCF G H r (S.place i ((f.symm q).1, q.1)))

/-- **Spoiler can either win or reach a state satisfying `Q` within `t` moves**, from the state `S`.
This is the phrase "Spoiler can either win or reach a game state …" of Lemmas 5.5 and 5.6 (§5.2,
pp.27–28): the state already satisfies `Q`, or Spoiler has a pebble index such that for every
bijection of Duplicator there is a vertex whose placement breaks the partial isomorphism or leaves a
state from which he can do it in `t - 1` moves. -/
def Forces {m : ℕ} (G : ColoredGraph K V) (H : ColoredGraph K W) :
    ℕ → GameState V W m → (GameState V W m → Prop) → Prop
  | 0, S, Q => Q S
  | t + 1, S, Q => Q S ∨ ∃ i : Fin m, ∀ f : V ≃ W, ∃ p : V,
      ¬ PartialIso G H (S.place i (p, f p)) ∨ Forces G H t (S.place i (p, f p)) Q

end ImplicitParityWL


