-- Prove2me | Definitions.Def_LocalBreadth_Supplement_StoppingGame
-- name    : LocalBreadth_Supplement_StoppingGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:20:52.435176+00:00
-- url     : https://prove2.me/theorems/07dff331-04cb-4407-ba39-b493a49731c9
-- title:
--   The finite stopping game and feasible rectangle packets
-- statement:
--   Fix a chain $L_0\supseteq L_1\supseteq\dots\supseteq L_r$ and quotas $q_0,\dots,q_r$. A **finite rectangle packet** is a tuple $(\mathcal R_0,\dots,\mathcal R_r)$ of finite families of rectangles, $\mathcal R_i$ assigned to $L_i$, with support $U=\bigcup_i\bigcup_{R\in\mathcal R_i}(L_i\cap R)$.
--
--   The game starts at level $r$ with visible set $U\cap L_r$. At level $i$ Black may either
--   1. claim an unused visible point, after which White may claim at most one unused visible point; or
--   2. if $i>0$, move to level $i-1$, enlarging the visible set to $U\cap L_{i-1}$, with no White response.
--
--   Black may stop at level $i$ only when every visible point has been claimed; at level $0$ the game ends when the visible set is exhausted. At a stop at level $i$ White wins if every $R\in\mathcal R_i$ satisfies
--   $$|W\cap L_i\cap R|\ge q_i\,|L_i\cap R|,$$
--   $W$ being White's points. The packet is **feasible** if White has a single strategy that wins at every legal stop, whatever Black does.
--
--   This finite game replaces the one-dimensional pairing score as the local certificate in higher dimensions.
--
--   **Formalization Note** The per-level quota $q_i$ is $q(L_i)$ for Definition 7.4 and the copy quota for Definition 7.14, where the chain may repeat a language and a level move between equal languages reveals nothing. White's strategy is a function of Black's moves so far; a reply that names no unused visible point counts as a pass.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §7.2, p.53

import Mathlib

namespace LocalBreadth.Supplement

/-- A move of Black in the finite stopping game (§7.2, p.53): claim a point, or move one level up the
chain (to the next larger language). -/
inductive BlackMove (P : Type) where
  | claim (p : P)
  | descend

/-- A position of the finite stopping game: the current level `i` (the visible language is `L i`) and
the points claimed so far by Black and by White. -/
structure GameState (P : Type) where
  level : ℕ
  black : Set P
  white : Set P

/-- A causal White strategy: after each Black claim, White's reply (`none` = no claim), as a function of
Black's moves so far (White's own earlier moves are determined by them). -/
abbrev WhiteStrategy (P : Type) := List (BlackMove P) → Option P

variable {P : Type}

open Classical in
/-- White's reply is carried out when it names an unused visible point; any other reply is a pass
("White may claim at most one unused visible point"). -/
noncomputable def applyWhite (L : ℕ → Set P) (U : Set P) (o : Option P) (s : GameState P) :
    GameState P :=
  match o with
  | none => s
  | some w =>
      if w ∈ U ∩ L s.level ∧ w ∉ s.black ∪ s.white then { s with white := insert w s.white } else s

/-- The positions reachable in the game on the chain `L 0, …, L r` with support `U`, when White
follows `σ`. Initially the level is `r` and nothing is claimed. At level `i` Black may claim an unused
visible point of `U ∩ L i`, after which White replies by `σ`; or, if `i > 0`, move to level `i - 1`, with
no White reply. -/
inductive GameReach (L : ℕ → Set P) (U : Set P) (r : ℕ) (σ : WhiteStrategy P) :
    List (BlackMove P) → GameState P → Prop
  | init : GameReach L U r σ [] ⟨r, ∅, ∅⟩
  | claim {ms : List (BlackMove P)} {s : GameState P} (hs : GameReach L U r σ ms s) (p : P)
      (hvis : p ∈ U ∩ L s.level) (hfree : p ∉ s.black ∪ s.white) :
      GameReach L U r σ (ms ++ [BlackMove.claim p])
        (applyWhite L U (σ (ms ++ [BlackMove.claim p])) { s with black := insert p s.black })
  | descend {ms : List (BlackMove P)} {s : GameState P} (hs : GameReach L U r σ ms s)
      (hpos : 0 < s.level) :
      GameReach L U r σ (ms ++ [BlackMove.descend]) { s with level := s.level - 1 }

/-- The finite support `U = ⋃_{i ≤ r} ⋃_{R ∈ R_i} (L_i ∩ R)` of a rectangle packet `(R_0, …, R_r)`;
rectangles are pairs `(a, b)` standing for `Set.Icc a b`. -/
def packetSupport [Preorder P] (L : ℕ → Set P) (r : ℕ) (Rs : ℕ → Finset (P × P)) : Set P :=
  ⋃ i ∈ Finset.range (r + 1), ⋃ R ∈ Rs i, L i ∩ Set.Icc R.1 R.2

/-- **Feasibility of a finite rectangle packet** in the finite stopping game. Kleinberg, Wei, STOC 2027
submission (manuscript sha256 f924cbfc…), §7.2, p.53: White has a single strategy such that, however
Black plays, whenever Black stops at a level `i` after every point currently visible at that level has
been claimed, every `R ∈ R_i` satisfies `|W ∩ L_i ∩ R| ≥ q_i |L_i ∩ R|`.

**Formalization Note.** The chain is `L 0, …, L r` (`L 0` the starting, largest language) with a
per-level quota `qt i`; Definition 7.4 uses `qt i = q(L_i)` on a strict chain, and Definition 7.14
uses the copy quota on a non-strict chain, where a level move between equal languages makes nothing
new visible. One strategy is fixed before Black's play (`∃ σ, ∀` plays); a legal stop is any reachable
position whose visible set `U ∩ L i` is entirely claimed, the end of the game at level `0` included. -/
def IsFeasiblePacket [Preorder P] (L : ℕ → Set P) (qt : ℕ → ℝ) (r : ℕ)
    (Rs : ℕ → Finset (P × P)) : Prop :=
  ∃ σ : WhiteStrategy P, ∀ ms s, GameReach L (packetSupport L r Rs) r σ ms s →
    packetSupport L r Rs ∩ L s.level ⊆ s.black ∪ s.white →
    ∀ R ∈ Rs s.level,
      qt s.level * ((L s.level ∩ Set.Icc R.1 R.2).ncard : ℝ) ≤
        ((s.white ∩ L s.level ∩ Set.Icc R.1 R.2).ncard : ℝ)

end LocalBreadth.Supplement


