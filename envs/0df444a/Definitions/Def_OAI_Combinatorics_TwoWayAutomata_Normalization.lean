-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
-- name    : OAI_Combinatorics_TwoWayAutomata_Normalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:19:54.497974+00:00
-- url     : https://prove2.me/theorems/6333157e-b3e7-4b77-8655-54424bcb41b7
-- title:
--   State renaming and the accepting-sink augmentation of two-way nondeterministic automata
-- statement:
--   Recall the model of the base definitions. A two-way nondeterministic automaton $A$ over an alphabet $\Sigma$ with state set $Q$ (an arbitrary set) consists of an initial state $q_0$, a set $F\subseteq Q$ of accepting states and a transition map $\delta$ that assigns to each state $q$ and tape symbol $s\in\{\triangleright,\triangleleft\}\cup\Sigma$ a set $\delta(q,s)$ of pairs (next state, move), the moves being $-1$ (left), $0$ (stay) and $+1$ (right). An input $w=w_1\cdots w_n$ is written as $\triangleright\,w_1\cdots w_n\,\triangleleft$ on the positions $0,\dots,n+1$. A step leads from a configuration $(q,i)$ to $(r,i+\mu)$ when $(r,\mu)\in\delta(q,s_i)$ for the symbol $s_i$ at position $i$ and $0\le i+\mu\le n+1$, and $A$ accepts $w$ if a configuration with an accepting state is reachable from $(q_0,0)$ in zero or more steps. No endmarker conditions are imposed on $\delta$; the head simply cannot leave the positions $0,\dots,n+1$.
--
--   1. **Renaming states.** For a bijection $\pi:Q\to Q'$, the automaton $A^\pi$ with state set $Q'$ has initial state $\pi(q_0)$, accepting set $\pi(F)$ and transitions
--   $$\delta^\pi(q',s)=\{(\pi(r),\mu):\ (r,\mu)\in\delta(\pi^{-1}(q'),s)\}.$$
--   2. **Augmented configurations.** The augmentation adds a fresh state $\star$ and one extra position $n+2$ to the right of $\triangleleft$. Its configurations are the pairs in $(Q\sqcup\{\star\})\times\{0,\dots,n+2\}$, and an original configuration $(q,i)$, $i\le n+1$, is regarded as the augmented configuration $(q,i)$.
--   3. **Augmented steps.** On the input $w$ there is an augmented step from $c$ to $c'$ exactly in the following cases: $c\to c'$ is a step of $A$ between original configurations; $c=(q,i)$ with $q\in F$ and $c'=(\star,i)$; or $c=(\star,i)$ and $c'=(\star,i+1)$.
--   4. **Local augmented moves.** For a tape symbol $s$ and a move $\mu$, the relation on $Q\sqcup\{\star\}$ given by:
--      - $q\to r$ for $q,r\in Q$ iff $(r,\mu)\in\delta(q,s)$, where moreover $\mu\ne-1$ if $s=\triangleright$ and $\mu\ne+1$ if $s=\triangleleft$;
--      - $q\to\star$ iff $q\in F$ and $\mu=0$;
--      - $\star\to\star$ iff $\mu=+1$;
--      - $\star\to q$ never holds.
--
--   Renaming does not change the accepted language (shown separately), so results proved for automata with an arbitrary finite state set transfer to automata with states $0,\dots,s-1$ and back. The augmentation turns acceptance into reachability of the single configuration $(\star,n+2)$: an accepting state may switch to $\star$, which then sweeps to the extra position. Item 4 describes the augmented moves through the symbol under the head alone, which is the local form needed to represent the automaton by one boundary diagram per tape symbol; the endmarker conditions record locally that the original head never moves left from $\triangleright$ or right from $\triangleleft$, which matters because on the augmented tape a position to the right of $\triangleleft$ exists.
--
--   **Formalization Note** Renaming is `TwoNFA.reindex A e` for `e : Q ≃ Q'`. The augmented state set is `Option Q`, with `none` the fresh state $\star$, and positions are `Fin (w.length + 3)`; `augmentConfig` embeds `Q × Fin n` by `some` and `Fin.castSucc`, and items 3 and 4 are `augmentedStep A w` and `augmentedMove A s move`. Moves are elements `k : Fin 3` with displacement `k - 1`, and the endmarkers are `Sum.inl 0` and `Sum.inl 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace TwoNFA

/-- Rename states along an equivalence, retaining all transitions and moves. -/
def reindex {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') : TwoNFA Sigma Q' where
  initial := e A.initial
  accepting := e.symm ⁻¹' A.accepting
  transition q s := {target | (e.symm target.1, target.2) ∈ A.transition (e.symm q) s}

/-- Embed an original configuration while reserving one state and one exit position. -/
def augmentConfig {Q : Type*} {n : ℕ} (c : Q × Fin n) : Option Q × Fin (n + 1) :=
  (some c.1, c.2.castSucc)

/-- Original moves, an accepting stay into the fresh state, and its rightward sweep. -/
def augmentedStep {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    SetRel (Option Q × Fin (w.length + 3)) (Option Q × Fin (w.length + 3)) :=
  {(c, d) | (∃ x y : Q × Fin (w.length + 2),
      c = augmentConfig x ∧ d = augmentConfig y ∧ (x, y) ∈ A.step w) ∨
    (∃ q : Q, ∃ p : Fin (w.length + 2),
      c = augmentConfig (q, p) ∧ d = (none, p.castSucc) ∧ q ∈ A.accepting) ∨
    (c.1 = none ∧ d.1 = none ∧ d.2.val = c.2.val + 1)}

/-- Augmented moves at one symbol, including the original endmarker restrictions. -/
def augmentedMove {Sigma Q : Type*} (A : TwoNFA Sigma Q) (symbol : Fin 2 ⊕ Sigma)
    (move : Fin 3) : SetRel (Option Q) (Option Q) :=
  {pq | match pq.1, pq.2 with
    | some q, some r => (r, move) ∈ A.transition q symbol ∧
        (symbol = Sum.inl 0 → move ≠ 0) ∧ (symbol = Sum.inl 1 → move ≠ 2)
    | some q, none => q ∈ A.accepting ∧ move = 1
    | none, none => move = 2
    | none, some _ => False}

end TwoNFA

end TwoWayComplementation

end OAI


