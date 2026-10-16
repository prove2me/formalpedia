-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:43:10.905693+00:00
-- url     : https://prove2.me/theorems/957eac67-ac9b-4d60-baf0-56ba36731115
-- title:
--   State renaming and the accepting-sink augmentation of two-way nondeterministic automata
-- statement:
--   A two-way nondeterministic automaton (2NFA) over an alphabet $\Sigma$ with state set $Q$ consists of an initial state $q_0\in Q$, a set $F\subseteq Q$ of accepting states, and, for every state $q$ and tape symbol $x\in\{\triangleright,\triangleleft\}\sqcup\Sigma$, a set $\delta(q,x)\subseteq Q\times\{0,1,2\}$ of next-state/move pairs, where the move codes $0,1,2$ mean left, stay and right. On an input $w=a_1\cdots a_n$ the tape reads $\triangleright a_1\cdots a_n\triangleleft$ at positions $0,\dots,n+1$, and $x_i$ denotes the symbol at position $i$. A step $(q,i)\to(r,j)$ between configurations in $Q\times\{0,\dots,n+1\}$ means that $(r,\mu)\in\delta(q,x_i)$ for some $\mu$ with $j=i+\mu-1$; the head can never leave the marked tape. $A$ accepts $w$ if a finite, possibly empty, sequence of steps leads from $(q_0,0)$ to a configuration whose state lies in $F$.
--
--   1. **Reindexing.** For a bijection $e:Q\to Q'$, the automaton $A^e$ has state set $Q'$, initial state $e(q_0)$, accepting set $e(F)$, and $(r',\mu)\in\delta^e(q',x)$ iff $(e^{-1}(r'),\mu)\in\delta(e^{-1}(q'),x)$. It is the same machine with renamed states, and it keeps all transitions and moves.
--   2. **Augmented configurations.** Configurations are embedded into $(Q\sqcup\{\bot\})\times\{0,\dots,n+2\}$ by $\iota(q,i)=(q,i)$; this reserves one fresh state $\bot$ and one fresh exit position $n+2$ to the right of the right endmarker.
--   3. **Augmented step relation.** On an input $w$ of length $n$, the augmented step relation on $(Q\sqcup\{\bot\})\times\{0,\dots,n+2\}$ consists exactly of the pairs
--   $$\iota(c)\to\iota(c')\ \ (c\to c'\text{ a step of }A),\qquad (q,i)\to(\bot,i)\ \ (q\in F,\ 0\le i\le n+1),\qquad (\bot,i)\to(\bot,i+1)\ \ (0\le i\le n+1):$$
--   the original steps, a stay into the fresh state from any accepting configuration, and a rightward sweep of the fresh state.
--   4. **Augmented local moves.** For a tape symbol $x$ and a move code $\mu$, the relation $M(x,\mu)$ on $Q\sqcup\{\bot\}$ contains $(q,r)$ for $q,r\in Q$ iff $(r,\mu)\in\delta(q,x)$, $\mu$ is not the left move when $x=\triangleright$, and $\mu$ is not the right move when $x=\triangleleft$; it contains $(q,\bot)$ iff $q\in F$ and $\mu$ is the stay move; it contains $(\bot,\bot)$ iff $\mu$ is the right move; and it never contains $(\bot,q)$ with $q\in Q$.
--
--   Renaming states does not change the accepted language (proved separately), so statements about machines with an arbitrary finite state set reduce to the state sets $\{0,\dots,s-1\}$ and back; for instance, a machine with $|H|+2$ states becomes one with state set $\{0,\dots,n-1\}$. The augmentation replaces existential acceptance ("some accepting state occurs") by reachability of a single configuration: $A$ accepts $w$ iff the augmented steps lead from $\iota(q_0,0)$ to $(\bot,n+2)$. The local moves $M(x,\mu)$ describe the augmented machine cell by cell and feed the representation of an $s$-state automaton by boundary diagrams on $s+1$ labels.
--
--   **Formalization Note** The base type `TwoNFA Sigma Q` has fields `initial`, `accepting`, `transition`; the endmarkers are `Sum.inl 0` (left) and `Sum.inl 1` (right) and moves are `0, 1, 2 : Fin 3`. In `reindex A e` (for `e : Q ≃ Q'`) the accepting set is the preimage under `e.symm`. The fresh state is `none : Option Q`, original states are `some q`, positions are `Fin (w.length + 3)`, and `augmentConfig` uses `Fin.castSucc`; the definitions are `TwoNFA.reindex`, `TwoNFA.augmentConfig`, `TwoNFA.augmentedStep` and `TwoNFA.augmentedMove`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization

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


