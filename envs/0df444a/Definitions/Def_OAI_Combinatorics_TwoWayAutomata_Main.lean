-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
-- name    : OAI_Combinatorics_TwoWayAutomata_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:51:05.22223+00:00
-- url     : https://prove2.me/theorems/16036bb3-5239-41c8-a2bc-c7c732652673
-- title:
--   Pulling a two-way automaton back along a letter map
-- statement:
--   A two-way nondeterministic automaton (2NFA) $A$ over an alphabet $\Gamma$ with state set $Q$ consists of an initial state $q_0\in Q$, a set $F\subseteq Q$ of accepting states, and, for every state $q$ and tape symbol $x\in\{\triangleright,\triangleleft\}\sqcup\Gamma$ (two endmarkers and the letters), a set $\delta_A(q,x)\subseteq Q\times\{\text{left},\text{stay},\text{right}\}$ of next-state/move pairs.
--
--   **Letter pullback.** Let $f:\Sigma\to\Gamma$ be a map from another alphabet $\Sigma$. The pullback $f^*A$ is the 2NFA over $\Sigma$ with the same state set $Q$, the same initial state $q_0$, the same accepting set $F$, and transitions
--   $$\delta_{f^*A}(q,\triangleright)=\delta_A(q,\triangleright),\qquad \delta_{f^*A}(q,\triangleleft)=\delta_A(q,\triangleleft),\qquad \delta_{f^*A}(q,a)=\delta_A(q,f(a))\quad(a\in\Sigma).$$
--   In words, $f^*A$ reads each letter $a$ as if it were $f(a)$ and treats the endmarkers as $A$ does.
--
--   The pullback has exactly the same states as $A$, and it accepts a word $a_1\cdots a_n$ iff $A$ accepts $f(a_1)\cdots f(a_n)$ (proved separately). It is therefore the tool for moving automata, and with them state-complexity bounds, between alphabets: along a bijection between two encodings of the same alphabet it transports deterministic machines and complements of languages without changing the number of states.
--
--   **Formalization Note** `TwoNFA.pullAlphabet A f : TwoNFA Sigma Q` for `A : TwoNFA Gamma Q` and `f : Sigma → Gamma`; tape symbols are elements of `Fin 2 ⊕ Sigma` and the transition is `A.transition q (Sum.map id f symbol)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Main.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Pull an automaton back along a letter map, preserving its state set. -/
def TwoNFA.pullAlphabet {Sigma Gamma Q : Type*} (A : TwoNFA Gamma Q) (f : Sigma → Gamma) :
    TwoNFA Sigma Q where
  initial := A.initial
  accepting := A.accepting
  transition q symbol := A.transition q (Sum.map id f symbol)

end TwoWayComplementation

end OAI


