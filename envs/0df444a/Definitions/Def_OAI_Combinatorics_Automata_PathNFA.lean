-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_PathNFA
-- name    : OAI_Combinatorics_Automata_PathNFA
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:10:08.81467+00:00
-- url     : https://prove2.me/theorems/63dfa1b7-5701-4489-b32f-7a2ad69ecf0b
-- title:
--   Nondeterministic two-way automata on arbitrary state sets and the path automaton for liveness
-- statement:
--   Words are read between a left endmarker $\triangleright$ and a right endmarker $\triangleleft$. A word $w=w_1\cdots w_n$ occupies positions $0,\dots,n+1$, with $\triangleright$ at $0$ and $\triangleleft$ at $n+1$. The possible moves are left, stay and right.
--
--   1. **Nondeterministic machines.** A nondeterministic two-way automaton over an alphabet $\Sigma$ with state set $Q$ has an initial state $q_0$, a set of accepting states, and a transition relation. The relation assigns to each state and tape symbol a set of pairs (next state, move), subject to two boundary rules: no transition on $\triangleright$ moves left, and no transition on $\triangleleft$ moves right. A configuration on $w$ is a pair $(i,p)$ of a position and a state. There is a step $(i,p)\vdash(i',p')$ if some transition $(p',d)$ is available from $p$ on the symbol at position $i$, and $i'=i-1$, $i$ or $i+1$ according as $d$ is left, stay or right. The automaton accepts $w$ under the positive convention if there is a run of at least one step from $(0,q_0)$ to a configuration with an accepting state. Under the reflexive convention, runs of length zero are also allowed. A bijection $Q\cong\{0,\dots,m-1\}$ relabels such a machine into one with numbered states.
--   2. **The path automaton.** Let $H$ be a set, and take as alphabet the set $\mathcal B(H)$ of binary relations on $H$. The path automaton has states $\mathrm{init}$, $\mathrm{acc}$, $\mathrm{rej}$ and one path state $p$ for every $p\in H$. Its initial state is $\mathrm{init}$ and its accepting set is $\{\mathrm{acc}\}$. Its only transitions are
--   $$
--   \mathrm{init}\xrightarrow{\ \triangleright\ }(p,\mathrm{right})\ \ (p\in H),\qquad p\xrightarrow{\ \Gamma\ }(p',\mathrm{right})\ \ \text{whenever }\Gamma(p,p'),\qquad p\xrightarrow{\ \triangleleft\ }(\mathrm{acc},\mathrm{stay}),
--   $$
--   where $\Gamma\in\mathcal B(H)$ is a letter. The automaton never moves left.
--   3. **Invariant.** For a word $w$ over $\mathcal B(H)$, the predicate $\mathrm{Good}$ on configurations is defined as follows.
--      - $(i,\mathrm{init})$ is good iff $i=0$.
--      - $(i,p)$ with $p$ a path state is good iff $i\ge1$ and $(w_1\cdots w_{i-1})(a,p)$ holds for some $a\in H$, so that $p$ is the endpoint of a path through the first $i-1$ letters.
--      - $(i,\mathrm{acc})$ is good iff $w$ is live, that is, $(w_1\cdots w_n)(x,y)$ holds for some $x,y\in H$.
--      - $(i,\mathrm{rej})$ is never good.
--
--   The path automaton reads the word once from left to right. It guesses a starting point and then follows a path through the relations, letter by letter. Later results show that it accepts exactly the live words under both acceptance conventions, and the invariant $\mathrm{Good}$ is what their proof tracks. For $H=\{0,\dots,h-1\}$ the path automaton is a nondeterministic automaton with $h+3$ states that never moves left and recognizes one-way liveness. This gives the upper-bound half of the main theorem.
--
--   **Formalization Note** The general machine is `NMachineOn Alpha Q`, with `Step`, `Accepts` (where `positive = true` uses the transitive closure of `Step` and `positive = false` the reflexive–transitive closure) and `relabel`, which produces an `NMachine Alpha n`. The path automaton is `PathNFA.machine`, with transition rules `PathNFA.rules` and invariant `PathNFA.Good`. Its state type is `PathNFA.State H = Option (H ⊕ Bool)`: `none` is init, `some (inl p)` is a path state, `some (inr false)` is acc and `some (inr true)` is the unused rejecting state. The lemma `rules_noLeft` records that no rule moves left.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/PathNFA.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/PathNFA.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition

namespace OAI

namespace OneWayLiveness

/-- A nondeterministic automaton on an arbitrary state type. -/
structure NMachineOn (Alpha Q : Type) where
  initial : Q
  accepting : Set Q
  transition : Q → Symbol Alpha → Set (Q × Move)
  left_boundary : ∀ q q', (q', .left) ∉ transition q .left
  right_boundary : ∀ q q', (q', .right) ∉ transition q .right

namespace NMachineOn
variable {Alpha Q : Type} (M : NMachineOn Alpha Q)
abbrev Config (w : List Alpha) := Fin (w.length+2) × Q

def Step (w : List Alpha) (c c' : Config (Q := Q) w) : Prop :=
  ∃ d, (c'.2,d) ∈ M.transition c.2 (scanned w c.1) ∧ d.Rel c.1.val c'.1.val

def Accepts (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0,by omega⟩,M.initial) c ∧ c.2 ∈ M.accepting

def relabel {n : ℕ} (e : Q ≃ Fin n) : NMachine Alpha n where
  initial := e M.initial
  accepting := {q | e.symm q ∈ M.accepting}
  transition q b := {p | (e.symm p.1,p.2) ∈ M.transition (e.symm q) b}
  left_boundary q q' := M.left_boundary (e.symm q) (e.symm q')
  right_boundary q q' := M.right_boundary (e.symm q) (e.symm q')

end NMachineOn

namespace PathNFA
variable {H : Type}
/-- `none` is the initial state. Boolean states are accept and reject. -/
abbrev State (H : Type) := Option (H ⊕ Bool)
abbrev path (p : H) : State H := some (.inl p)
abbrev accept : State H := some (.inr false)

def rules : State H → Symbol (BRel H) → Set (State H × Move)
  | none, .left => {c | ∃ p, c = (path p,.right)}
  | some (.inl p), .letter R => {c | ∃ q, c = (path q,.right) ∧ R.holds p q}
  | some (.inl _), .right => {(accept,.stay)}
  | _, _ => ∅

lemma rules_noLeft (q : State H) (b : Symbol (BRel H)) (q' : State H) :
    (q',.left) ∉ rules q b := by
  cases q with
  | none => cases b <;> simp [rules]
  | some q => cases q with
    | inl p => cases b <;> simp [rules]
    | inr b' => cases b <;> simp [rules]

def machine : NMachineOn (BRel H) (State H) where
  initial := none
  accepting := {accept}
  transition := rules
  left_boundary q q' := rules_noLeft q .left q'
  right_boundary q q' := by
    cases q with
    | none => simp [rules]
    | some q => cases q <;> simp [rules]

/-- The accumulated product on every prefix reached by a path state. -/
def Good (w : List (BRel H)) (c : NMachineOn.Config (Q := State H) w) : Prop :=
  match c.2 with
  | none => c.1.val = 0
  | some (.inl p) => 1 ≤ c.1.val ∧ ∃ a, (w.take (c.1.val-1)).prod.holds a p
  | some (.inr false) => BRel.live w
  | some (.inr true) => False

end PathNFA

end OneWayLiveness

end OAI


