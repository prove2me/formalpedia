-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge
-- name    : OAI_Combinatorics_TwoWayAutomata_TransitionBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:55:43.441981+00:00
-- url     : https://prove2.me/theorems/40a3bfe4-24b7-4603-a2e5-88ee8bd14835
-- title:
--   Converting a deterministic two-way automaton into the companion deterministic machine model
-- statement:
--   Let $\Sigma$ be an alphabet and $s\in\mathbb N$, and write $[s]=\{0,\dots,s-1\}$. Two machine models are compared.
--
--   *Two-way automata (2NFA).* $A$ has an initial state $q_0\in[s]$, an accepting set $F\subseteq[s]$, and for every state $q$ and tape symbol $x$ (the left endmarker $\triangleright$, encoded as marker $0$; a letter of $\Sigma$; or the right endmarker $\triangleleft$, encoded as marker $1$) a set $\delta(q,x)\subseteq[s]\times\{0,1,2\}$ of next-state/move pairs, the codes $0,1,2$ meaning left, stay and right. $A$ is deterministic if every set $\delta(q,x)$ has at most one element.
--
--   *Companion deterministic machines.* A machine $D$ with $s$ states has an initial state, an accepting set, and a partial transition function assigning to each state $q$ and tape symbol $x\in\{\triangleright,\triangleleft\}\sqcup\Sigma$ either nothing or a single pair $(r,M)$ with $M\in\{\mathrm L,\mathrm S,\mathrm R\}$ (left, stay, right), subject to the boundary conditions that it never prescribes $\mathrm L$ on $\triangleright$ and never prescribes $\mathrm R$ on $\triangleleft$.
--
--   1. **Encodings.** $\mathrm{enc}(\triangleright)=$ marker $0$, $\mathrm{enc}(a)=a$ for letters, $\mathrm{enc}(\triangleleft)=$ marker $1$; moves are coded by $\mathrm L\mapsto0$, $\mathrm S\mapsto1$, $\mathrm R\mapsto2$, and decoded by $0\mapsto\mathrm L$, $1\mapsto\mathrm S$, $2\mapsto\mathrm R$. Decoding followed by coding is the identity on $\{0,1,2\}$, and the move code is injective.
--   2. **Guard.** $\mathrm{Guard}(x,M)$ holds iff ($x=\triangleright$ implies $M\neq\mathrm L$) and ($x=\triangleleft$ implies $M\neq\mathrm R$): $M$ is not an outward move at an endmarker.
--   3. **Selection.** For a set $S$, $\mathrm{select}(S)$ is a chosen element of $S$ if $S\neq\emptyset$ and undefined otherwise. If $S$ has at most one element, then $\mathrm{select}(S)=y$ iff $y\in S$.
--   4. **Converted transitions.** For a 2NFA $A$ with state set $[s]$,
--   $$T_A(q,x)=\{(r,M):\ (r,\mathrm{code}(M))\in\delta(q,\mathrm{enc}(x))\ \text{and}\ \mathrm{Guard}(x,M)\}.$$
--   If $A$ is deterministic, every $T_A(q,x)$ has at most one element.
--   5. **Converted machine.** For a deterministic $A$, the companion machine $D_A$ has the same states, initial state and accepting set as $A$, and transition $\delta_{D_A}(q,x)=\mathrm{select}(T_A(q,x))$; the guard guarantees the boundary conditions. No halting or totality condition is introduced.
--
--   The guard removes only transitions that point outward at an endmarker, and such transitions can never be executed on the bounded tape. Hence $D_A$ has the same finite runs as $A$ and accepts the same words under the convention that allows runs of length zero (proved separately), so lower bounds known for the companion deterministic model apply to deterministic 2NFAs.
--
--   **Formalization Note** `Symbol Alpha` (constructors `left`, `letter`, `right`), `Move` (`left`, `stay`, `right`) and `DMachine Alpha s` come from the companion one-way liveness development; a `DMachine` transition is `Option (Fin s × Move)` and its fields `left_boundary`, `right_boundary` are the boundary conditions. The module defines `encodeSymbol`, `encodeMove`, `decodeMove`, `Guard`, `select` (noncomputable, by choice), `convertedTransitions` and `toDMachine A hA` for `hA : A.Deterministic`, with the facts `encode_decode`, `encodeMove_injective`, `select_eq_some_iff` and `convertedTransitions_subsingleton`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/TransitionBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/TransitionBridge.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge

namespace OAI

namespace TwoWayComplementation.CompanionBridge

open OneWayLiveness

/-- The encodings have the same two distinct endmarkers. -/
def encodeSymbol {Alpha : Type*} : Symbol Alpha → Fin 2 ⊕ Alpha
  | .left => .inl 0
  | .letter a => .inr a
  | .right => .inl 1

def encodeMove : Move → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

def decodeMove (m : Fin 3) : Move :=
  if m = 0 then .left else if m = 1 then .stay else .right

@[simp] theorem encode_decode (m : Fin 3) : encodeMove (decodeMove m) = m := by
  fin_cases m <;> rfl

theorem encodeMove_injective : Function.Injective encodeMove := by
  intro a b h
  cases a <;> cases b <;> simp_all [encodeMove]

/-- A marker-outward transition is never usable on this bounded tape. -/
def Guard {Alpha : Type*} (a : Symbol Alpha) (m : Move) : Prop :=
  (a = .left → m ≠ .left) ∧ (a = .right → m ≠ .right)

/-- Option-valued form of a partial transition. Only the single allowed element is selected. -/
noncomputable def select {X : Type*} (S : Set X) : Option X := by
  classical
  exact if h : S.Nonempty then some h.choose else none

theorem select_eq_some_iff {X : Type*} (S : Set X) (hS : S.Subsingleton) (x : X) :
    select S = some x ↔ x ∈ S := by
  classical
  unfold select
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun hx => hx ▸ h.choose_spec, fun hx => hS h.choose_spec hx⟩
  · simp only [false_iff]
    exact fun hx => h ⟨x, hx⟩

/-- Recode moves and remove only impossible outward marker transitions. -/
def convertedTransitions {Alpha : Type*} {s : ℕ} (A : TwoNFA Alpha (Fin s))
    (q : Fin s) (a : Symbol Alpha) : Set (Fin s × Move) :=
  {t | (t.1, encodeMove t.2) ∈ A.transition q (encodeSymbol a) ∧ Guard a t.2}

theorem convertedTransitions_subsingleton {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (q : Fin s) (a : Symbol Alpha) :
    (convertedTransitions A q a).Subsingleton := by
  intro x hx y hy
  have h := hA q (encodeSymbol a) hx.1 hy.1
  apply Prod.ext
  · exact congrArg (fun t : Fin s × Fin 3 => t.1) h
  · exact encodeMove_injective (congrArg (fun t : Fin s × Fin 3 => t.2) h)

/-- A deterministic machine with exactly the same states and finite accepting runs.
No halting or totality condition is introduced. -/
noncomputable def toDMachine {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) : DMachine Alpha s where
  initial := A.initial
  accepting := A.accepting
  transition q a := select (convertedTransitions A q a)
  left_boundary q q' he := by
    have h := (select_eq_some_iff _ (convertedTransitions_subsingleton A hA q .left) _).mp he
    exact h.2.1 rfl rfl
  right_boundary q q' he := by
    have h := (select_eq_some_iff _ (convertedTransitions_subsingleton A hA q .right) _).mp he
    exact h.2.2 rfl rfl

end TwoWayComplementation.CompanionBridge

end OAI


