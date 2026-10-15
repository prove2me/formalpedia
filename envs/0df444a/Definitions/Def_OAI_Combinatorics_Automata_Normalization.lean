-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Normalization
-- name    : OAI_Combinatorics_Automata_Normalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:54:38.68745+00:00
-- url     : https://prove2.me/theorems/aee0e5ce-8bdc-4533-9133-a063e11dd5ff
-- title:
--   Two-way deterministic machines on arbitrary state sets, the positive-start copy and the sink normalization
-- statement:
--   Throughout, $\Sigma$ is an input alphabet and a word $w=a_1\cdots a_n\in\Sigma^*$ is read between two endmarkers: position $0$ carries $\vdash$, position $i$ carries $a_i$ for $1\le i\le n$, and position $n+1$ carries $\dashv$. The file records that the scanned symbol is $\vdash$ exactly at position $0$ and $\dashv$ exactly at position $n+1$. The moves $L,S,R$ change the position by $-1,0,+1$.
--
--   1. **Machines on an arbitrary state set.** A deterministic two-way machine $M$ over $\Sigma$ with state set $Q$ (any set, not necessarily finite) consists of an initial state $q_0\in Q$, a set $A\subseteq Q$ of accepting states and a partial transition function
--   $$\delta:Q\times(\Sigma\cup\{\vdash,\dashv\})\rightharpoonup Q\times\{L,S,R\}$$
--   that never moves left from $\vdash$ and never moves right from $\dashv$. A configuration on $w$ is a pair $(i,q)$ with $0\le i\le n+1$ and $q\in Q$, and $(i,q)\to(j,q')$ is a step when $\delta(q,b_i)=(q',m)$ for the symbol $b_i$ at position $i$ and $j=i+m$. For a Boolean flag $\pi$, the machine accepts $w$ if some configuration with an accepting state is reached from $(0,q_0)$ by a run of at least one step when $\pi$ is true, and by a run of any length, including zero, when $\pi$ is false. Every deterministic machine with the state set $\{0,\dots,s-1\}$ is such a machine.
--
--   2. **Positive-start copy.** The machine on $Q\sqcup\{\star\}$ with the new initial state $\star$, which is not accepting; its accepting states are those of $M$, and its transitions are $\delta(q,b)$ from $q\in Q$ and $\delta(q_0,b)$ from $\star$. Every transition leads into $Q$.
--
--   3. **Sink normalization.** The machine on $Q\sqcup\{f\}$ with initial state $q_0$, the single accepting state $f$ and transitions
--   $$\delta^{\sharp}(q,b)=\begin{cases}(f,S), & q\in A,\\ \delta(q,b), & q\in Q\setminus A,\\ (f,R), & q=f,\ b\neq\dashv,\\ \text{undefined}, & q=f,\ b=\dashv.\end{cases}$$
--   The first case applies even where $\delta(q,b)$ is undefined.
--
--   4. **Terminal configuration.** For a word $w$ of length $n$, the configuration $t_w=(n+1,f)$ of the sink normalization, in which the new state $f$ scans the right endmarker; it has no successor.
--
--   The positive-start copy converts acceptance after a positive number of steps into acceptance with runs of length zero allowed, at the cost of one extra state. The sink normalization turns acceptance into reachability of the single configuration $t_w$, which has no successor. Together they reduce both acceptance conventions to one reachability question about a configuration without successor, which is what the matching-diagram representation of a machine encodes.
--
--   **Formalization Note** `Machine Alpha Q` (with `Q : Type`) has fields `initial`, `accepting`, `transition : Q → Symbol Alpha → Option (Q × Move)` and the two boundary conditions; `Config`, `Step` and `Accepts positive w` mirror the definitions for `DMachine`, where `FiniteRun` is `TransGen` for `positive = true` and `ReflTransGen` for `positive = false`, and `DMachine.toMachine` repackages a `DMachine` on `Fin s`. Both copies have state type `Option Q` with `none` as the new state; `positiveCopy` reads the row of `none` through `q.getD M.initial`, and `sinkCopy` is noncomputable because membership in `accepting` is decided classically. `terminal w` is the configuration `(⟨w.length + 1, _⟩, none)`, and the endmarker positions are `scanned_eq_left_iff` and `scanned_eq_right_iff`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Normalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Normalization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours

namespace OAI

namespace OneWayLiveness

/-- A deterministic automaton on an arbitrary state type. -/
structure Machine (Alpha Q : Type) where
  initial : Q
  accepting : Set Q
  transition : Q → Symbol Alpha → Option (Q × Move)
  left_boundary : ∀ q q', transition q .left ≠ some (q', .left)
  right_boundary : ∀ q q', transition q .right ≠ some (q', .right)

namespace Machine
variable {Alpha Q : Type}
variable (M : Machine Alpha Q)
abbrev Config (w : List Alpha) := Fin (w.length + 2) × Q

def Step (w : List Alpha) (c c' : Config (Q := Q) w) : Prop :=
  ∃ d, M.transition c.2 (scanned w c.1) = some (c'.2, d) ∧ d.Rel c.1.val c'.1.val

def Accepts (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting

end Machine

def DMachine.toMachine {Alpha : Type} {s : ℕ} (M : DMachine Alpha s) : Machine Alpha (Fin s) :=
  ⟨M.initial, M.accepting, M.transition, M.left_boundary, M.right_boundary⟩

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

/-- A fresh nonaccepting initial state copies the original initial row. -/
def positiveCopy : Machine Alpha (Option Q) where
  initial := none
  accepting := {q | ∃ a, q = some a ∧ a ∈ M.accepting}
  transition q b := (M.transition (q.getD M.initial) b).map (fun x => (some x.1, x.2))
  left_boundary q q' h := by
    cases ht : M.transition (q.getD M.initial) .left with
    | none => simp [ht] at h
    | some x =>
      rcases x with ⟨r, d⟩
      simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact M.left_boundary _ r (h.2 ▸ ht)
  right_boundary q q' h := by
    cases ht : M.transition (q.getD M.initial) .right with
    | none => simp [ht] at h
    | some x =>
      rcases x with ⟨r, d⟩
      simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact M.right_boundary _ r (h.2 ▸ ht)

/-- Sink normalization also replaces missing transitions at accepting states. -/
noncomputable def sinkCopy : Machine Alpha (Option Q) := by
  classical
  exact {
    initial := some M.initial
    accepting := {none}
    transition := fun q b => match q with
      | some q => if q ∈ M.accepting then some (none, .stay)
          else (M.transition q b).map (fun x => (some x.1, x.2))
      | none => match b with
        | .right => none
        | _ => some (none, .right)
    left_boundary := by
      intro q q' h
      cases q with
      | none => simp at h
      | some q =>
        dsimp only at h
        split_ifs at h with hq
        · cases h
        · obtain ⟨⟨r,d⟩, ht, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          exact M.left_boundary _ r (he.2 ▸ ht)
    right_boundary := by
      intro q q' h
      cases q with
      | none => cases h
      | some q =>
        dsimp only at h
        split_ifs at h with hq
        · cases h
        · obtain ⟨⟨r,d⟩, ht, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          exact M.right_boundary _ r (he.2 ▸ ht) }

end Machine

lemma scanned_eq_left_iff {Alpha : Type} (w : List Alpha) (i : Fin (w.length + 2)) :
    scanned w i = .left ↔ i.val = 0 := by
  simp only [scanned]
  split_ifs <;> simp_all

lemma scanned_eq_right_iff {Alpha : Type} (w : List Alpha) (i : Fin (w.length + 2)) :
    scanned w i = .right ↔ i.val = w.length + 1 := by
  simp only [scanned]
  split_ifs <;> simp_all <;> omega

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

def terminal (w : List Alpha) : Config (Q := Option Q) w := (⟨w.length + 1, by omega⟩, none)

end Machine
end OneWayLiveness

end OAI


