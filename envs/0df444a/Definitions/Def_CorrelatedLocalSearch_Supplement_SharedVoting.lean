-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Supplement_SharedVoting
-- name    : CorrelatedLocalSearch_Supplement_SharedVoting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:03:18.239046+00:00
-- url     : https://prove2.me/theorems/8e3ac6ca-376c-4841-9635-ea264d7a707c
-- title:
--   Shared-source discordant voting and the sine profile $V_N$
-- statement:
--   A finite disjoint union of connected components carries binary vertex values. A nonanticipating selector chooses a disagreeing edge. The four labels, with reference probabilities $(49/100,1/4,1/4,1/100)$, set its endpoints to $00$, leave them unchanged, reverse them, or set them to $11$. Constant components are finished. The layer defines $\Delta_N$, the exact sine profile $V_N$, the number $K_0$ of ones in initially nonconstant components, the process and its stopping time.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. G pp.42–43 (PDF pp.44–45)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_GeneralSource

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Reference label probabilities `(49/100,1/4,1/4,1/100)`. -/
noncomputable def votingPi (z : Fin 4) : Real :=
  match z.val with
  | 0 => 49 / 100
  | 1 => 1 / 4
  | 2 => 1 / 4
  | _ => 1 / 100

/-- The independent reference law on the shared four-label tape. -/
noncomputable def votingReferenceMeasure : Measure (Nat -> Fin 4) :=
  Measure.infinitePi (fun _ : Nat =>
    ∑ z : Fin 4, ENNReal.ofReal (votingPi z) • Measure.dirac z)

/-- The unique `Delta_N in (1/2,1)` solving the displayed equation in Appendix G. -/
noncomputable def votingThreshold (N : Nat) : Real :=
  sInf {s : Real | 1 / 2 ≤ s ∧
    2 * 4 ^ (-s) + 2 * (7 / 100 : Real) ^ s * Real.cos (Real.pi / N) ≤ 1}

/-- The sine profile `V_N`. -/
noncomputable def votingValue (N k : Nat) : Real :=
  let s := votingThreshold N
  let r := (7 : Real) ^ s
  if k = 0 then 0
  else if k < N - 1 then r ^ ((k : Int) - (N : Int) + 1) *
    Real.sin (k * (Real.pi / N)) / Real.sin (Real.pi / N)
  else 1

/-- A finite disjoint union of connected discordant-voting components. -/
structure SharedVotingSystem (N : Nat) where
  Vertex : Type
  finiteVertex : Fintype Vertex
  decidableEqVertex : DecidableEq Vertex
  component : Vertex -> Nat
  adjacent : Vertex -> Vertex -> Prop
  adjacent_symm : Std.Symm adjacent
  adjacent_same_component : ∀ u v, adjacent u v -> component u = component v
  connected_component : ∀ u v, component u = component v -> Relation.ReflTransGen adjacent u v
  component_size : ∀ c, (∃ v, component v = c) ->
    N ≤ Set.ncard {v | component v = c}
  initial : Vertex -> Bool

attribute [instance] SharedVotingSystem.finiteVertex
attribute [instance] SharedVotingSystem.decidableEqVertex

abbrev VotingSelector {N : Nat} (G : SharedVotingSystem N) :=
  List (Fin 4) -> (G.Vertex -> Bool) -> Option (G.Vertex × G.Vertex)

def VotingFinished {N : Nat} (G : SharedVotingSystem N) (x : G.Vertex -> Bool) : Prop :=
  ∀ u v, G.component u = G.component v -> x u = x v

def IsValidVotingSelector {N : Nat} (G : SharedVotingSystem N) (sel : VotingSelector G) : Prop :=
  ∀ pre x,
    (VotingFinished G x -> sel pre x = none) ∧
    (¬ VotingFinished G x -> ∃ u v, sel pre x = some (u, v) ∧
      G.adjacent u v ∧ x u ≠ x v)

open Classical in
def votingStep {N : Nat} (G : SharedVotingSystem N) (sel : VotingSelector G)
    (pre : List (Fin 4)) (x : G.Vertex -> Bool) (z : Fin 4) : G.Vertex -> Bool :=
  match sel pre x with
  | none => x
  | some e =>
      match z.val with
      | 0 => Function.update (Function.update x e.1 false) e.2 false
      | 1 => x
      | 2 => Function.update (Function.update x e.1 (x e.2)) e.2 (x e.1)
      | _ => Function.update (Function.update x e.1 true) e.2 true

noncomputable def votingRunFrom {N : Nat} (G : SharedVotingSystem N)
    (sel : VotingSelector G) :
    List (Fin 4) -> (G.Vertex -> Bool) -> List (Fin 4) -> (G.Vertex -> Bool)
  | _, x, [] => x
  | pre, x, z :: rest =>
      votingRunFrom G sel (pre ++ [z]) (votingStep G sel pre x z) rest

noncomputable def votingState {N : Nat} (G : SharedVotingSystem N)
    (sel : VotingSelector G) (w : List (Fin 4)) : G.Vertex -> Bool :=
  votingRunFrom G sel [] G.initial w

noncomputable def votingTau {N : Nat} (G : SharedVotingSystem N)
    (sel : VotingSelector G) (omega : Nat -> Fin 4) : ℕ∞ :=
  ⨅ (t : Nat) (_h : VotingFinished G (votingState G sel (tapePrefix omega t))), (t : ℕ∞)

/-- A component is initially nonconstant. -/
def InitiallyNonconstant {N : Nat} (G : SharedVotingSystem N) (c : Nat) : Prop :=
  (∃ u, G.component u = c ∧ G.initial u = false) ∧
    ∃ v, G.component v = c ∧ G.initial v = true

/-- Number of ones in initially nonconstant components. -/
noncomputable def initialLiveOnes {N : Nat} (G : SharedVotingSystem N) : Nat :=
  Set.ncard {v | G.initial v = true ∧ InitiallyNonconstant G (G.component v)}

/-- Main catalog declaration for shared-source discordant voting. -/
abbrev SharedVoting (N : Nat) := SharedVotingSystem N

end CorrelatedLocalSearch.Supplement


