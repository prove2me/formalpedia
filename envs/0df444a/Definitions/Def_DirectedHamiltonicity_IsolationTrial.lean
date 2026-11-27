-- Prove2me | Definitions.Def_DirectedHamiltonicity_IsolationTrial
-- name    : DirectedHamiltonicity_IsolationTrial
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:49:48.765842+00:00
-- url     : https://prove2.me/theorems/fa696a52-2846-4c8c-ab7b-ef034e31ab0a
-- title:
--   The finite three-group isolation experiment for directed Hamiltonian paths
-- statement:
--   Each arc receives one of 50 equiprobable symbols. One deletes the arc and seven symbols encode each nonempty subset of three incoming groups. Give each vertex-group pair outside the start vertex a uniform weight from one to twice the number of such pairs. The event records whether any admissible total weight has an odd number of labelled Hamiltonian paths.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies

namespace DirectedHamiltonicity.Main.IsolationTrial

/-- Labels of the three incoming groups at vertices other than the start. -/
abbrev Group {V : Type} (s : V) := {v : V // v ≠ s} × Fin 3

/-- A sample consists of one 50-valued symbol per arc and one bounded weight per group. -/
abbrev Seed {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj] (s : V) :=
  (SArc adj → Fin 50) × (Group s → Fin (2 * Fintype.card (Group s)))

/-- Symbol zero deletes the arc. Each of the seven nonzero three-bit masks has seven preimages. -/
def mask (x : Fin 50) : Finset (Fin 3) :=
  Finset.univ.filter fun j => (if x.val = 0 then 0 else 1 + (x.val-1)/7).testBit j.val

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj] (s t : V)
variable (hs : ∀ u, ¬ adj u s)

def groupWeight (z : Seed adj s) (x : ArcCopy adj (fun a => mask (z.1 a))) : ℕ :=
  (z.2 (⟨x.1.1.2, fun h => hs x.1.1.1 ((congrArg (adj x.1.1.1) h).mp x.1.2)⟩,x.2.val)).val+1

open Classical in
/-- Some admissible total weight has an odd number of labelled Hamiltonian paths. -/
def Hits (z : Seed adj s) : Prop :=
  ∃ B : ℕ, B ≤ (Fintype.card V-1)*(2*Fintype.card (Group s)) ∧
    Odd ((copyGraph adj (fun a => mask (z.1 a))).weightedPathCount (groupWeight adj s hs z) s t B)

end DirectedHamiltonicity.Main.IsolationTrial


