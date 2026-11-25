-- Prove2me | Definitions.Def_OpenMath_Common
-- name    : OpenMath_Common
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:36:32.379208+00:00
-- url     : https://prove2.me/theorems/68af251a-a0a6-457d-abaa-f4a64bf3a9be
-- title:
--   Common
-- statement:
--   Definitions and structural lemmas for Common, from Rhett (v3ai/openmath; definitions reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Proof of WOWII Conjecture 96 (DeLaVina, Graffiti.pc) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedSectionVars false
namespace OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)
noncomputable def ecc (G : SimpleGraph α) (u : α) : ℕ := (G.eccent u).toNat
end OpenMath


