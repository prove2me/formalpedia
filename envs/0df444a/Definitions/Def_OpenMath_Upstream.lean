-- Prove2me | Definitions.Def_OpenMath_Upstream
-- name    : OpenMath_Upstream
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:38:06.61965+00:00
-- url     : https://prove2.me/theorems/57123b68-ef11-5011-b473-cdc1592ba440
-- title:
--   Upstream
-- statement:
--   Definitions and structural lemmas for Upstream, from Rhett (v3ai/openmath; definitions reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Proof of WOWII Conjecture 96 (DeLaVina, Graffiti.pc) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Upstream.lean

module
public import Definitions.Def_OpenMath_WOWII96
public import Definitions.Def_OpenMath_WOWII19
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SimpleGraph
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
end SimpleGraph
namespace WrittenOnTheWallII.GraphConjecture96
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
end WrittenOnTheWallII.GraphConjecture96
namespace WrittenOnTheWallII.GraphConjecture19
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
end WrittenOnTheWallII.GraphConjecture19


