-- Prove2me | Definitions.Def_r03_defs_191207a298_r03_sp01_c3c3_complement_lean_candidate_v1
-- name    : r03_defs_191207a298_r03_sp01_c3c3_complement_lean_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:24.41218+00:00
-- url     : https://prove2.me/theorems/f8f995e9-3f42-4c61-b4ce-a2a5b7cff2eb
-- title:
--   R03 P3-factor definition module: r03_defs_191207a298_r03_sp01_c3c3_complement_lean_candidate_v1
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-c3c3-complement-lean-candidate-v1.lean; source SHA-256 cd17740cb8be66723af1ed58716c762071f06cc490645c56d595e991ec98c720; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

/-!
Candidate-only generic C3 disjoint union C3 complement lemma for SP01.

The supplied equivalence `parts` labels two triples by indices 0..2 and 3..5;
the hypothesis says that no complement edge crosses these two triples.  The
explicit permutation then realizes the two paths (A0,B0,A1) and (B1,A2,B2).
The cubic-to-complement classification is intentionally not assumed here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace R03SP01C3C3Complement

abbrev V := Fin 6

structure LocalP3Factor (G : SimpleGraph V) where
  blockCount : Nat
  place : (Fin blockCount × Fin 3) ≃ V
  edge01 : ∀ i : Fin blockCount, G.Adj (place (i, 0)) (place (i, 1))
  edge12 : ∀ i : Fin blockCount, G.Adj (place (i, 1)) (place (i, 2))

def triTo : Fin 6 → Fin 6 := ![0, 3, 1, 4, 2, 5]
def triInv : Fin 6 → Fin 6 := ![0, 2, 4, 1, 3, 5]

def triEquiv : Fin 6 ≃ Fin 6 where
  toFun := triTo
  invFun := triInv
  left_inv := by decide
  right_inv := by decide

/-- The two triples in the complement have no complement edge between them. -/
def ComplementHasTwoParts (G : SimpleGraph V) (parts : Fin 6 ≃ V) : Prop :=
  ∀ u v, u.val / 3 ≠ v.val / 3 → ¬ Gᶜ.Adj (parts u) (parts v)

def c3c3Place (parts : Fin 6 ≃ V) : (Fin 2 × Fin 3) ≃ V :=
  finProdFinEquiv.trans (triEquiv.trans parts)

end R03SP01C3C3Complement


