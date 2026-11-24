-- Prove2me | Definitions.Def_RequestProject_SmallN
-- name    : RequestProject_SmallN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:54.38166+00:00
-- url     : https://prove2.me/theorems/4b3a0f44-7f24-4c7e-b64f-b2ce77e6ea59
-- title:
--   Small N
-- statement:
--   Definitions and structural lemmas for Small N, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
noncomputable def minUtil (v : G → ℝ) (o : Outcome G n) : ℝ := ⨅ j, util v o j
def outcomeOf (assign : G → Option (Fin n)) (m : Fin n → ℝ) : Outcome G n where
  sold := Finset.univ.filter (fun g => assign g = none)
  kept := fun j => Finset.univ.filter (fun g => assign g = some j)
  money := m
noncomputable def procOf (p : G → ℝ) (assign : G → Option (Fin n)) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => assign g = none), p g
noncomputable def keptVal (v : G → ℝ) (assign : G → Option (Fin n)) (j : Fin n) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => assign g = some j), v g
noncomputable def minUtilData (v : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ) : ℝ :=
  ⨅ j, keptVal v assign j + m j
open Classical in
/-- The concrete outcome realizing the unified assignment where agent `i` receives the goods
`A i` (to keep or sell privately), the goods in `F` are force-sold, and `q i` is the share of
the force-sale proceeds given to agent `i`. -/
noncomputable def unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) : Outcome G n where
  sold := F ∪ Finset.univ.biUnion (fun i => (A i).filter (fun g => v i g < p g))
  kept := fun i => (A i).filter (fun g => ¬ v i g < p g)
  money := fun i => q i + ∑ g ∈ (A i).filter (fun g => v i g < p g), p g
end FairSelling


