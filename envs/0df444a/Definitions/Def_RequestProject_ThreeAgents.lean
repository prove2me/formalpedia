-- Prove2me | Definitions.Def_RequestProject_ThreeAgents
-- name    : RequestProject_ThreeAgents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:12:36.063937+00:00
-- url     : https://prove2.me/theorems/2c14eaaf-7118-4396-a5cc-d5088db22798
-- title:
--   Three Agents
-- statement:
--   Definitions and structural lemmas for Three Agents, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def restrictVal (R : Finset G) (w : G → ℝ) : G → ℝ := fun g => if g ∈ R then w g else 0
inductive MainLemmaTwoLoss (w p : G → ℝ) (B : Finset G) : Prop
  | pure (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p)
      (hB : vbarSum w p B ≤ (3/4) * MMS 3 w p)
  | untouched (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
      (lost j k : Fin 3) (g : G) (hB : B = {g})
      (hcfg : ConfigN 3 w p (MMS 3 w p) A s q)
      (hlj : lost ≠ j) (hlk : lost ≠ k) (hjk : j ≠ k) (hg : g ∈ A lost)
  | paired (C : Finset G) (hC : C ⊆ Finset.univ \ B)
      (hClo : (3/4) * MMS 3 w p ≤ vbarSum w p C)
      (hChi : vbarSum w p C ≤ MMS 3 w p)
      (hR : MMS 3 w p + (3/4) * MMS 3 w p ≤ vbarSum w p (Finset.univ \ B))
end FairSelling


