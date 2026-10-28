-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Seeds
-- name    : BS2_b3ba934b_Endpoint16Seeds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:27:52.054467+00:00
-- url     : https://prove2.me/theorems/2b059873-6301-40f1-a065-07ca15e8ba62
-- title:
--   Sensitivity separation: Endpoint16Seeds (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Seeds` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Seeds.lean; original SHA-256 60aaa342db2094f3c34c81e3b17a9560a419ada86efdba02a370fdecea24f26c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The second endpoint's literal finite Boolean functions, lower witnesses,
   and conversion of the periodic profile invariant into the campaign goal.
   The last two theorems explicitly take the periodic upper invariant; its
   proof is supplied by the semantic transfer and numerical phase checks. -/
import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_ClosureHomogeneity
import Definitions.Def_BS2_b3ba934b_EndpointReduction

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 6000000

namespace ThreeBoundEndpoint16Seeds
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundFullProfile
open Sensitivity10007Endpoint16

noncomputable def coordinates (n : ℕ) :
    IterProd (Fin 10007 × Bool) n ≃ Fin (20014^n) :=
  (Fintype.equivFin _).trans (finCongr (by
    simpa only [Fintype.card_fin, Nat.reduceMul] using
      (tower_input_dimension (V := Fin 10007) n)))

noncomputable def finiteFamily (n : ℕ) (l : Fin 16) :
    (Fin (20014^n) → Bool) → Bool :=
  reindex (coordinates n) (family n l)

theorem finiteFamily_sensitivity (n : ℕ) (l : Fin 16) :
    sensitivity (finiteFamily n l) = sensitivity (family n l) :=
  sensitivity_reindex (coordinates n) (family n l)

theorem finiteFamily_lower (n : ℕ) (l : Fin 16) :
    2^n ≤ sensitivity (finiteFamily n l) ∧
      10007^n ≤ blockSensitivity (finiteFamily n l) := by
  classical
  constructor
  · rw [finiteFamily_sensitivity]
    exact (tower_lower_bounds periodicRecipe (0 : Fin 10007) n l).1
  · obtain ⟨w⟩ := tower_common_witnesses periodicRecipe (0 : Fin 10007) n
    let w' := w.reindex (coordinates n)
    have h := blockSensitivity_lower_of_indexed_blocks
      (reindex (coordinates n) (towerFamily periodicRecipe n l))
      w'.zero w'.blocks w'.blocks_nonempty w'.blocks_disjoint
      (fun a => by rw [w'.blocks_on a l,w'.zero_rejects l]; decide)
    simpa only [card_iterProd,Fintype.card_fin,finiteFamily,family] using h

theorem finiteFamily_four_stage_lower (m : ℕ) (l : Fin 16) :
    16^m ≤ sensitivity (finiteFamily (4*m) l) ∧
      (10007^4)^m ≤ blockSensitivity (finiteFamily (4*m) l) := by
  simpa only [pow_mul,show (2 : ℕ)^4=16 from rfl] using finiteFamily_lower (4*m) l

def prefactor : ℕ :=
  max (ThreeBoundMinmaxNumeric.Endpoint16.profile0 (.a 0 0))
    (ThreeBoundMinmaxNumeric.Endpoint16.profile0 (.b 0 0))

theorem prefactor_gt_one : 1 < prefactor := by decide +kernel

theorem finiteFamily_upper (m : ℕ)
    (hupper : Upper (family (4*m))
      (scale (31192129^m) ThreeBoundMinmaxNumeric.Endpoint16.profile0)) :
    sensitivity (finiteFamily (4*m) 0) ≤ prefactor*31192129^m := by
  rw [finiteFamily_sensitivity]
  have ha := hupper (.a 0 0) (le_refl (0 : Fin 16))
  have hb := hupper (.b 0 0) (le_refl (0 : Fin 16))
  have h := sensitivity_le_diagonal_max (family (4*m)) 0 _ _ ha hb
  simpa only [scale,← Nat.mul_max_mul_left,prefactor,Nat.mul_comm] using h

theorem seeds_of_periodic_upper
    (hupper : ∀ m : ℕ, Upper (family (4*m))
      (scale (31192129^m) ThreeBoundMinmaxNumeric.Endpoint16.profile0)) :
    ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧ sensitivity f ≤ prefactor*31192129^m ∧
        (10007^4)^m ≤ blockSensitivity f := by
  intro m
  refine ⟨20014^(4*m),finiteFamily (4*m) 0,?_,?_,?_⟩
  · exact (finiteFamily_four_stage_lower m 0).1
  · exact finiteFamily_upper m (hupper m)
  · exact (finiteFamily_four_stage_lower m 0).2

theorem achieves_213519_of_periodic_upper
    (hupper : ∀ m : ℕ, Upper (family (4*m))
      (scale (31192129^m) ThreeBoundMinmaxNumeric.Endpoint16.profile0)) :
    SensitivityCampaign.AchievesExponent ((213519 : ℝ)/100000) :=
  ThreeBoundEndpoint.reach_213519_of_seeds prefactor prefactor_gt_one
    (seeds_of_periodic_upper hupper)

end ThreeBoundEndpoint16Seeds

#print axioms ThreeBoundEndpoint16Seeds.finiteFamily_lower
#print axioms ThreeBoundEndpoint16Seeds.finiteFamily_upper
#print axioms ThreeBoundEndpoint16Seeds.achieves_213519_of_periodic_upper


