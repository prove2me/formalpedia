-- Prove2me | Definitions.Def_Csg_IntrusionDetectionReach
-- name    : Csg_IntrusionDetectionReach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:50:59.542959+00:00
-- url     : https://prove2.me/theorems/4d118f3b-61c4-42db-ad69-136ac5871aea
-- title:
--   Intrusion Detection Reach
-- statement:
--   Definitions and structural lemmas for Intrusion Detection Reach, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
set_option autoImplicit true
namespace Csg
noncomputable def idsGameCSG : CSG IDSState PolicyAction AttackAction where
  K := idsK
  r := fun _ _ _ => 0
theorem idsGameCSG_r_zero (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) :
    idsGameCSG.r s a1 a2 = 0 := rfl
abbrev idsGoalHealthy : IDSState → Prop := fun s => s = .healthy
noncomputable def idsUnifP : PolicyAction → ℝ := fun _ => 1 / 2
noncomputable def idsUnifQ : AttackAction → ℝ := fun _ => 1 / 2
noncomputable def idsVStar : IDSState → Set.Icc (0 : ℝ) 1 := fun _ => ⟨1, by norm_num, by norm_num⟩
end Csg


