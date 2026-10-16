-- Prove2me | Definitions.Def_BS20205_Sharp_Bounds
-- name    : BS20205_Sharp_Bounds
-- status  : Definition
-- author  : @Leo Shaposhnik
-- created : 2026-10-15T23:50:57.274867+00:00
-- url     : https://prove2.me/theorems/f7ee9abd-e022-411b-828b-620aafb940ca
-- title:
--   A sharper simultaneous four-profile recurrence
-- statement:
--   For $M,r\in\mathbb N$ and a natural-number vector $v=(a,b,c,e)$, define
--   $$\Phi_{M,r}(a,b,c,e)=\left(15a+\max(b+e,3e),\ M^2a+rb,\ 15a+3e,\ M^2c+rb\right).$$
--   For an initial budget $L\in\mathbb N$, define the sequence $v_n$ by
--   $$v_0=(L,LM,0,0),\qquad v_{n+1}=\Phi_{M,r}(v_n).$$
--   The Lean definitions are `sharpStep M r` and `sharpBounds M r L n`. The four entries correspond to bounds for zero-side, one-side, zero-joint and one-joint sensitivity, in that order. Updates are simultaneous: every right-hand side uses the previous vector. This bundle specifies the recurrence only; its domination of the construction is proved separately. The coefficient $15$ and maximum distinguish it from the older coefficient-$16$, additive gate estimate.
-- source:
--   Local research commit f142fafe7b0ad4f46d209a530ee057421fe0f374, lean/round2-sharp/Sharp/Bounds.lean, sharpStep and sharpBounds. Built on OpenAI, A superquadratic separation between sensitivity and block sensitivity (September 25, 2026), source: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity. Existing platform definitions are reused unchanged; supporting upstream helpers retain OpenAI attribution.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2-sharp/Sharp/Bounds.lean
Modifications: mechanical skeleton subtraction, import rewriting,
and a root solution alias with the same elaborated theorem type.
Copied upstream files previously received only the documented Lean
conditional-proof lemma-name port; mathematical definitions and
statements were preserved. This generated file is local staging.
-/

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Theorems.Thm_OAI_Paper320_Tournament_card_badLabelings_le
import Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges
import Theorems.Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one
import Theorems.Thm_OAI_Paper320_Tournament_labelingConstraint_iff
import Theorems.Thm_OAI_Paper320_ballPredicate_sensitivityAt_zero_le
import Theorems.Thm_OAI_Paper320_blockSensitivityAt_compose_zero_le
import Theorems.Thm_OAI_Paper320_coupled_profiles_bound
import Theorems.Thm_OAI_Paper320_exists_blockSensitivityAt_family
import Theorems.Thm_OAI_Paper320_initialFamily_joint
import Theorems.Thm_OAI_Paper320_le_blockSensitivityAt_of_family
import Theorems.Thm_OAI_Paper320_normalized_profiles_step
import Theorems.Thm_OAI_Paper320_quantitative_profile_bounds
import Theorems.Thm_OAI_Paper320_quantitative_separation
import Theorems.Thm_OAI_Paper320_recursive_joint_one_at
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_one_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at
import Theorems.Thm_OAI_Paper320_rowClause_repair_cases
import Theorems.Thm_OAI_Paper320_sensitivity_orCopies_le
import Theorems.Thm_OAI_Paper320_towerFamily_blocks
import Theorems.Thm_OAI_Paper320_tower_four_recurrences
import Theorems.Thm_SensitivityCampaign_baseline
import Theorems.Thm_SensitivityCampaign_baseline_arithmetic
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_openai_seed_bounds
import Definitions.Def_BS20205_Round2_Bounds
import Definitions.Def_BS20205_Round2_GeneralSeed


namespace OAI.Paper320

def sharpStep (M r : ℕ) (v : RawBounds) : RawBounds :=
  ⟨15*v.s0+max (v.s1+v.j1) (3*v.j1), M^2*v.s0+r*v.s1,
    15*v.s0+3*v.j1, M^2*v.j0+r*v.s1⟩

def sharpBounds (M r L : ℕ) : ℕ → RawBounds
  | 0 => ⟨L,L*M,0,0⟩
  | n+1 => sharpStep M r (sharpBounds M r L n)

end OAI.Paper320


