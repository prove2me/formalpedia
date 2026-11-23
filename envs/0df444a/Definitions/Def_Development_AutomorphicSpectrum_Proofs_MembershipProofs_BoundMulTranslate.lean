-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:23.375962+00:00
-- url     : https://prove2.me/theorems/804496b1-aac3-4228-8848-04a67cb4dc1b
-- title:
--   Bound Mul Translate
-- statement:
--   Definitions and structural lemmas for Bound Mul Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
namespace GlobalTheory.CompanionTheory.OM.SchDiff
section general
variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
end general
section family
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
end family
variable {κ : Type} [Fintype κ]
noncomputable def dotL (κ : Type) [Fintype κ] : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ :=
  ∑ i : κ, (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ)
noncomputable def phase (q : W κ ℝ × (κ → ℝ)) : ℝ :=
  2 * Real.pi * dotL κ q.2 q.1.2 + Real.pi * dotL κ q.1.1 q.1.2
noncomputable def ker (s : (κ → ℝ) → ℂ) (q : W κ ℝ × (κ → ℝ)) : ℂ :=
  cexp (I * (phase q : ℝ)) * s (q.2 + q.1.1)
end GlobalTheory.CompanionTheory.OM.SchDiff
namespace GlobalTheory.CompanionTheory.OM
open SchDiff
end GlobalTheory.CompanionTheory.OM


