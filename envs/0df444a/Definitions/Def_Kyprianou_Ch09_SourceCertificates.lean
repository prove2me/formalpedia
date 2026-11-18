-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceCertificates
-- name    : Kyprianou_Ch09_SourceCertificates
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:21:53.241202+00:00
-- url     : https://prove2.me/theorems/a4adbb1a-44e0-46e6-b8d5-ffbf749af369
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceCertificates
-- statement:
--   All sixteen complete source-derived certificate propositions and the cumulative Chapter 9 goal. This source Definition module provides the actual declarations: certificate_result_9_1, certificate_result_9_2, certificate_result_9_3, certificate_result_9_4, certificate_result_9_6, certificate_result_9_7, certificate_result_9_9, certificate_result_9_10, certificate_result_9_11, certificate_result_9_12, certificate_result_9_13, certificate_result_9_14 (and 4 further declarations). The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_AppellSource
import Definitions.Def_Kyprianou_Ch09_SourceVerification
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
import Definitions.Def_Kyprianou_Ch09_SourceAppell
import Definitions.Def_Kyprianou_Ch09_SourceReflected
import Definitions.Def_Kyprianou_Ch09_SourceGame
set_option autoImplicit false

namespace Kyprianou.Ch09

universe v

/-- Canonical complete source certificate for result 9.1.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_1 : Prop := verificationLemma

/-- Canonical complete source certificate for result 9.2.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_2 : Prop := mckeanValueAndThreshold

/-- Canonical complete source certificate for result 9.3.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_3 : Prop := spectrallyNegativeMckeanScale

/-- Canonical complete source certificate for result 9.4.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_4 : Prop := mckeanContinuousSmoothFit

/-- Canonical complete source certificate for result 9.6.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_6 : Prop := novikovShiryaevOptimalStopping

/-- Canonical complete source certificate for result 9.7.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_7 : Prop := novikovShiryaevFit

/-- Canonical complete source certificate for result 9.9.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_9 : Prop := appellFirstPassageFluctuation

/-- Canonical complete source certificate for result 9.10.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_10 : Prop := appellLargestRootAndSign

/-- Canonical complete source certificate for result 9.11.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_11 : Prop := sheppShiryaevValueAndStrategy

/-- Canonical complete source certificate for result 9.12.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_12 : Prop := reflectedProcessFit

/-- Canonical complete source certificate for result 9.13.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_13 : Prop := gameSaddleVerification

/-- Canonical complete source certificate for result 9.14.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_14 : Prop := gameTwoPenaltyRegimes

/-- Canonical complete source certificate for result 9.15.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_result_9_15 : Prop := gameStrictLowerComparison

/-- Canonical complete source certificate for exercise 9.1.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_exercise_9_1 : Prop := exercise9_1

/-- Canonical complete source certificate for exercise 9.2.
Direct alias of the only matching source proposition; proof still Open. -/
noncomputable def certificate_exercise_9_2 : Prop := exercise9_2

/-- The complete Chapter 9 source contract genuinely entails the
fourteen numbered results and both whole exercises. The root is not itself
a mission milestone; each source result must remain an independent milestone. -/
noncomputable def completeChapterNine : Prop :=
  certificate_result_9_1 ∧
    certificate_result_9_2 ∧
    certificate_result_9_3 ∧
    certificate_result_9_4 ∧
    certificate_result_9_6 ∧
    certificate_result_9_7 ∧
    certificate_result_9_8.{v} ∧
    certificate_result_9_9 ∧
    certificate_result_9_10 ∧
    certificate_result_9_11 ∧
    certificate_result_9_12 ∧
    certificate_result_9_13 ∧
    certificate_result_9_14 ∧
    certificate_result_9_15 ∧
    certificate_exercise_9_1 ∧
    certificate_exercise_9_2

/-- Kernel-level implication from the aggregate to all original quantified
source parents. This is parity evidence, not proof of the chapter results. -/
theorem completeChapterNine_entails_all
    (h : completeChapterNine.{v}) :
    verificationLemma ∧
    mckeanValueAndThreshold ∧
    spectrallyNegativeMckeanScale ∧
    mckeanContinuousSmoothFit ∧
    novikovShiryaevOptimalStopping ∧
    novikovShiryaevFit ∧
    appellMeanValue.{v} ∧
    appellFirstPassageFluctuation ∧
    appellLargestRootAndSign ∧
    sheppShiryaevValueAndStrategy ∧
    reflectedProcessFit ∧
    gameSaddleVerification ∧
    gameTwoPenaltyRegimes ∧
    gameStrictLowerComparison ∧
    exercise9_1 ∧
    exercise9_2 := by
  exact h

end Kyprianou.Ch09


