-- Prove2me | Definitions.Def_ReciprocityTheory_AdeleApproximation_AdeleIntA
-- name    : ReciprocityTheory_AdeleApproximation_AdeleIntA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:10.320879+00:00
-- url     : https://prove2.me/theorems/285f8739-fcc6-43e0-bef0-cdf7b308a8f8
-- title:
--   Adele Int A
-- statement:
--   Definitions and structural lemmas for Adele Int A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdeleApproximation/AdeleIntA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain WithZero
namespace ReciprocityTheory.UG.AdeleIntA
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
def IsInt (y : FiniteAdeleRing R K) : Prop := ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K
end ReciprocityTheory.UG.AdeleIntA


