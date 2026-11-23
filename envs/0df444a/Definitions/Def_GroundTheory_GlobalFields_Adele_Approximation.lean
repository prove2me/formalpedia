-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
-- name    : GroundTheory_GlobalFields_Adele_Approximation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:21.817775+00:00
-- url     : https://prove2.me/theorems/cbc6d6a3-1831-4065-b7ef-3811f8bfed3f
-- title:
--   Approximation
-- statement:
--   Definitions and structural lemmas for Approximation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
def integralFiniteAdeles (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := Subring.mul_mem _ (ha v) (hb v)
  one_mem' _ := Subring.one_mem _
  add_mem' ha hb v := Subring.add_mem _ (ha v) (hb v)
  zero_mem' _ := Subring.zero_mem _
  neg_mem' ha v := Subring.neg_mem _ (ha v)
instance : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))
instance (F : Type*) [Field F] : T2Space (NumberField.InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
instance : T2Space (NumberField.AdeleRing R K) :=
  inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K × FiniteAdeleRing R K))
end GroundTheory.Global


