-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:37.469816+00:00
-- url     : https://prove2.me/theorems/4b12b14c-3ecb-4c11-b410-f76de0581a41
-- title:
--   Is Discrete Valuation Ring Localization Of Is Dedekind D
-- statement:
--   Definitions and structural lemmas for Is Discrete Valuation Ring Localization Of Is Dedekind D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
namespace NormVal
section Det
variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
end Det
section Semilocal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
end Semilocal
end NormVal
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
section Local
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
variable [∀ n, IsDomain (A n)] [∀ n, IsDiscreteValuationRing (A n)]
variable [∀ n, Algebra R (A n)] [∀ n, IsScalarTower R S (A n)]
  [∀ n, IsLocalHom (algebraMap R (A n))]
end Local
end GlobalTheory


