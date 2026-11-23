-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:59.470007+00:00
-- url     : https://prove2.me/theorems/8ade2088-d644-4ec4-a2dd-881520c02001
-- title:
--   Length Base Change Quotient Of Map Maximal Ideal
-- statement:
--   Definitions and structural lemmas for Length Base Change Quotient Of Map Maximal Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
namespace GlobalTheory
section Local
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]
variable {R S}
end Local
section DVR
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
variable [IsLocalHom (algebraMap R S)]
variable (X : Type*) [AddCommGroup X] [Module R X]
end DVR
section Uniformizer
open IsDiscreteValuationRing hiding maximalIdeal
variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
end Uniformizer
end GlobalTheory


