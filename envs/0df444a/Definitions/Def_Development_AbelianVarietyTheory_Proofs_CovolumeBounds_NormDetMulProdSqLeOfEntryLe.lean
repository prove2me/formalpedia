-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:43.170543+00:00
-- url     : https://prove2.me/theorems/dd9e82d2-3533-4be8-b32c-8203a659f840
-- title:
--   Norm Det Mul Prod Sq Le Of Entry Le
-- statement:
--   Definitions and structural lemmas for Norm Det Mul Prod Sq Le Of Entry Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
namespace GlobalTheory
section Pi
variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]
end Pi
section BaseChange
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing E]
  [Algebra R E] [Module.Free R S] [Module.Finite R S]
end BaseChange
section Split
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]
variable [Module.Finite R S]
variable [DecidableEq ι]
end Split
section General
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
end General
section Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Hadamard
section Etale
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]
end Etale
section DiscrBaseChange
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
end DiscrBaseChange
end GlobalTheory


