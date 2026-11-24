-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:50.729803+00:00
-- url     : https://prove2.me/theorems/34829ba4-415a-43ac-82bf-99d759860927
-- title:
--   Fibre Rank Comp Of Surjective
-- statement:
--   Definitions and structural lemmas for Fibre Rank Comp Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
namespace GlobalTheory.PDiv
variable {O : Type} [CommRing O]
abbrev fibreDim (M : Type) [AddCommGroup M] [Module O M] (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] M)
abbrev fibreRank {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField))
section Linear
variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]
variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
end Linear
variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]
variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]
end GlobalTheory.PDiv


