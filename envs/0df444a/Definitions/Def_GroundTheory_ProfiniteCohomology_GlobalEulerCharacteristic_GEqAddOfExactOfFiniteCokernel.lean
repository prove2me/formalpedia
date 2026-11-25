-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:11:55.554278+00:00
-- url     : https://prove2.me/theorems/67eb58e1-0e84-4872-9735-8f9327b42fae
-- title:
--   GEq Add Of Exact Of Finite Cokernel
-- statement:
--   Definitions and structural lemmas for GEq Add Of Exact Of Finite Cokernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
section Finiteness
variable {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (n : ℕ) [NeZero n]
end Finiteness
namespace AdditiveFunction
variable {l : ℕ} [NeZero l] {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
end AdditiveFunction
section LogLattice
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
end LogLattice
namespace AdditiveFunction
section Units
variable {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (L ≃ₐ[K] L))
end Units
end AdditiveFunction
end GroundTheory.ProfCoh


