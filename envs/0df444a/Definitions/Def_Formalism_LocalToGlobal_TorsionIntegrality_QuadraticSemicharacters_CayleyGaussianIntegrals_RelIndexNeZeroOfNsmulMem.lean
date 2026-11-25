-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:19:03.434732+00:00
-- url     : https://prove2.me/theorems/67a42a7a-9a80-4e8a-98e4-a93acfec9f2c
-- title:
--   Rel Index Ne Zero Of Nsmul Mem
-- statement:
--   Definitions and structural lemmas for Rel Index Ne Zero Of Nsmul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Index
variable {V : Type*} [AddCommGroup V]
def nsmulHom [Module ℂ V] (N : ℕ) : V →+ V where
  toFun x := N • x
  map_zero' := smul_zero _
  map_add' _ _ := smul_add _ _ _
end Index
section Lattice
instance periodLattice_finite (L : PeriodPair) : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice
def stdLatEquiv (L : PeriodPair) (m : Type*) : stdLat L m ≃+ (m → L.lattice) where
  toFun x := fun i => ⟨(x : m → ℂ) i, (mem_stdLat L m x).1 x.2 i⟩
  invFun y := ⟨fun i => (y i : ℂ), (mem_stdLat L m _).2 fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
end Lattice
end Formalism.L2.Th1.H


