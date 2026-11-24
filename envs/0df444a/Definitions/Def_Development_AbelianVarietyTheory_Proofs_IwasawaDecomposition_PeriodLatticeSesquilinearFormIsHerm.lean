-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:26:45.725909+00:00
-- url     : https://prove2.me/theorems/0b657b10-2fbd-4ba9-ab5d-455ea3c91a95
-- title:
--   Period Lattice Sesquilinear Form Is Herm
-- statement:
--   Definitions and structural lemmas for Period Lattice Sesquilinear Form Is Herm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_latticeForm_add_left
import Theorems.Thm_GlobalTheory_latticeForm_add_right
import Theorems.Thm_GlobalTheory_latticeForm_mul_left
import Theorems.Thm_GlobalTheory_latticeForm_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
def form1 : Sesq ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => latticeForm L z w)
    (latticeForm_add_left L) (fun a u v => latticeForm_mul_left L a u v) (latticeForm_add_right L)
    (fun a u v => latticeForm_mul_right L a u v)
section Std
variable {n : Type} [Fintype n] [DecidableEq n]
end Std
section Four
variable {n : Type} [Fintype n]
def ins (z : Fin 4 × n → ℂ) (x : n → ℂ) : Fin 4 × n → ℂ := fun w => if w.1 = 0 then x w.2 else z w
end Four
end GlobalTheory.Mem.Col2.ThetaVec


