-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:34.718946+00:00
-- url     : https://prove2.me/theorems/6d6807f0-ef07-410b-a937-1c61acf63a2e
-- title:
--   Smooth Vec
-- statement:
--   Definitions and structural lemmas for Smooth Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Group
variable {k r : ℕ}
end Group
section SmoothJ
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
end SmoothJ
section Conj
variable {k r : ℕ}
end Conj
section Lin
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}
def svSub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) : Submodule ℂ Wp where
  carrier := SmVec k r z π
  zero_mem' := by
    intro h _ X _
    simp only [map_zero]
    exact differentiableAt_const _
  add_mem' := by
    intro x y hx hy h hh X hX
    simp only [map_add]
    exact (hx h hh X hX).add (hy h hh X hX)
  smul_mem' := by
    intro c x hx h hh X hX
    simp only [map_smul]
    exact (hx h hh X hX).const_smul c
end Lin
section Frame
variable {k r : ℕ}
end Frame
section QM
end QM
section Cap
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}
end Cap
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors


