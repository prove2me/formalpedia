-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:51.193101+00:00
-- url     : https://prove2.me/theorems/69301240-2079-4857-b514-5fd5baae61d8
-- title:
--   Frobenius Sum Formula
-- statement:
--   Definitions and structural lemmas for Frobenius Sum Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/FrobeniusSumFormula.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply


set_option autoImplicit false
noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
namespace PI.SerBridgeGLW
theorem levi_mul' (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  show blk K b c (((p * q : parab K b) : GL ι K) : Matrix ι ι K) =
    blk K b c ((p : GL ι K) : Matrix ι ι K) * blk K b c ((q : GL ι K) : Matrix ι ι K)
  rw [← blk_mul b c p.2.1 q.2.1]
  rfl
theorem levi_one' (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  show blk K b c (((1 : parab K b) : GL ι K) : Matrix ι ι K) = 1
  exact Matrix.submatrix_one _ Subtype.val_injective
def inflRep (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :
    Representation ℂ (parab K b) (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam p
  map_one' := by
    simp only [infl, levi_one', map_one]
    exact PiTensorProduct.map_one
  map_mul' p q := by
    simp only [infl, levi_mul', map_mul]
    exact PiTensorProduct.map_mul _ _
end PI.SerBridgeGLW


