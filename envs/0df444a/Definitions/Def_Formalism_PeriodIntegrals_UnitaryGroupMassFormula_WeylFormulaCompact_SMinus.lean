-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_SMinus
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_SMinus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:49.785986+00:00
-- url     : https://prove2.me/theorems/1d587705-c390-49f8-93ff-c5f065196a42
-- title:
--   SMinus
-- statement:
--   Definitions and structural lemmas for SMinus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/SMinus.lean

import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.WeylForKWork
open PI PI.UpqRep Matrix
variable {N : ℕ}
def sPlus (ε : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun a => ε a = true)
def sMinus (ε : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun a => ε a = false)
def blk (ε : Fin N → Bool) : Fin (nPl ε) ⊕ Fin (nMi ε) ≃ Fin N :=
  (Equiv.sumCongr
    (((sPlus ε).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (fun a => by simp [sPlus])))
    (((sMinus ε).orderIsoOfFin rfl).toEquiv.trans
      (Equiv.subtypeEquivRight (p := fun a => a ∈ sMinus ε) (q := fun a => ¬ (ε a = true))
        (fun a => by simp [sMinus])))).trans
  (Equiv.sumCompl (fun a => ε a = true))
def ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) : Fin N := blk ε (Sum.inl i)
def eMi (ε : Fin N → Bool) (j : Fin (nMi ε)) : Fin N := blk ε (Sum.inr j)
def iPl (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks h 0 0 1).submatrix (blk ε).symm (blk ε).symm
def iMi (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks 1 0 0 h).submatrix (blk ε).symm (blk ε).symm
def sPl {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin N → Bool)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ → (H →L[ℂ] H) :=
  fun h => σ (iPl ε h)
def sMi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin N → Bool)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ → (H →L[ℂ] H) :=
  fun h => σ (iMi ε h)
def wu (n : ℕ) (μ : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b), (μ a - μ b + ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) /
    ∏ i ∈ Finset.range n, (i.factorial : ℝ)
end PI.WeylForKWork


