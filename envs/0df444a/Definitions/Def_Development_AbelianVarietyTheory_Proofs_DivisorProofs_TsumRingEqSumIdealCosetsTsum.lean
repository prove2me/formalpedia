-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:43.583029+00:00
-- url     : https://prove2.me/theorems/d8537ef5-56bf-440a-9f7f-c93fb63521bf
-- title:
--   Tsum Ring Eq Sum Ideal Cosets Tsum
-- statement:
--   Definitions and structural lemmas for Tsum Ring Eq Sum Ideal Cosets Tsum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumRingEqSumIdealCosetsTsum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
namespace GlobalTheory
noncomputable def quotCosetProdEquiv (R : Type) [CommRing R] (M : Ideal R) : (R ⧸ M) × M ≃ R where
  toFun p := Quotient.out p.1 + (p.2 : R)
  invFun α := (Ideal.Quotient.mk M α, ⟨α - Quotient.out (Ideal.Quotient.mk M α), by
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm⟩)
  left_inv p := by
    obtain ⟨c, μ⟩ := p
    have hc : Ideal.Quotient.mk M (Quotient.out c + (μ : R)) = c := by
      rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.eq_zero_iff_mem.mpr μ.2, add_zero]
    ext
    · exact hc
    · simp only [hc]; ring
  right_inv α := by simp
end GlobalTheory


