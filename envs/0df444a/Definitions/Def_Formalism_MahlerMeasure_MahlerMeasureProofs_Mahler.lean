-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:14.572609+00:00
-- url     : https://prove2.me/theorems/19c9b79d-51b9-45da-bfc7-5c2a5e09bdae
-- title:
--   Mahler
-- statement:
--   Definitions and structural lemmas for Mahler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Polynomial
def zpS (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | padicNorm p x ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, padicNorm.mul] at *
    exact mul_le_one₀ ha (padicNorm.nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact le_trans padicNorm.nonarchimedean (max_le ha hb)
  zero_mem' := by simp [padicNorm.zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, padicNorm.neg] at *
    exact ha
def zpT (p : ℕ) [Fact p.Prime] : Subring ℚ[X] where
  carrier := {P | ∀ n, P.coeff n ∈ zpS p}
  mul_mem' {a b} ha hb := by
    intro n
    rw [coeff_mul]
    exact Subring.sum_mem _ (fun x _ => Subring.mul_mem _ (ha _) (hb _))
  one_mem' := by
    intro n
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {a b} ha hb := by
    intro n
    rw [coeff_add]
    exact Subring.add_mem _ (ha n) (hb n)
  zero_mem' := by intro n; simp
  neg_mem' {a} ha := by
    intro n
    rw [coeff_neg]
    exact Subring.neg_mem _ (ha n)
noncomputable def bB (c : ℚ) (i : ℕ) (t : ℤ) : ℚ[X] :=
  C ((i.factorial : ℚ)⁻¹) * (descPochhammer ℚ i).comp (C c * X + C (t : ℚ))
end Formalism.GM


