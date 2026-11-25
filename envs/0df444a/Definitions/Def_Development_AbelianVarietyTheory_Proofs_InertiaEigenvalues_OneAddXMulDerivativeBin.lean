-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:52:46.026798+00:00
-- url     : https://prove2.me/theorems/a5e7038d-0ed3-418d-922b-b8fc8a970540
-- title:
--   One Add XMul Derivative Bin
-- statement:
--   Definitions and structural lemmas for One Add XMul Derivative Bin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
abbrev bin (c : ℤ_[l]) : O⟦X⟧ := binomialSeries O c
open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
theorem _root_.GlobalTheory.CycFr.hasSubst_bin (c : ℤ_[l]) : HasSubst (_root_.GlobalTheory.CycFr.bin O c - 1) :=
  HasSubst.of_constantCoeff_zero' (by rw [map_sub, binomialSeries_constantCoeff, map_one, sub_self])
def act (c : ℤ_[l]) : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom (hasSubst_bin O c)
def lvl (l : ℕ) (O : Type) [CommRing O] (k : ℕ) : O⟦X⟧ :=
  ∑ i ∈ Finset.range l, ((1 + X : O⟦X⟧) ^ l ^ k) ^ i
variable {O}
variable [IsDomain O] [CharZero O]
end GlobalTheory.CycFr


