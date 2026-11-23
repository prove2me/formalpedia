-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:36.293615+00:00
-- url     : https://prove2.me/theorems/33280be6-c741-43bd-9c68-99cf60081585
-- title:
--   Mod Eval Ser
-- statement:
--   Definitions and structural lemmas for Mod Eval Ser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
theorem natMul_injective {k : ℕ} (hk : k ≠ 0) : Function.Injective (fun m : ℕ => k * m) := fun _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h
theorem Conv.xp {f : PowerSeries ℂ} (hf : Conv f) {k : ℕ} (hk : k ≠ 0) : Conv (xp k f) := by
  intro x hx
  have hxk : ‖x ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx hk
  have hz : ∀ n ∉ Set.range (fun m : ℕ => k * m),
      ‖PowerSeries.coeff n (ReciprocityTheory.ChartRestriction.L1.xp k f)‖ * ‖x‖ ^ n = 0 := by
    intro n hn
    have hkn : ¬ k ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
    rw [ReciprocityTheory.ChartRestriction.L1.xp, PowerSeries.coeff_mk, if_neg hkn, norm_zero, zero_mul]
  refine ((natMul_injective hk).summable_iff hz).mp ?_
  refine (hf (x ^ k) hxk).congr fun m => ?_
  show ‖PowerSeries.coeff m f‖ * ‖x ^ k‖ ^ m =
    ‖PowerSeries.coeff (k * m) (ReciprocityTheory.ChartRestriction.L1.xp k f)‖ * ‖x‖ ^ (k * m)
  rw [ReciprocityTheory.ChartRestriction.L1.xp, PowerSeries.coeff_mk, if_pos (dvd_mul_right k m),
    Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hk), norm_pow, pow_mul]
theorem Conv.rescale {f : PowerSeries ℂ} (hf : Conv f) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Conv (PowerSeries.rescale c f) := by
  intro x hx
  have hcx : ‖c * x‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
      _ < 1 := by rw [one_mul]; exact hx
  refine (hf (c * x) hcx).congr fun n => ?_
  simp only [PowerSeries.coeff_rescale, norm_mul, norm_pow, mul_pow]
  ring
theorem Conv.sub1 {f : PowerSeries ℂ} (hf : Conv f) {c : ℂ} (hc : ‖c‖ ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    Conv (sub1 c k f) := (hf.rescale hc).xp hk
end ReciprocityTheory.ChartRestriction.L1


