-- Prove2me | Definitions.Def_OAIQ032L033
-- name    : OAIQ032L033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:57:58.134182+00:00
-- url     : https://prove2.me/theorems/b03b0698-2d15-4470-8773-827e3a7a29ad
-- title:
--   Definitions bundle OAIQ032L033 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_RootTwist`.
--
--   **Imports.** It imports the bundles `OAIQ032L030` and `OAIQ032L031` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L034`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L030
import Definitions.Def_OAIQ032L031

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTwist
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma grid_power_mem (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) (hx : x ∈ grid R n m s t) (N : ℕ) :
    x^N ∈ grid R n (N • m) s t := by
  induction N with
  | zero => simpa only [pow_zero,zero_smul] using grid_one_mem R n s t
  | succ N ih =>
      simpa only [pow_succ,succ_nsmul] using grid_mul_mem R n (N • m) m s t _ _ ih hx

lemma coefficient_zpow_grid_mem (k : Fin (n+1)) (s : Finset (Fin (n+1)))
    (hk : k ∈ s) (t : Finset (Chart n)) (a : ℤ) :
    ((targetUnit R n k)^a : (GridAmbient R n)ˣ).val ∈ grid R n (fun _ => a) s t := by
  cases a with
  | ofNat N =>
      have hp := grid_power_mem R n (fun _ => 1) s t _ (coefficient_grid_mem R n k s t) N
      change (↑(targetUnit R n k) ^ N : GridAmbient R n) ∈ _
      simpa only [Pi.smul_def,nsmul_eq_mul,mul_one,Int.ofNat_eq_natCast] using hp
  | negSucc N =>
      have hp := grid_power_mem R n (fun _ => -1) s t _
        (coefficient_inverse_grid_mem R n k s hk t) (N+1)
      have he : (N+1) • (fun _ : Fin n => (-1:ℤ)) = fun _ => Int.negSucc N := by
        ext i
        simp only [Pi.smul_apply,nsmul_eq_mul,mul_neg_one]
        omega
      rw [he] at hp
      change (↑(((targetUnit R n k)⁻¹) ^ (N+1)) : GridAmbient R n) ∈ _
      simpa only [Units.val_pow_eq_pow_val] using hp

variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s) (hs : s.Nonempty)
variable (m l : Fin n → ℤ) (a : ℤ) (hml : ∀ j, l j = m j + a)

include hk hml in
lemma twist_mem (x : GridAmbient R n) (hx : x ∈ grid R n m s ∅) :
    (↑((targetUnit R n k)^a) : GridAmbient R n) * x ∈ grid R n l s ∅ := by
  have he : (fun _ : Fin n => a) + m = l := by ext j; simp only [Pi.add_apply,hml]; ring
  rw [←he]
  exact grid_mul_mem R n _ m s ∅ _ x (coefficient_zpow_grid_mem R n k s hk ∅ a) hx



end Lech.ProjectiveRoot

end

end OAI
end


