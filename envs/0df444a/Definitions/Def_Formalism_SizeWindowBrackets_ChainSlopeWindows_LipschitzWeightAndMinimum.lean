-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:41.393295+00:00
-- url     : https://prove2.me/theorems/83fc2072-234c-4676-889e-2c9a955901c5
-- title:
--   Lipschitz Weight And Minimum
-- statement:
--   Definitions and structural lemmas for Lipschitz Weight And Minimum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
namespace SZ
lemma T2 {x Y m nT aE b k : ℝ} (hx0 : 0 < x) (hY1 : 1 ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hk0 : 0 < k) (hk1 : x * m ≤ k) (haE : aE ≤ 2 * x * b) :
    nT * aE * (m ^ 2 / k) ≤ 2 * Y * (nT * m * b) := by
  have hmk : m ^ 2 / k ≤ m / x := by
    rw [div_le_div_iff₀ hk0 hx0]; nlinarith
  have h1 : nT * aE * (m ^ 2 / k) ≤ nT * (2 * x * b) * (m / x) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haE hnT0) hmk (by positivity) (by positivity)
  have h2 : nT * (2 * x * b) * (m / x) = 2 * (nT * m * b) := by field_simp
  have hQ : 0 ≤ nT * m * b := by positivity
  have h3 : 2 * (nT * m * b) ≤ 2 * Y * (nT * m * b) := by nlinarith
  linarith
end SZ
namespace CR
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
lemma primVal_zero (D : ArithData H) (n : ℕ) : primVal D 0 n = 1 := by
  classical
  unfold primVal
  apply Finset.prod_eq_one
  intro p _
  unfold cosetMean
  simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  apply div_self
  have h0 : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ D.inertia p) := by
    simp
  have := Finset.card_pos.2 ⟨0, h0⟩
  exact_mod_cast this.ne'
lemma chC_apply' (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) g = ((sgn2 g.1.1 : ℝ) : ℂ) := by
  show (if g.1.1 = 0 then (1 : ℂ) else -1) = _
  unfold sgn2; split_ifs <;> simp
lemma psC_apply' (g : E0 × H) : (psC : AddChar (E0 × H) ℂ) g = ((sgn2 g.1.2 : ℝ) : ℂ) := by
  show (if g.1.2 = 0 then (1 : ℂ) else -1) = _
  unfold sgn2; split_ifs <;> simp
lemma chpsC_apply' (g : E0 × H) :
    (chpsC : AddChar (E0 × H) ℂ) g = ((sgn2 g.1.1 * sgn2 g.1.2 : ℝ) : ℂ) := by
  unfold chpsC; rw [AddChar.mul_apply, chC_apply', psC_apply']; push_cast; ring
def host (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) : CycHost H where
  cv := primVal D
  cv_zero := primVal_zero D
  ell := ell
  chC := chC
  psC := psC
  chpsC := chpsC
  chC_apply := chC_apply'
  psC_apply := psC_apply'
  chpsC_apply := chpsC_apply'
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def wR {m : ℕ} (T2 : Finset H) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) : H → Fin m → E0 × H → ℝ :=
  fun u0 j ρ => if IsThickAt T2 u0 ρ then b else if InPhi ρ then w u0 j ρ else 1
def aR (TT : Finset H) (a : H → ℝ) : H → ℝ := fun t => if t ∈ TT then a t else 1
lemma wR_thick {m : ℕ} (T2 : Finset H) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) (u0 : H) (j : Fin m) (ρ : E0 × H)
    (h : IsThickAt T2 u0 ρ) : wR T2 b w u0 j ρ = b := by unfold wR; rw [if_pos h]
def nodes {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) (hb : 0 < b)
    (ha : ∀ t ∈ TT, 0 < a t) (hw : ∀ u0 j ρ, InPhi ρ → 0 < w u0 j ρ) : Nodes H m where
  T := TT
  T2 := T2
  a := aR TT a
  bj := fun _ => b
  w := wR T2 b w
  w_thick := fun u0 j t ht => wR_thick T2 b w u0 j _ (Finset.mem_image_of_mem _ ht)
  w_pos := fun u0 j ρ => by
    unfold wR; split_ifs with h1 h2
    · exact hb
    · exact hw u0 j ρ h2
    · exact one_pos
  a_pos := fun t => by
    unfold aR; split_ifs with h
    · exact ha t h
    · exact one_pos
end
end CR
namespace AN
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
end AN
namespace AN
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
end AN
end Formalism.LFunctionChainParameters.ThickSetMeanBounds


