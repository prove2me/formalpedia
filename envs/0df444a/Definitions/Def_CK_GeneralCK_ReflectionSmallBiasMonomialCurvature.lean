-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasMonomialCurvature
-- name    : CK_GeneralCK_ReflectionSmallBiasMonomialCurvature
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T13:19:56.337707+00:00
-- url     : https://prove2.me/theorems/d2e53deb-808b-47a6-bee5-5332fb7b5bc8
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasMonomialCurvature` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasMonomialCurvature` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasMonomialCurvature` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasMonomialCurvature (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasMonomialCurvature.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCandidate

-- ===== source module GeneralCK.ReflectionSmallBiasMonomialCurvature =====
section

/-! Positive second derivatives of every factored candidate monomial. -/

namespace GeneralCK.Reflection.SmallBiasCandidate

noncomputable def base (b x : ℝ) : ℝ := x * (x^2-b^2)^2
noncomputable def baseFirst (b x : ℝ) : ℝ := (x^2-b^2)*(5*x^2-b^2)
noncomputable def baseSecond (b x : ℝ) : ℝ := 20*x^3-12*x*b^2

theorem hasDerivAt_base (b x : ℝ) : HasDerivAt (base b) (baseFirst b x) x := by
  convert! (hasDerivAt_id x).mul ((((hasDerivAt_id x).pow 2).sub_const (b^2)).pow 2) using 1
  dsimp [baseFirst]; ring

theorem hasDerivAt_baseFirst (b x : ℝ) : HasDerivAt (baseFirst b) (baseSecond b x) x := by
  convert! (((hasDerivAt_id x).pow 2).sub_const (b^2)).mul
    ((((hasDerivAt_id x).pow 2).const_mul 5).sub_const (b^2)) using 1
  dsimp [baseSecond]; ring

noncomputable def weightedBase (m : ℕ) (b x : ℝ) : ℝ := x^m * base b x

noncomputable def weightedFirst (m : ℕ) (b x : ℝ) : ℝ :=
  (m:ℝ)*x^(m-1)*base b x + x^m*baseFirst b x

noncomputable def weightedSecond (m : ℕ) (b x : ℝ) : ℝ :=
  (m:ℝ)*((m-1:ℕ):ℝ)*x^(m-1-1)*base b x +
    2*(m:ℝ)*x^(m-1)*baseFirst b x + x^m*baseSecond b x

theorem hasDerivAt_weightedBase (m : ℕ) (b x : ℝ) :
    HasDerivAt (weightedBase m b) (weightedFirst m b x) x := by
  convert! ((hasDerivAt_id x).pow m).mul (hasDerivAt_base b x) using 1
  dsimp [weightedFirst]; ring

theorem hasDerivAt_weightedFirst (m : ℕ) (b x : ℝ) :
    HasDerivAt (weightedFirst m b) (weightedSecond m b x) x := by
  have hp := (((hasDerivAt_id x).pow (m-1)).const_mul (m:ℝ)).mul (hasDerivAt_base b x)
  have hq := ((hasDerivAt_id x).pow m).mul (hasDerivAt_baseFirst b x)
  convert! hp.add hq using 1
  dsimp [weightedSecond]; ring

theorem deriv_weightedBase (m : ℕ) (b : ℝ) :
    deriv (weightedBase m b) = weightedFirst m b :=
  funext (fun x => (hasDerivAt_weightedBase m b x).deriv)

theorem deriv2_weightedBase (m : ℕ) (b x : ℝ) :
    deriv (deriv (weightedBase m b)) x = weightedSecond m b x := by
  rw [deriv_weightedBase]
  exact (hasDerivAt_weightedFirst m b x).deriv

theorem weightedSecond_lower (m : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    8*a^(m+3) ≤ weightedSecond m b a := by
  have hsq : 0 ≤ a^2-b^2 := by nlinarith
  have hb0 : 0 ≤ base b a := by unfold base; positivity
  have hb1 : 0 ≤ baseFirst b a := by
    unfold baseFirst
    exact mul_nonneg hsq (by nlinarith)
  have hb2 : 8*a^3 ≤ baseSecond b a := by
    have hh := mul_nonneg ha.le hsq
    unfold baseSecond
    nlinarith
  have hleft : 0 ≤ (m:ℝ)*((m-1:ℕ):ℝ)*a^(m-1-1)*base b a := by positivity
  have hmiddle : 0 ≤ 2*(m:ℝ)*a^(m-1)*baseFirst b a := by positivity
  have hright := mul_le_mul_of_nonneg_left hb2 (pow_nonneg ha.le m)
  unfold weightedSecond
  rw [pow_add]
  nlinarith

theorem weightedSecond_nonneg (m : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    0 ≤ weightedSecond m b a :=
  (by positivity : (0:ℝ) ≤ 8*a^(m+3)).trans (weightedSecond_lower m ha hb hba)

end GeneralCK.Reflection.SmallBiasCandidate

end


