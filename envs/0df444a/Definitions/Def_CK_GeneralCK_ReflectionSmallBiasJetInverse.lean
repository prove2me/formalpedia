-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetInverse
-- name    : CK_GeneralCK_ReflectionSmallBiasJetInverse
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:42:44.75618+00:00
-- url     : https://prove2.me/theorems/3c09e51c-df5b-4ef7-85d4-46d877cda194
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasJetInverse` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasJetInverse` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasJetInverse` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasJetInverse (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasJetInverse.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetConstructors

-- ===== source module GeneralCK.ReflectionSmallBiasJetInverse =====
section

/-! # The geometric-series remainder for Taylor-jet inversion -/

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem inverse_one_sub {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hf : Approximates n k f p) (hzero : f 0 = 0) :
    Approximates n k (fun z => (1 - f z)⁻¹) (SmallBiasPolynomial.geometric n p) := by
  have ha : AnalyticAt ℂ (fun z => (1 - f z)⁻¹) 0 :=
    (analyticAt_const.sub hf.analytic).inv (by simp [hzero])
  have hb : (fun z => (1 - f z)⁻¹) =O[𝓝 (0 : ℂ × ℂ)] (fun _ => (1 : ℝ)) :=
    ha.continuousAt.tendsto.isBigO_one ℝ
  have hp := (hf.function_isBigO_norm hzero).pow n
  have he : (fun z => f z ^ n * (1 - f z)⁻¹)
      =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖ ^ n) := by
    simpa only [mul_one] using hp.mul hb
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), 1 - f z ≠ 0 :=
    (continuousAt_const.sub hf.analytic.continuousAt).eventually_ne (by simp [hzero])
  have heq : (fun z => f z ^ n * (1 - f z)⁻¹) =ᶠ[𝓝 (0 : ℂ × ℂ)]
      (fun z => (1 - f z)⁻¹ - ∑ j ∈ Finset.range n, f z ^ j) := by
    filter_upwards [hne] with z hz
    calc
      _ = (1 - (∑ j ∈ Finset.range n, f z ^ j) * (1 - f z)) / (1 - f z) := by
        rw [geom_sum_mul_neg]
        ring
      _ = (1 - f z)⁻¹ - ∑ j ∈ Finset.range n, f z ^ j := by
        field_simp [hz]
  exact (hf.geometric hk).transfer ha (he.congr' heq Filter.EventuallyEq.rfl)

end GeneralCK.Reflection.SmallBiasJet.Approximates

end


