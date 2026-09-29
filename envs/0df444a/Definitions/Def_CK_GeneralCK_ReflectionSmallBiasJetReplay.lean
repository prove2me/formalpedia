-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetReplay
-- name    : CK_GeneralCK_ReflectionSmallBiasJetReplay
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:58:36.273611+00:00
-- url     : https://prove2.me/theorems/8ec05673-10b1-4bb1-9aff-d8b5dd0f1761
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasJetReplay` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasJetReplay` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasJetReplay` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasJetReplay (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasJetReplay.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCompactFunctions

-- ===== source module GeneralCK.ReflectionSmallBiasJetReplay =====
section

/-! Composition with a separately checked finite polynomial computation. -/

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem comp_finite {n : ℕ} {k : ℂ} {f g h : ℂ × ℂ → ℂ}
    {p q ts result : List Term}
    (hg : Approximates n k g p) (hh : Approximates n k h q)
    (hg0 : g 0 = 0) (hh0 : h 0 = 0) (hf : Approximates n k f ts)
    (ht : Approximates n k (fun z => eval k ts (g z,h z)) result) :
    Approximates n k (fun z => f (g z,h z)) result := by
  have hprod : AnalyticAt ℂ (fun z => (g z,h z)) 0 := hg.analytic.prod hh.analytic
  have hz : (g 0,h 0) = (0 : ℂ × ℂ) := by simp only [hg0,hh0]; rfl
  have hT : Tendsto (fun z => (g z,h z)) (𝓝 (0 : ℂ × ℂ)) (𝓝 0) := by
    simpa only [hz] using hprod.continuousAt.tendsto
  have hnorm : (fun z => (g z,h z)) =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖) := by
    simpa only [hz,sub_zero] using hprod.differentiableAt.isBigO_sub.norm_right
  exact ht.transfer (hf.analytic.comp_of_eq hprod hz)
    ((hf.error.comp_tendsto hT).trans (hnorm.norm_left.pow n))

theorem entropy_of_finite {k : ℂ} {f : ℂ × ℂ → ℂ} {p q : List Term}
    (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ))
    (hf : Approximates 24 k f p) (hzero : f 0 = 0)
    (ht : Approximates 24 k (fun z => eval k entropySeed (f z,0)) q) :
    Approximates 24 k (fun z => ComplexEntropy.entropyExt (f z)) q := by
  have hs := ((coordinateA 24 k).entropy hk hklog (by rfl)).replacePolynomial
    (equalityCheck_sound entropySeed_checked k)
  simpa only [Rat.cast_zero] using hf.comp_finite (const 24 k 0) hzero (by simp) hs ht

theorem atanh_of_finite {k : ℂ} {f : ℂ × ℂ → ℂ} {p q : List Term}
    (hk : k ≠ 0) (hf : Approximates 24 k f p) (hzero : f 0 = 0)
    (ht : Approximates 24 k (fun z => eval k atanhSeed (f z,0)) q) :
    Approximates 24 k (fun z => SmallBiasComplexDomain.atanhExt (f z)) q := by
  have hs := ((coordinateA 24 k).atanh hk (by rfl)).replacePolynomial
    (equalityCheck_sound atanhSeed_checked k)
  simpa only [Rat.cast_zero] using hf.comp_finite (const 24 k 0) hzero (by simp) hs ht

end GeneralCK.Reflection.SmallBiasJet.Approximates

end


