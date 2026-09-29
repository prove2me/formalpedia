-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCurvatureAssembly
-- name    : CK_GeneralCK_ReflectionSmallBiasCurvatureAssembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:28:28.196157+00:00
-- url     : https://prove2.me/theorems/662170b3-e7a1-43d9-bc12-afe753e3fb13
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasCurvatureAssembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasCurvatureAssembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasCurvatureAssembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasCurvatureAssembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasCurvatureAssembly.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCandidateCurvature
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasRemainderCurvature
import Mathlib.Analysis.Complex.RealDeriv

-- ===== source module GeneralCK.ReflectionSmallBiasCurvatureAssembly =====
section

/-! Assembly of the quantitative curvature estimate from an order-24 identity. -/

namespace GeneralCK.Reflection.SmallBiasPartialCauchy

open Filter
open scoped Topology

theorem partialA_sub {f g : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) :
    partialA (fun z => f z-g z) p = partialA f p-partialA g p := by
  unfold partialA
  change (fderiv ℂ (f-g) p) (1,0) = (fderiv ℂ f p) (1,0)-(fderiv ℂ g p) (1,0)
  rw [fderiv_sub hf.differentiableAt hg.differentiableAt]
  rfl

theorem partialAA_sub {f g : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) :
    partialAA (fun z => f z-g z) p = partialAA f p-partialAA g p := by
  have he : partialA (fun z => f z-g z) =ᶠ[𝓝 p] (fun z => partialA f z-partialA g z) := by
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hz hz'
    exact partialA_sub hz hz'
  change fderiv ℂ (partialA (fun z => f z-g z)) p (1,0) = _
  rw [he.fderiv_eq]
  exact partialA_sub (analyticAt_partialA hf) (analyticAt_partialA hg)

theorem deriv2_restriction {f : ℂ × ℂ → ℂ} {a b : ℝ}
    (hf : AnalyticAt ℂ f ((a:ℂ),(b:ℂ))) :
    deriv (deriv (fun x : ℝ => (f ((x:ℂ),(b:ℂ))).re)) a =
      (partialAA f ((a:ℂ),(b:ℂ))).re := by
  have hp : Tendsto (fun x : ℝ => ((x:ℂ),(b:ℂ))) (𝓝 a) (𝓝 ((a:ℂ),(b:ℂ))) :=
    (Complex.continuous_ofReal.prodMk continuous_const).tendsto a
  have he : deriv (fun x : ℝ => (f ((x:ℂ),(b:ℂ))).re) =ᶠ[𝓝 a]
      (fun x : ℝ => (partialA f ((x:ℂ),(b:ℂ))).re) := by
    filter_upwards [hp.eventually hf.eventually_analyticAt] with x hx
    exact (hasDerivAt_sliceA hx).real_of_complex.deriv
  rw [he.deriv_eq]
  exact (hasDerivAt_sliceA (analyticAt_partialA hf)).real_of_complex.deriv

end GeneralCK.Reflection.SmallBiasPartialCauchy

namespace GeneralCK.Reflection.SmallBiasCurvatureAssembly

open Filter Asymptotics SmallBiasPartialCauchy
open scoped Topology

noncomputable def complexDifference (z : ℂ × ℂ) : ℂ :=
  SmallBiasComplexDomain.difference z.1 z.2

noncomputable def remainder (z : ℂ × ℂ) : ℂ :=
  complexDifference z-SmallBiasCandidate.polynomial z

theorem analyticAt_complexDifference {z : ℂ × ℂ} (hz : ‖z‖ ≤ (21/50:ℝ)) :
    AnalyticAt ℂ complexDifference z :=
  SmallBiasComplexDomain.analyticAt_difference ((norm_fst_le z).trans hz) ((norm_snd_le z).trans hz)

theorem analyticAt_remainder {z : ℂ × ℂ} (hz : ‖z‖ ≤ (21/50:ℝ)) :
    AnalyticAt ℂ remainder z :=
  (analyticAt_complexDifference hz).sub (SmallBiasCandidate.analyticAt_polynomial z)

theorem norm_remainder_le {z : ℂ × ℂ} (hz : ‖z‖ ≤ (21/50:ℝ)) : ‖remainder z‖ ≤ 4 := by
  have ha := (norm_fst_le z).trans hz
  have hb := (norm_snd_le z).trans hz
  have hd := SmallBiasComplexDomain.norm_difference_le ha hb
  have hp := SmallBiasCandidate.norm_polynomial_le_one ha hb
  change ‖complexDifference z‖ ≤ 3 at hd
  exact (norm_sub_le _ _).trans (by linarith)

theorem remainder_axis (a : ℂ) : remainder (a,0) = 0 := by
  simp [remainder,complexDifference,SmallBiasComplexDomain.difference,SmallBiasComplexDomain.atanhExt]

theorem curvature_nonneg_of_order24
    (horder : remainder =O[𝓝 0] (fun z : ℂ × ℂ => ‖z‖^24))
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha1 : a ≤ 3/20) :
    0 ≤ deriv (deriv (fun x : ℝ => (complexDifference ((x:ℂ),(b:ℂ))).re)) a := by
  have ha : 0 < a := hb.trans hba
  have hz : ‖((a:ℂ),(b:ℂ))‖ ≤ (21/50:ℝ) := by
    simp only [Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,abs_of_pos hb]
    exact (max_le le_rfl hba.le).trans (by linarith)
  have hd := analyticAt_complexDifference hz
  have hp := SmallBiasCandidate.analyticAt_polynomial ((a:ℂ),(b:ℂ))
  have herr := SmallBiasRemainder.remainder_curvature_bound
    (fun z hz => analyticAt_remainder hz) (fun z hz => norm_remainder_le hz)
    remainder_axis horder ha hb hba.le ha1
  have hreal : (partialAA SmallBiasCandidate.polynomial ((a:ℂ),(b:ℂ))).re =
      deriv (deriv (fun x => SmallBiasCandidate.realPolynomial x b)) a := by
    rw [← deriv2_restriction hp]
    have he : (fun x : ℝ => (SmallBiasCandidate.polynomial ((x:ℂ),(b:ℂ))).re) =
        (fun x => SmallBiasCandidate.realPolynomial x b) := by
      funext x
      rw [← SmallBiasCandidate.realPolynomial_cast]
      rfl
    rw [he]
  have hdiff : (partialAA remainder ((a:ℂ),(b:ℂ))).re =
      deriv (deriv (fun x : ℝ => (complexDifference ((x:ℂ),(b:ℂ))).re)) a -
      deriv (deriv (fun x => SmallBiasCandidate.realPolynomial x b)) a := by
    rw [show partialAA remainder ((a:ℂ),(b:ℂ)) =
      partialAA complexDifference ((a:ℂ),(b:ℂ))-
      partialAA SmallBiasCandidate.polynomial ((a:ℂ),(b:ℂ)) from partialAA_sub hd hp]
    rw [Complex.sub_re,← deriv2_restriction hd,hreal]
  have herror := (Complex.abs_re_le_norm (partialAA remainder ((a:ℂ),(b:ℂ)))).trans_lt herr
  rw [hdiff] at herror
  have hlower := SmallBiasCandidate.realPolynomial_curvature_lower ha hb hba.le
  have hpos : 0 < a^3*b := by positivity
  have he := (abs_lt.mp herror).1
  nlinarith

end GeneralCK.Reflection.SmallBiasCurvatureAssembly


end


