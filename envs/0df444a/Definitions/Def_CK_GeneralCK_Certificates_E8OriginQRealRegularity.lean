-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginQRealRegularity
-- name    : CK_GeneralCK_Certificates_E8OriginQRealRegularity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:24:40.613613+00:00
-- url     : https://prove2.me/theorems/5ad8326a-8eb6-4bfb-8321-e1c641a14876
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginQRealRegularity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginQRealRegularity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginQRealRegularity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginQRealRegularity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginQRealRegularity.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedDerivativeConsumer

-- ===== source module GeneralCK.Certificates.E8OriginQRealRegularity =====
section

/-! Real-axis regularity of the quantitative E8 inverse branch. -/

namespace GeneralCK.Certificates.E8OriginQRealRegularity

open Metric Set
open E8QuantitativeBranchBridge
open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer

theorem qReal_contDiffAt (cert : QuantitativeCertificate) {y : ℝ}
    (hy : abs y < yOuterRadius) : ContDiffAt ℝ ⊤ (qReal cert) y := by
  have hy' : (y : ℂ) ∈ ball (0 : ℂ) yOuterRadius := by
    simpa [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hy
  have hq : ContDiffAt ℂ ⊤ (qDisc cert.inverse) (y : ℂ) :=
    (((qDisc_diffCont cert.inverse).differentiableOn.contDiffOn isOpen_ball)
      (y : ℂ) hy').contDiffAt (isOpen_ball.mem_nhds hy')
  have hof : ContDiffAt ℝ ⊤ (⇑Complex.ofRealCLM) y :=
    (Complex.ofRealCLM.contDiff (n := ⊤)).contDiffAt
  have hcomp : ContDiffAt ℝ ⊤
      (qDisc cert.inverse ∘ (⇑Complex.ofRealCLM)) y :=
    (hq.restrict_scalars ℝ).comp y hof
  have hre : ContDiffAt ℝ ⊤
      ((⇑Complex.reCLM) ∘ qDisc cert.inverse ∘ (⇑Complex.ofRealCLM)) y :=
    (Complex.reCLM.contDiff (n := ⊤)).contDiffAt.comp y hcomp
  have heq : qReal cert =
      ((⇑Complex.reCLM) ∘ qDisc cert.inverse ∘ (⇑Complex.ofRealCLM)) := by
    funext x
    simp only [qReal, Function.comp_apply, Complex.ofRealCLM_apply,
      Complex.reCLM_apply]
  rw [heq]
  exact hre

theorem qReal_differentiableAt (cert : QuantitativeCertificate) {y : ℝ}
    (hy : abs y < yOuterRadius) : DifferentiableAt ℝ (qReal cert) y :=
  (qReal_contDiffAt cert hy).differentiableAt (by simp)

theorem qReal_contDiffAt_on_origin_inputs (cert : QuantitativeCertificate)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 2 / 25) :
    And (ContDiffAt ℝ ⊤ (qReal cert) s)
      (And (ContDiffAt ℝ ⊤ (qReal cert) t)
        (And (ContDiffAt ℝ ⊤ (qReal cert) (s + t))
          (ContDiffAt ℝ ⊤ (qReal cert) (2 * s + t)))) := by
  have hs' : |s| < yOuterRadius := by
    rw [abs_of_nonneg hs]
    have : s ≤ 2 / 25 := by linarith
    exact this.trans_lt (by norm_num [yOuterRadius])
  have ht' : |t| < yOuterRadius := by
    rw [abs_of_nonneg ht]
    have : t ≤ 2 / 25 := by linarith
    exact this.trans_lt (by norm_num [yOuterRadius])
  have hst' : |s + t| < yOuterRadius := by
    rw [abs_of_nonneg (add_nonneg hs ht)]
    exact hst.trans_lt (by norm_num [yOuterRadius])
  have h2st : 2 * s + t ≤ 4 / 25 := by linarith
  have h2st' : |2 * s + t| < yOuterRadius := by
    rw [abs_of_nonneg (by linarith)]
    exact h2st.trans_lt (by norm_num [yOuterRadius])
  exact ⟨qReal_contDiffAt cert hs', qReal_contDiffAt cert ht',
    qReal_contDiffAt cert hst', qReal_contDiffAt cert h2st'⟩

theorem e8Delta_left_contDiffAt {Q : ℝ → ℝ} {s t : ℝ}
    (hB : ContDiffAt ℝ ⊤ Q (2 * s + t))
    (hC : ContDiffAt ℝ ⊤ Q (s + t))
    (hD : ContDiffAt ℝ ⊤ Q s) :
    ContDiffAt ℝ ⊤ (fun u => e8Delta Q u t) s := by
  unfold e8Delta
  fun_prop

private noncomputable def partialS₂ (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => F (u, p.2)) p.1

private noncomputable def partialT₂ (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun v => F (p.1, v)) p.2

private theorem partialS₂_contDiffAt {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : ContDiffAt ℝ ⊤ F p) : ContDiffAt ℝ ⊤ (partialS₂ F) p := by
  have hf : ContDiffAt ℝ ⊤
      (Function.uncurry (fun r : ℝ × ℝ => fun u : ℝ => F (u, r.2)))
        (p, p.1) := by
    fun_prop
  have hg : ContDiffAt ℝ ⊤ (fun r : ℝ × ℝ => r.1) p := by fun_prop
  have hd : ContDiffAt ℝ ⊤
      (fun r : ℝ × ℝ => fderiv ℝ (fun u : ℝ => F (u, r.2)) r.1) p :=
    hf.fderiv hg (by simp)
  unfold partialS₂
  simpa only [← fderiv_apply_one_eq_deriv] using
    hd.clm_apply (by fun_prop : ContDiffAt ℝ ⊤ (fun _ : ℝ × ℝ => (1 : ℝ)) p)

private theorem partialT₂_contDiffAt {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : ContDiffAt ℝ ⊤ F p) : ContDiffAt ℝ ⊤ (partialT₂ F) p := by
  have hf : ContDiffAt ℝ ⊤
      (Function.uncurry (fun r : ℝ × ℝ => fun v : ℝ => F (r.1, v)))
        (p, p.2) := by
    fun_prop
  have hg : ContDiffAt ℝ ⊤ (fun r : ℝ × ℝ => r.2) p := by fun_prop
  have hd : ContDiffAt ℝ ⊤
      (fun r : ℝ × ℝ => fderiv ℝ (fun v : ℝ => F (r.1, v)) r.2) p :=
    hf.fderiv hg (by simp)
  unfold partialT₂
  simpa only [← fderiv_apply_one_eq_deriv] using
    hd.clm_apply (by fun_prop : ContDiffAt ℝ ⊤ (fun _ : ℝ × ℝ => (1 : ℝ)) p)

private noncomputable def delta₂ (Q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  e8Delta Q p.1 p.2

private theorem delta₂_contDiffAt {Q : ℝ → ℝ} {s t : ℝ}
    (hB : ContDiffAt ℝ ⊤ Q (2 * s + t))
    (hC : ContDiffAt ℝ ⊤ Q (s + t))
    (hD : ContDiffAt ℝ ⊤ Q s)
    (hA : ContDiffAt ℝ ⊤ Q t) :
    ContDiffAt ℝ ⊤ (delta₂ Q) (s, t) := by
  unfold delta₂ e8Delta
  fun_prop

private theorem deltaS₂_eq (Q : ℝ → ℝ) :
    (fun p : ℝ × ℝ => deltaS Q p.1 p.2) = partialS₂ (delta₂ Q) := by
  rfl

private theorem deltaSS₂_eq (Q : ℝ → ℝ) :
    (fun p : ℝ × ℝ => deltaSS Q p.1 p.2) =
      partialS₂ (partialS₂ (delta₂ Q)) := by
  rfl

theorem deltaS_pair_contDiffAt {Q : ℝ → ℝ} {s t : ℝ}
    (hB : ContDiffAt ℝ ⊤ Q (2 * s + t))
    (hC : ContDiffAt ℝ ⊤ Q (s + t))
    (hD : ContDiffAt ℝ ⊤ Q s)
    (hA : ContDiffAt ℝ ⊤ Q t) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => deltaS Q p.1 p.2) (s, t) := by
  rw [deltaS₂_eq]
  exact partialS₂_contDiffAt (delta₂_contDiffAt hB hC hD hA)

theorem deltaSS_pair_contDiffAt {Q : ℝ → ℝ} {s t : ℝ}
    (hB : ContDiffAt ℝ ⊤ Q (2 * s + t))
    (hC : ContDiffAt ℝ ⊤ Q (s + t))
    (hD : ContDiffAt ℝ ⊤ Q s)
    (hA : ContDiffAt ℝ ⊤ Q t) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => deltaSS Q p.1 p.2) (s, t) := by
  rw [deltaSS₂_eq]
  exact partialS₂_contDiffAt
    (partialS₂_contDiffAt (delta₂_contDiffAt hB hC hD hA))

/-- The exact axis identities and first differentiation step required by
the origin integration argument. -/
structure AxisRegularity (Q : ℝ → ℝ) (R : ℝ) : Prop where
  delta_zero_left : ∀ t, 0 ≤ t → t ≤ R → e8Delta Q 0 t = 0
  deltaS_zero_left : ∀ t, 0 ≤ t → t ≤ R → deltaS Q 0 t = 0
  deltaSS_zero_right : ∀ s, 0 ≤ s → s ≤ R → deltaSS Q s 0 = 0
  hasDeriv_delta : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
    HasDerivAt (fun u => e8Delta Q u t) (deltaS Q s t) s

theorem qReal_axisRegularity (cert : QuantitativeCertificate) :
    AxisRegularity (qReal cert) (2 / 25 : ℝ) := by
  have hzero : qReal cert 0 = 0 := qReal_zero cert
  refine
    { delta_zero_left := ?_
      deltaS_zero_left := ?_
      deltaSS_zero_right := ?_
      hasDeriv_delta := ?_ }
  · intro t _ _
    exact delta_zero_left_of_zero hzero t
  · intro t ht htR
    apply deltaS_zero_left_of_zero hzero t
    · apply qReal_differentiableAt cert
      rw [abs_of_nonneg ht]
      exact htR.trans_lt (by norm_num [yOuterRadius])
    · apply qReal_differentiableAt cert
      norm_num [yOuterRadius]
  · intro s _ _
    exact deltaSS_zero_right_of_zero hzero s
  · intro s t hs ht hst
    rcases qReal_contDiffAt_on_origin_inputs cert hs ht hst with
      ⟨hsQ, htQ, hstQ, h2stQ⟩
    have hd := e8Delta_left_contDiffAt h2stQ hstQ hsQ
    change HasDerivAt (fun u => e8Delta (qReal cert) u t)
      (deriv (fun u => e8Delta (qReal cert) u t) s) s
    exact (hd.differentiableAt (by simp)).hasDerivAt

theorem qReal_hasDeriv_deltaS (cert : QuantitativeCertificate) :
    ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ (2 / 25 : ℝ) →
      HasDerivAt (fun u => deltaS (qReal cert) u t)
        (deltaSS (qReal cert) s t) s := by
  intro s t hs ht hst
  rcases qReal_contDiffAt_on_origin_inputs cert hs ht hst with
    ⟨hsQ, htQ, hstQ, h2stQ⟩
  have hp := deltaS_pair_contDiffAt h2stQ hstQ hsQ htQ
  have ha : ContDiffAt ℝ ⊤ (fun u : ℝ => (u, t)) s := by fun_prop
  have hc' := hp.comp s ha
  have hc : ContDiffAt ℝ ⊤ (fun u => deltaS (qReal cert) u t) s := by
    have heq : (fun u => deltaS (qReal cert) u t) =
        (fun p : ℝ × ℝ => deltaS (qReal cert) p.1 p.2) ∘ fun u => (u, t) := by
      rfl
    rw [heq]
    exact hc'
  change HasDerivAt (fun u => deltaS (qReal cert) u t)
    (deriv (fun u => deltaS (qReal cert) u t) s) s
  exact (hc.differentiableAt (by simp)).hasDerivAt

theorem qReal_hasDeriv_deltaSS (cert : QuantitativeCertificate) :
    ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ (2 / 25 : ℝ) →
      HasDerivAt (fun v => deltaSS (qReal cert) s v)
        (deltaSST (qReal cert) s t) t := by
  intro s t hs ht hst
  rcases qReal_contDiffAt_on_origin_inputs cert hs ht hst with
    ⟨hsQ, htQ, hstQ, h2stQ⟩
  have hp := deltaSS_pair_contDiffAt h2stQ hstQ hsQ htQ
  have ha : ContDiffAt ℝ ⊤ (fun v : ℝ => (s, v)) t := by fun_prop
  have hc' := hp.comp t ha
  have hc : ContDiffAt ℝ ⊤ (fun v => deltaSS (qReal cert) s v) t := by
    have heq : (fun v => deltaSS (qReal cert) s v) =
        (fun p : ℝ × ℝ => deltaSS (qReal cert) p.1 p.2) ∘ fun v => (s, v) := by
      rfl
    rw [heq]
    exact hc'
  change HasDerivAt (fun v => deltaSS (qReal cert) s v)
    (deriv (fun v => deltaSS (qReal cert) s v) t) t
  exact (hc.differentiableAt (by simp)).hasDerivAt

/-- Once the second partial and the mixed lower bound have been replayed,
all exact axis and first-derivative bookkeeping is automatic. -/
theorem mixedDerivativeCertificate_of_remaining
    (cert : QuantitativeCertificate)
    (hDs : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ (2 / 25 : ℝ) →
      HasDerivAt (fun u => deltaS (qReal cert) u t)
        (deltaSS (qReal cert) s t) s)
    (hDss : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ (2 / 25 : ℝ) →
      HasDerivAt (fun v => deltaSS (qReal cert) s v)
        (deltaSST (qReal cert) s t) t)
    (hpos : ∀ s t, 0 ≤ s → 0 < t → s + t ≤ (2 / 25 : ℝ) →
      0 < deltaSST (qReal cert) s t) :
    MixedDerivativeCertificate (qReal cert) (2 / 25 : ℝ) := by
  let haxis := qReal_axisRegularity cert
  exact
    { delta_zero_left := haxis.delta_zero_left
      deltaS_zero_left := haxis.deltaS_zero_left
      deltaSS_zero_right := haxis.deltaSS_zero_right
      hasDeriv_delta := haxis.hasDeriv_delta
      hasDeriv_deltaS := hDs
      hasDeriv_deltaSS := hDss
      mixed_pos := hpos }

/-- All regularity and axis fields of the mixed certificate follow from the
holomorphic inverse branch.  Only the strict numerical mixed-derivative
enclosure remains. -/
theorem mixedDerivativeCertificate_of_mixed_pos
    (cert : QuantitativeCertificate)
    (hpos : ∀ s t, 0 ≤ s → 0 < t → s + t ≤ (2 / 25 : ℝ) →
      0 < deltaSST (qReal cert) s t) :
    MixedDerivativeCertificate (qReal cert) (2 / 25 : ℝ) :=
  mixedDerivativeCertificate_of_remaining cert
    (qReal_hasDeriv_deltaS cert) (qReal_hasDeriv_deltaSS cert) hpos

end GeneralCK.Certificates.E8OriginQRealRegularity

end


