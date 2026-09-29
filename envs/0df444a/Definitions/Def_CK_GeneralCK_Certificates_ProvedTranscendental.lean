-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ProvedTranscendental
-- name    : CK_GeneralCK_Certificates_ProvedTranscendental
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:53:57.911459+00:00
-- url     : https://prove2.me/theorems/934751e1-656f-4c72-923e-5e1361e2f4f1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ProvedTranscendental` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ProvedTranscendental` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ProvedTranscendental` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ProvedTranscendental (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ProvedTranscendental.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicBivariateJetBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

-- ===== source module GeneralCK.Certificates.ProvedTranscendental =====
section

namespace GeneralCK.Certificates.ProvedTranscendental
open DyadicInterval GeneralCK.Reflection GeneralCK.Certificates.Reflection





theorem log_of_endpoints {p : ℕ} {input out : DyadicInterval p}
    (hp : 0 < input.lo)
    (hl : out.Contains (Real.log ((input.lo:ℝ)/(scale p:ℝ))))
    (hu : out.Contains (Real.log ((input.hi:ℝ)/(scale p:ℝ)))) : LogEncloses input out := by
  intro x hx
  have hl' := contains_toReal_iff.mpr hl
  have hu' := contains_toReal_iff.mpr hu
  have hx' := contains_toReal_iff.mpr hx
  have hpos : 0 < input.toReal.lo := toReal_positive_iff.mpr hp
  apply contains_toReal_iff.mp
  exact ⟨hl'.1.trans (Real.log_le_log hpos hx'.1),
    (Real.log_le_log (hpos.trans_le hx'.1) hx'.2).trans hu'.2⟩

theorem jetLog_sound {p : ℕ} {b : DyadicJetEnclosure p} {out : DyadicInterval p}
    {j : Jet2} {t : ℝ} (hb : b.Contains j t) (hp : 0<b.value.lo)
    (hv : out.Contains (Real.log (j.value t))) :
    (DyadicLog.jetLog b out).Contains j.log t := by
  have hr := recip_sound hp hb.1
  refine ⟨hv,?_,?_⟩
  · simpa only [DyadicLog.jetLog,Jet2.log,div_eq_mul_inv] using mul_sound hb.2.1 hr
  · convert! sub_sound (mul_sound hb.2.2 hr)
      (mul_sound (mul_sound hb.2.1 hb.2.1) (mul_sound hr hr)) using 1
    simp only [Jet2.log,div_eq_mul_inv]
    ring

theorem bivariateLog_sound {p : ℕ} {b : DyadicBivariateJetEnclosure p}
    {out : DyadicInterval p} {j : BivariateJet2} {t : ℝ}
    (hb : b.Contains j t) (hp : 0<b.value.lo) (hl : LogEncloses b.value out) :
    (b.log out).Contains (BivariateJet2.outerCompose Jet2.variableJet.log j) t :=
  DyadicBivariateJetEnclosure.Contains.outerCompose
    (jetLog_sound (DyadicJetEnclosure.contains_variable hb.1) hp (hl _ hb.1)) hb





theorem entropy_encloses {p : ℕ} {c out two plus minus : DyadicInterval p}
    (h2 : two.Contains (Real.log 2))
    (hp : LogEncloses ((ofInt p 1).add c) plus)
    (hm : LogEncloses ((ofInt p 1).sub c) minus)
    (hsub : (entropyRaw c two plus minus).subsetCheck out=true)
    {x : ℝ} (hx : c.Contains x) : out.Contains (biasE x) := by
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have hplus := add_sound hone hx
  have hminus := sub_sound hone hx
  apply subsetCheck_sound hsub
  simpa only [entropyRaw,biasE,div_eq_mul_inv] using
    sub_sound h2 (mul_sound
      (add_sound (mul_sound hplus (hp _ hplus)) (mul_sound hminus (hm _ hminus)))
      (DyadicEntropy.half_contains p))




theorem denominator_encloses {p : ℕ} {c out two gapLog : DyadicInterval p}
    (h2 : two.Contains (Real.log 2))
    (hg : LogEncloses ((ofInt p 1).sub (c.mul c)) gapLog)
    (hsub : (denominatorRaw two gapLog).subsetCheck out=true)
    {x : ℝ} (hx : c.Contains x) : out.Contains (biasB x) := by
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have hgap := sub_sound hone (mul_sound hx hx)
  apply subsetCheck_sound hsub
  simpa only [denominatorRaw,biasB,div_eq_mul_inv] using
    sub_sound h2 (mul_sound (hg _ hgap) (DyadicEntropy.half_contains p))

/-- Only endpoint entropy proofs and exact arithmetic comparisons are required;
the actual contact follows from its already proved monotone inverse. -/
theorem contact_bracket {p : ℕ} {Y c elo ehi : DyadicInterval p}
    (hc0 : 0≤c.lo) (hc1 : c.hi≤scale p) (horder : c.lo≤c.hi) (hY : 0<Y.lo)
    (hel : elo.Contains (biasE ((c.lo:ℝ)/(scale p:ℝ))))
    (heu : ehi.Contains (biasE ((c.hi:ℝ)/(scale p:ℝ))))
    (hleft : (Y.mul (DyadicContact.point c.lo)).hi≤elo.lo)
    (hright : ehi.hi≤(Y.mul (DyadicContact.point c.hi)).lo)
    {y : ℝ} (hy : Y.Contains y) : c.Contains (biasContact y) := by
  have hyp : 0<y := positiveCheck_sound (by simpa [positiveCheck] using hY) hy
  have hs := scale_cast_pos p
  have hl : 0≤(c.lo:ℝ)/(scale p:ℝ) := div_nonneg (by exact_mod_cast hc0) hs.le
  have hu : (c.hi:ℝ)/(scale p:ℝ)≤1 := (div_le_one hs).mpr (by exact_mod_cast hc1)
  have hlu : (c.lo:ℝ)/(scale p:ℝ)≤(c.hi:ℝ)/(scale p:ℝ) :=
    (div_le_div_iff_of_pos_right hs).mpr (by exact_mod_cast horder)
  have hpl := mul_sound hy (DyadicContact.point_contains p c.lo)
  have hpu := mul_sound hy (DyadicContact.point_contains p c.hi)
  have hcmem := biasContact_mem hyp
  have heq : biasE (biasContact y)=y*biasContact y :=
    (div_eq_iff hcmem.1.ne').mp (biasR_biasContact hyp)
  apply contains_toReal_iff.mp
  apply Reflection.contact_bracket hcmem.1.le hcmem.2.le hl hu hlu hyp heq
  · have hcmp : ((Y.mul (DyadicContact.point c.lo)).hi:ℝ)≤(elo.lo:ℝ) := by exact_mod_cast hleft
    exact (mul_le_mul_iff_right₀ hs).mp (hpl.2.trans (hcmp.trans hel.1))
  · have hcmp : (ehi.hi:ℝ)≤((Y.mul (DyadicContact.point c.hi)).lo:ℝ) := by exact_mod_cast hright
    exact (mul_le_mul_iff_right₀ hs).mp (heu.2.trans (hcmp.trans hpu.1))

theorem contact_jet {p : ℕ} {Y c B : DyadicInterval p} {out : DyadicJetEnclosure p}
    (hY : 0<Y.lo)
    (hc : ∀ y : ℝ, Y.Contains y → c.Contains (biasContact y))
    (hB : ∀ x : ℝ, c.Contains x → B.Contains (biasB x))
    (hBp : 0<B.lo) (hgap : 0<(DyadicContact.gap c).lo)
    (hsub : (DyadicContact.enclosure c B).subsetCheck out=true)
    {y : ℝ} (hy : Y.Contains y) : out.Contains reflectionContactJet y := by
  have hyp : 0<y := positiveCheck_sound (by simpa [positiveCheck] using hY) hy
  have hcontact := hc y hy
  exact DyadicJetEnclosure.subsetCheck_sound hsub
    (DyadicContact.enclosure_sound hyp hcontact (hB _ hcontact) hBp hgap)

end GeneralCK.Certificates.ProvedTranscendental

end


