-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallRatioMidpoint
-- name    : CK_GeneralCK_ReflectionSmallRatioMidpoint
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:48:47.875971+00:00
-- url     : https://prove2.me/theorems/33faf82e-daaa-4958-9cfb-9fe93ff30fc2
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallRatioMidpoint` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallRatioMidpoint` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallRatioMidpoint` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallRatioMidpoint (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallRatioMidpoint.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallRatio
import Definitions.Def_CK_GeneralCK_Certificates_MidpointBounds

-- ===== source module GeneralCK.ReflectionSmallRatioMidpoint =====
section

namespace GeneralCK.Reflection.SmallRatio
open Set Certificates Certificates.Reflection Certificates.ReflectionExpression

/-- A quadratic majorant of P controls the contact difference with its exact
midpoint average. The entropy is fixed throughout the radius interval. -/
theorem difference_le_midpoint {a e l u p0 p1 M : ℝ}
    (ha : 0<a) (ha' : a<1) (he : 0<e) (hl : 0<l) (hlu : l<u)
    (hP : ∀ s ∈ Ioo l u,
      P a e s ≤ p0+p1*(s-(l+u)/2)+M*(s-(l+u)/2)^2/2) :
    V a e u-V a e l ≤ (p0+M*(u-l)^2/24)*(u-l) := by
  have h := difference_le_midpoint_quadratic hlu
    (fun s hs => hasDerivAt_V ha ha' he (hl.trans_le hs.1)) hP
  convert! h using 1 <;> ring

theorem normalized_lower_of_midpoint {a b e p0 p1 M : ℝ}
    (ha : 0<a) (ha' : a<1) (hb : 0<b) (hba : b<a) (he : 0<e)
    (hP : ∀ s ∈ Ioo ((a-b)/2) ((a+b)/2),
      P a e s ≤ p0+p1*(s-a/2)+M*(s-a/2)^2/2) :
    (2*a/(1-a^2)^2-(p0+M*b^2/24))/a^3 ≤
      (2*a*b/(1-a^2)^2+V a e ((a-b)/2)-V a e ((a+b)/2))/(a^3*b) := by
  have h := difference_le_midpoint ha ha' he (by linarith : 0<(a-b)/2)
    (by linarith : (a-b)/2<(a+b)/2) (p0 := p0) (p1 := p1) (M := M)
  have hm : ((a-b)/2+(a+b)/2)/2=a/2 := by ring
  have hb' : (a+b)/2-(a-b)/2=b := by ring
  simp only [hm,hb'] at h
  have hd := h hP
  have hgap : 1-a^2≠0 := by nlinarith
  calc
    _ = (2*a*b/(1-a^2)^2-(p0+M*b^2/24)*b)/(a^3*b) := by
      field_simp [ha.ne',hb.ne',hgap]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (mul_pos (pow_pos ha 3) hb).le

/-- Acceptance rule for the actual curvature. Numeric bounds on the center
value and second derivative suffice once the quadratic majorant is proved. -/
theorem curvature_pos_of_midpoint_bound {a z p0 p1 M : ℝ}
    (ha : 0<a) (ha' : a<1) (hz : 0<z) (hz' : z<1)
    (hP : ∀ s ∈ Ioo (a*(1-z)/2) (a*(1+z)/2),
      P a ((biasE a+biasE (a*z))/2) s ≤ p0+p1*(s-a/2)+M*(s-a/2)^2/2)
    (haccept : p0+M*(a*z)^2/24<2*a/(1-a^2)^2) : 0<curvature a (a*z) := by
  have hb : 0<a*z := mul_pos ha hz
  have hba : a*z<a := by nlinarith
  have he : 0<(biasE a+biasE (a*z))/2 := by
    rw [biasE_eq_log_mul_E (by linarith) ha',biasE_eq_log_mul_E (by linarith) (hba.trans ha')]
    have hmean := meanEntropy_pos (by linarith : -1<a) ha'
      (by linarith : -1<a*z) (hba.trans ha')
    convert! mul_pos log_two_pos hmean using 1
    unfold meanEntropy
    ring
  have h := normalized_lower_of_midpoint ha ha' hb hba he (p0 := p0) (p1 := p1) (M := M)
  rw [show (a-a*z)/2=a*(1-z)/2 by ring,show (a+a*z)/2=a*(1+z)/2 by ring] at h
  apply curvature_pos_of_normalizedValue_pos ha ha' hz hz'
  exact (div_pos (sub_pos.mpr haccept) (pow_pos ha 3)).trans_le (h hP)

end GeneralCK.Reflection.SmallRatio

end


