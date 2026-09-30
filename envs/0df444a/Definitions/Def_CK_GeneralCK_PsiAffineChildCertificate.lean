-- Prove2me | Definitions.Def_CK_GeneralCK_PsiAffineChildCertificate
-- name    : CK_GeneralCK_PsiAffineChildCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:58:50.361273+00:00
-- url     : https://prove2.me/theorems/dc5be860-0f40-42c4-a4e4-105e82ce9742
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiAffineChildCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiAffineChildCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiAffineChildCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiAffineChildCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiAffineChildCertificate.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_EqualMean

-- ===== source module GeneralCK.PsiAffineChildCertificate =====
section

/-!
# Three-variable certificates from actual child entropy supports

Each child gets an affine lower support to its actual hybrid profile, with
its own feasible reference entropy. The minimum of the resulting affine sum
over the exact feasible allocation interval is an explicit endpoint minimum.
Only the two means and the average entropy remain as chart variables.
-/

namespace GeneralCK.PsiAffineChildCertificate
open Set

structure EntropySupport (m : ℝ) where
  intercept : ℝ
  slope : ℝ
  lower : ∀ h : ℝ, 0 < h → h ≤ H m → intercept + slope * h ≤ B m h

private theorem convex_tangent_lower {f : ℝ → ℝ} {cap x y : ℝ}
    (hc : ConvexOn ℝ (Ioc 0 cap) f) (hx : x ∈ Ioc 0 cap) (hy : y ∈ Ioc 0 cap)
    (hd : DifferentiableAt ℝ f x) :
    f x + deriv f x * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have h := hc.le_slope_of_hasDerivAt hx hy hlt hd.hasDerivAt
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    linarith
  · simp only [heq, sub_self, mul_zero, add_zero, le_refl]
  · have h := hc.slope_le_of_hasDerivAt hy hx hgt hd.hasDerivAt
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith only [hh]

private theorem phi_differentiable {m h : ℝ} (hh : 0 < h) (hcap : h < H m) :
    DifferentiableAt ℝ (phi m) h := by
  have hh1 : h < 1 := hcap.trans_le (H_le_one _)
  change DifferentiableAt ℝ (radialPhi |1 - 2 * m|) h
  rcases (abs_nonneg (1 - 2 * m)).eq_or_lt with heq | hpos
  · rw [← heq, EntropyCurvature.radialPhi_zero]
    exact (hasDerivAt_eta hh hh1).differentiableAt
  · exact (EntropyCurvature.hasDerivAt_radialPhi_entropy hpos hh hh1).differentiableAt

private theorem psi_differentiable {m h : ℝ} (hh : 0 < h) (hcap : h < H m) :
    DifferentiableAt ℝ (psi m) h := by
  have ha : 0 < h + 1 - H m := by linarith [H_le_one m]
  have ha1 : h + 1 - H m < 1 := by linarith
  exact ((hasDerivAt_eta ha ha1).comp h
    (((hasDerivAt_id h).add_const 1).sub_const (H m))).differentiableAt

/-- A concrete support from the phi tangent at a separately feasible entropy. -/
noncomputable def phiSupport (m h : ℝ) (hm : 0 < m) (hm1 : m < 1)
    (hh : 0 < h) (hcap : h < H m) : EntropySupport m where
  intercept := phi m h - deriv (phi m) h * h
  slope := deriv (phi m) h
  lower := by
    intro y hy hycap
    have ht := convex_tangent_lower (phi_entropy_convexOn hm hm1)
      ⟨hh, hcap.le⟩ ⟨hy, hycap⟩ (phi_differentiable hh hcap)
    have hb : phi m y ≤ B m y := le_max_left _ _
    nlinarith only [ht, hb]

/-- A concrete support from the psi tangent, independently of the other child. -/
noncomputable def psiSupport (m h : ℝ) (hh : 0 < h) (hcap : h < H m) : EntropySupport m where
  intercept := psi m h - deriv (psi m) h * h
  slope := deriv (psi m) h
  lower := by
    intro y hy hycap
    have ht := convex_tangent_lower (psi_entropy_convexOn (m := m))
      ⟨hh, hcap.le⟩ ⟨hy, hycap⟩ (psi_differentiable hh hcap)
    have hb : psi m y ≤ B m y := le_max_right _ _
    nlinarith only [ht, hb]

/-- Convex mixtures allow supporting slopes at crossings of the two branches. -/
noncomputable def mixSupport {m : ℝ} (S T : EntropySupport m) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : EntropySupport m where
  intercept := w * S.intercept + (1 - w) * T.intercept
  slope := w * S.slope + (1 - w) * T.slope
  lower := by
    intro h hh hcap
    have hs := mul_le_mul_of_nonneg_left (S.lower h hh hcap) hw
    have ht := mul_le_mul_of_nonneg_left (T.lower h hh hcap) (sub_nonneg.mpr hw1)
    nlinarith only [hs, ht]

noncomputable def allocationLower (a b E : ℝ) : ℝ := max 0 (2 * E - H b)
noncomputable def allocationUpper (a b E : ℝ) : ℝ := min (H a) (2 * E)

noncomputable def childFloor {a b : ℝ} (S : EntropySupport a) (T : EntropySupport b)
    (E : ℝ) : ℝ :=
  (S.intercept + T.intercept + 2 * E * T.slope +
    min ((S.slope - T.slope) * allocationLower a b E)
      ((S.slope - T.slope) * allocationUpper a b E)) / 2

theorem childFloor_lower {a b e f E : ℝ}
    (S : EntropySupport a) (T : EntropySupport b)
    (he : 0 < e) (hf : 0 < f) (hecap : e ≤ H a) (hfcap : f ≤ H b)
    (hE : (e + f) / 2 = E) :
    childFloor S T E ≤ (B a e + B b f) / 2 := by
  have hlo : allocationLower a b E ≤ e := by
    apply max_le he.le
    linarith
  have hup : e ≤ allocationUpper a b E := by
    apply le_min hecap
    linarith
  have hm : min ((S.slope - T.slope) * allocationLower a b E)
      ((S.slope - T.slope) * allocationUpper a b E) ≤ (S.slope - T.slope) * e := by
    by_cases hs : 0 ≤ S.slope - T.slope
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlo hs)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hup (le_of_not_ge hs))
  have hs := S.lower e he hecap
  have ht := T.lower f hf hfcap
  have heq : 2 * E * T.slope = (e + f) * T.slope :=
    congrArg (fun z : ℝ => z * T.slope) (by linarith only [hE])
  unfold childFloor
  nlinarith only [hm, hs, ht, heq]

/-- Both established cost floors depend only on the three chart variables. -/
noncomputable def scalarCostFloor (a b E : ℝ) : ℝ :=
  max (F (b - a) E)
    (interiorCost a b + (a - b) ^ 2 / (4 * LogSum.V a b) * (H a + H b - 2 * E))

theorem scalarCostFloor_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) : scalarCostFloor μ.a μ.b μ.meanEntropy ≤ μ.cost := by
  apply max_le (PsiEndpointPlane.law_radial_lower μ hab)
  have h := LogSum.cost_lower_bound μ
  convert! h using 1
  unfold InteriorLaw.meanEntropy
  ring

/-- The explicit numerical inequality needed after choosing the two supports.
It depends on `(a,b,E)` and the chosen support data, not the law entropy split. -/
def certificateInequality {a b : ℝ} (S : EntropySupport a) (T : EntropySupport b)
    (E : ℝ) : Prop :=
  psi ((a + b) / 2) E - childFloor S T E ≤ scalarCostFloor a b E

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy)
    (S : EntropySupport μ.a) (T : EntropySupport μ.b)
    (hcert : certificateInequality S T μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hchild := childFloor_lower S T μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap rfl
  change childFloor S T μ.meanEntropy ≤ (B μ.a μ.e + B μ.b μ.f) / 2 at hchild
  have hparent : B μ.midpoint μ.meanEntropy = psi μ.midpoint μ.meanEntropy := max_eq_right hactive
  have hgap : μ.gap ≤ psi μ.midpoint μ.meanEntropy - childFloor S T μ.meanEntropy := by
    unfold InteriorLaw.gap
    change B μ.midpoint μ.meanEntropy - (B μ.a μ.e + B μ.b μ.f) / 2 ≤ _
    rw [hparent]
    linarith only [hchild]
  exact (hgap.trans hcert).trans (scalarCostFloor_le_cost μ hab)

/-- A three-real-variable chart contract. Tangent constructors above provide
the support proofs; production only needs to certify their displayed scalar
comparison. Each reference entropy has its own child's cap. -/
def AffineChildCertificate (region : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ a b E : ℝ, 0 < a → a < b → b < 1 → 0 < E → E ≤ (H a + H b) / 2 →
    region a b E → phi ((a + b) / 2) E ≤ psi ((a + b) / 2) E →
    ∃ S : EntropySupport a, ∃ T : EntropySupport b, certificateInequality S T E

theorem law_gap_le_cost_of_certificate {ι : Type*} [Fintype ι]
    {region : ℝ → ℝ → ℝ → Prop} (hcert : AffineChildCertificate region)
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (hregion : region μ.a μ.b μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hcap : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap]
  obtain ⟨S, T, hs⟩ := hcert μ.a μ.b μ.meanEntropy μ.a_interior.1 hab μ.b_interior.2
    hE hcap hregion hactive
  exact law_gap_le_cost μ hab hactive S T hs

end GeneralCK.PsiAffineChildCertificate

#print axioms GeneralCK.PsiAffineChildCertificate.phiSupport
#print axioms GeneralCK.PsiAffineChildCertificate.psiSupport
#print axioms GeneralCK.PsiAffineChildCertificate.mixSupport
#print axioms GeneralCK.PsiAffineChildCertificate.childFloor_lower
#print axioms GeneralCK.PsiAffineChildCertificate.scalarCostFloor_le_cost
#print axioms GeneralCK.PsiAffineChildCertificate.law_gap_le_cost_of_certificate

end


