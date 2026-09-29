-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionContactBounds
-- name    : CK_GeneralCK_Certificates_ReflectionContactBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:07:08.44538+00:00
-- url     : https://prove2.me/theorems/c26c0e4d-53e9-4db0-9252-0e93a5795272
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionContactBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionContactBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionContactBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionContactBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionContactBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionContactJet
import Definitions.Def_CK_GeneralCK_Certificates_Jet2Bounds

namespace GeneralCK.Certificates.ReflectionContactBounds
open JetBounds
open GeneralCK.Reflection
open GeneralCK.Certificates.Reflection

theorem first_eq {y : ℝ} (_hy : 0 < y) :
    reflectionContactJet.first y = -(biasContact y)^2/biasB (biasContact y) := by
  simp only [reflectionContactJet,biasRprime,neg_div,inv_neg,inv_div]

/-- Inverse-ratio second derivative expressed using positive denominators only. -/
theorem second_eq {y : ℝ} (hy : 0 < y) :
    reflectionContactJet.second y =
      2*(biasContact y)^3/(biasB (biasContact y))^2 -
      (biasContact y)^5/((1-(biasContact y)^2)*(biasB (biasContact y))^3) := by
  have hc := biasContact_mem hy
  have hb := (biasB_pos hc.1 hc.2).ne'
  have hg : 1-(biasContact y)^2 ≠ 0 := by nlinarith [hc.1,hc.2]
  simp only [reflectionContactJet,biasRsecond,biasRprime]
  field_simp [hc.1.ne',hb,hg]

/-- Arithmetic enclosure of the contact jet; soundness checks both reciprocal domains. -/
noncomputable def enclosure (c B : Interval) : JetEnclosure :=
  let r := B.inv
  let gap := (Interval.point 1).sub c.sq
  ⟨c,(c.sq.mul r).neg,
    (((Interval.point 2).mul c.cube).mul r.sq).sub
      (((c.cube.mul c.sq).mul gap.inv).mul r.cube)⟩

theorem contains {c B : Interval} {y : ℝ} (hy : 0 < y)
    (hc : c.Contains (biasContact y)) (hB : B.Contains (biasB (biasContact y)))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    (enclosure c B).Contains reflectionContactJet y := by
  have hr := hB.inv hBp
  have hg := ((Interval.contains_point 1).sub hc.sq).inv hgap
  refine ⟨hc,?_,?_⟩
  · rw [first_eq hy]
    simpa only [enclosure,div_eq_mul_inv,neg_mul] using (hc.sq.mul hr).neg
  · rw [second_eq hy]
    have h := (((Interval.contains_point 2).mul hc.cube).mul hr.sq).sub
      (((hc.cube.mul hc.sq).mul hg).mul hr.cube)
    have he (x b : ℝ) : 2*x^3/b^2-x^5/((1-x^2)*b^3) =
        2*x^3*(b⁻¹)^2-x^3*x^2*(1-x^2)⁻¹*(b⁻¹)^3 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    rw [he]
    exact h

/-- Produce a contact bracket from entropy inequalities at its rational endpoints. -/
theorem contact_contains {c Y : Interval} {y : ℝ} (hy : Y.Contains y)
    (hY : 0 < Y.lo) (hc0 : 0 ≤ c.lo) (hc1 : c.hi ≤ 1) (horder : c.lo ≤ c.hi)
    (hl : Y.hi*c.lo ≤ biasE c.lo) (hu : biasE c.hi ≤ Y.lo*c.hi) :
    c.Contains (biasContact y) := by
  have hyp : 0 < y := hY.trans_le hy.1
  have hcm := biasContact_mem hyp
  have heq : biasE (biasContact y) = y*biasContact y := by
    have h := biasR_biasContact hyp
    exact (div_eq_iff hcm.1.ne').mp h
  exact contact_bracket hcm.1.le hcm.2.le hc0 hc1 horder hyp heq
    ((mul_le_mul_of_nonneg_right hy.2 hc0).trans hl)
    (hu.trans (mul_le_mul_of_nonneg_right hy.1 (hc0.trans horder)))

/-- Enclosure propagation through contact composition, without assumptions about derivatives. -/
theorem contains_comp {c B : Interval} {input : JetEnclosure} {j : Jet2} {t : ℝ}
    (hj : input.Contains j t) (hy : 0 < j.value t)
    (hc : c.Contains (biasContact (j.value t)))
    (hB : B.Contains (biasB (biasContact (j.value t))))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    ((enclosure c B).comp input).Contains (reflectionContactJet.comp j) t :=
  (contains hy hc hB hBp hgap).comp hj

theorem containsOn_comp {c B : Interval} {input : JetEnclosure} {j : Jet2} {s : Set ℝ}
    (hj : input.ContainsOn j s) (hy : ∀ t ∈ s, 0 < j.value t)
    (hc : ∀ t ∈ s, c.Contains (biasContact (j.value t)))
    (hB : ∀ t ∈ s, B.Contains (biasB (biasContact (j.value t))))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    ((enclosure c B).comp input).ContainsOn (reflectionContactJet.comp j) s :=
  fun t ht => contains_comp (hj t ht) (hy t ht) (hc t ht) (hB t ht) hBp hgap

end GeneralCK.Certificates.ReflectionContactBounds


