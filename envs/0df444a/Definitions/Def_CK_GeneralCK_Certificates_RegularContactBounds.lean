-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_RegularContactBounds
-- name    : CK_GeneralCK_Certificates_RegularContactBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:05.462618+00:00
-- url     : https://prove2.me/theorems/369884a1-3e4e-4202-b8d1-d57743d1414c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.RegularContactBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.RegularContactBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.RegularContactBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.RegularContactBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/RegularContactBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_RegularContactJet
import Definitions.Def_CK_GeneralCK_Certificates_Jet2Bounds

-- ===== source module GeneralCK.Certificates.RegularContactBounds =====
section

namespace GeneralCK.Certificates.RegularContactBounds
open JetBounds GeneralCK.Reflection GeneralCK.Certificates.Reflection

theorem regularContact_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ regularContact y := by
  rw [regularContact_equation y]
  exact mul_nonneg hy (biasE_pos_wide (regularContact_mem y).1 (regularContact_mem y).2).le

/-- The increasing regular contact is bracketed without dividing by its radius. -/
theorem contact_contains {c Y : Interval} {y : ℝ} (hy : Y.Contains y)
    (hY : 0 ≤ Y.lo) (hc0 : 0 ≤ c.lo) (hc1 : c.hi ≤ 1) (horder : c.lo ≤ c.hi)
    (hl : c.lo ≤ Y.lo*biasE c.lo) (hu : Y.hi*biasE c.hi ≤ c.hi) :
    c.Contains (regularContact y) := by
  have hyp : 0 ≤ y := hY.trans hy.1
  have hcm := regularContact_mem y
  have hcn := regularContact_nonneg hyp
  have heq := regularContact_equation y
  have he1 : biasE 1=0 := by norm_num [biasE]
  have hel : 0 ≤ biasE c.lo := by
    have h := biasE_antitone ⟨hc0,horder.trans hc1⟩ (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
      (horder.trans hc1)
    simpa only [he1] using h
  have heu : 0 ≤ biasE c.hi := by
    have h := biasE_antitone ⟨hc0.trans horder,hc1⟩ (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) hc1
    simpa only [he1] using h
  constructor
  · by_contra hn
    have hh : regularContact y < c.lo := lt_of_not_ge hn
    have hm := biasE_antitone ⟨hcn,hcm.2.le⟩ ⟨hc0,horder.trans hc1⟩ hh.le
    have h1 := mul_le_mul_of_nonneg_right hy.1 hel
    have h2 := mul_le_mul_of_nonneg_left hm hyp
    linarith
  · by_contra hn
    have hh : c.hi < regularContact y := lt_of_not_ge hn
    have hm := biasE_antitone ⟨hc0.trans horder,hc1⟩ ⟨hcn,hcm.2.le⟩ hh.le
    have h1 := mul_le_mul_of_nonneg_right hy.2 heu
    have h2 := mul_le_mul_of_nonneg_left hm hyp
    linarith

theorem first_eq (y : ℝ) : regularContactJet.first y =
    (biasE (regularContact y))^2/biasB (regularContact y) := rfl

theorem second_eq (y : ℝ) : regularContactJet.second y =
    -2*(biasE (regularContact y))^3*SmallMean.A (regularContact y)/(biasB (regularContact y))^2 -
    (biasE (regularContact y))^4*regularContact y/
      ((1-(regularContact y)^2)*(biasB (regularContact y))^3) := rfl

/-- All reciprocal denominators are positive; the contact interval may contain zero. -/
noncomputable def enclosure (c E B A : Interval) : JetEnclosure :=
  let r := B.inv
  let gap := (Interval.point 1).sub c.sq
  ⟨c,E.sq.mul r,
    ((((Interval.point 2).mul E.cube).mul A).mul r.sq).neg.sub
      (((E.sq.sq.mul c).mul gap.inv).mul r.cube)⟩

theorem contains {c E B A : Interval} {y : ℝ}
    (hc : c.Contains (regularContact y)) (hE : E.Contains (biasE (regularContact y)))
    (hB : B.Contains (biasB (regularContact y))) (hA : A.Contains (SmallMean.A (regularContact y)))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    (enclosure c E B A).Contains regularContactJet y := by
  have hr := hB.inv hBp
  have hg := ((Interval.contains_point 1).sub hc.sq).inv hgap
  refine ⟨hc,?_,?_⟩
  · rw [first_eq]
    exact hE.sq.div hB hBp
  · rw [second_eq]
    have h := ((((Interval.contains_point 2).mul hE.cube).mul hA).mul hr.sq).neg.sub
      (((hE.sq.sq.mul hc).mul hg).mul hr.cube)
    have he (x e b a : ℝ) : -2*e^3*a/b^2-e^4*x/((1-x^2)*b^3) =
        -(2*e^3*a*(b⁻¹)^2)-(e^2)^2*x*(1-x^2)⁻¹*(b⁻¹)^3 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    rw [he]
    exact h

theorem contains_comp {c E B A : Interval} {input : JetEnclosure} {j : Jet2} {t : ℝ}
    (hj : input.Contains j t)
    (hc : c.Contains (regularContact (j.value t)))
    (hE : E.Contains (biasE (regularContact (j.value t))))
    (hB : B.Contains (biasB (regularContact (j.value t))))
    (hA : A.Contains (SmallMean.A (regularContact (j.value t))))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    ((enclosure c E B A).comp input).Contains (regularContactJet.comp j) t :=
  (contains hc hE hB hA hBp hgap).comp hj

theorem containsOn_comp {c E B A : Interval} {input : JetEnclosure} {j : Jet2} {s : Set ℝ}
    (hj : input.ContainsOn j s)
    (hc : ∀ t ∈ s, c.Contains (regularContact (j.value t)))
    (hE : ∀ t ∈ s, E.Contains (biasE (regularContact (j.value t))))
    (hB : ∀ t ∈ s, B.Contains (biasB (regularContact (j.value t))))
    (hA : ∀ t ∈ s, A.Contains (SmallMean.A (regularContact (j.value t))))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    ((enclosure c E B A).comp input).ContainsOn (regularContactJet.comp j) s :=
  fun t ht => contains_comp (hj t ht) (hc t ht) (hE t ht) (hB t ht) (hA t ht) hBp hgap

end GeneralCK.Certificates.RegularContactBounds

end


