-- Prove2me | Definitions.Def_CK_E8CompactTaylor
-- name    : CK_E8CompactTaylor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:36:17.091989+00:00
-- url     : https://prove2.me/theorems/d60a4f64-4b6d-4597-b397-8177d5fe8ce1
-- title:
--   Courtade–Kumar proof module `E8CompactTaylor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8CompactTaylor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8CompactTaylor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8CompactTaylor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8CompactTaylor.lean)

import Definitions.Def_CK_E8InitialInterval
import Definitions.Def_CK_GeneralCK_Certificates_JetProgramTaylor

-- ===== source module E8CompactTaylor =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set Filter Certificates
open Certificates.E8TAxisStableScalar
open Certificates.E8TAxisStableJet5
open Certificates.E8HistoricalLogConvexityBridge

private def truncate (j : Jet5) : Jet2 := ⟨j.d0, j.d1, j.d2⟩

private theorem truncate_sound {j : Jet5} {a : ℝ} (hj : j.SoundAt a) :
    (truncate j).SoundAt a := ⟨hj.1, hj.2.1⟩

/-- An explicit second-order graph, retaining the short quadratic factor. -/
noncomputable def factorJet (jr jk jh jq : Jet2) : Jet2 :=
  let c := Jet2.const
  let t := jr.mul jr
  let ki := jk.inv
  let d := (((jq.mul jk).mul jh.inv).add (c 1).neg).mul t.inv
  let w := t.mul (((c 2).mul jk).add t.neg).inv
  let b := ((((((c 6).mul (d.mul d)).add
    (((c 4).mul d).mul (((c 1).add ((c 2).mul w)).add ((c 3).mul ki).neg)).neg).add
    (c 2)).add ((c 4).mul w)).add ((c 8).mul (w.mul w))).add
    ((((c 8).add ((c 10).mul w)).mul ki).neg)
  let b := b.add ((c 3).mul (ki.mul ki))
  ((((c 6).mul ki).add (c 4).neg).add
    (((c 6).mul ((c 1).add t.neg)).mul w).neg).add (t.mul b)

theorem factorJet_value (jr jk jh jq : Jet2) (a : ℝ) :
    (factorJet jr jk jh jq).value a = compactFactor (jk.value a) (jr.value a ^ 2)
      ((jq.value a * jk.value a / jh.value a - 1) / jr.value a ^ 2) := by
  simp only [factorJet, compactFactor, Jet2.add, Jet2.mul, Jet2.neg, Jet2.const,
    Jet2.inv, div_eq_mul_inv]
  ring

theorem factorJet_sound {jr jk jh jq : Jet2} {a : ℝ}
    (hr : jr.SoundAt a) (hk : jk.SoundAt a) (hh : jh.SoundAt a) (hq : jq.SoundAt a)
    (hrn : jr.value a ≠ 0) (hkn : jk.value a ≠ 0) (hhn : jh.value a ≠ 0)
    (hgn : 2 * jk.value a - jr.value a ^ 2 ≠ 0) :
    (factorJet jr jk jh jq).SoundAt a := by
  let hc := fun n : ℝ => Jet2.soundAt_const n a
  have ht := hr.mul hr
  have hki := hk.inv hkn
  have hti := ht.inv (by simpa [Jet2.mul] using mul_ne_zero hrn hrn)
  have hd := (((hq.mul hk).mul (hh.inv hhn)).add (hc 1).neg).mul hti
  have hwi := ((hc 2).mul hk |>.add ht.neg).inv (by
    simpa [Jet2.add, Jet2.mul, Jet2.const, Jet2.neg, pow_two, sub_eq_add_neg] using hgn)
  have hw := ht.mul hwi
  have hb := ((((((hc 6).mul (hd.mul hd)).add
    (((hc 4).mul hd).mul (((hc 1).add ((hc 2).mul hw)).add ((hc 3).mul hki).neg)).neg).add
    (hc 2)).add ((hc 4).mul hw)).add ((hc 8).mul (hw.mul hw))).add
    ((((hc 8).add ((hc 10).mul hw)).mul hki).neg)
  have hb := hb.add ((hc 3).mul (hki.mul hki))
  exact ((((hc 6).mul hki).add (hc 4).neg).add
    (((hc 6).mul ((hc 1).add ht.neg)).mul hw).neg).add (ht.mul hb)

noncomputable def compactJet : Jet2 :=
  factorJet (truncate rJet) (truncate ellJet) (truncate hJet)
    (truncate E8TAxisStableJet5.qJet)

theorem compactJet_sound {a : ℝ} (ha : 0 < a) : compactJet.SoundAt a := by
  apply factorJet_sound (truncate_sound (rJet_soundAt a))
    (truncate_sound (ellJet_soundAt a)) (truncate_sound (hJet_soundAt a))
    (truncate_sound (E8TAxisStableJet5.qJet_soundAt a))
  · simpa [truncate] using (r_pos ha).ne'
  · simpa [truncate] using (ell_pos ha).ne'
  · simpa [truncate] using (h_pos ha).ne'
  · simpa [truncate] using (stable_gap_pos ha).ne'

theorem compactJet_value {a : ℝ} (ha : 0 < a) : compactJet.value a = stableL a := by
  rw [compactJet, factorJet_value]
  simp only [truncate, rJet_d0, ellJet_d0, hJet_d0, qJet_d0]
  rw [stableL_eq_compactFactor ha]
  congr 1
  unfold entropyQuotient
  field_simp [(r_pos ha).ne', (h_pos ha).ne']
  rw [← one_sub_r_sq, ← h_add_a_mul_r]
  ring

/-- Integer-only acceptance test for a centered cell. `slope` encloses x-center. -/
def centeredTaylorCheck {p : ℕ} (center whole : DyadicJetEnclosure p)
    (slope : DyadicInterval p) : Bool :=
  decide (0 < 2 * center.value.lo + 2 * (center.first.mul slope).lo +
    (whole.second.mul (slope.mul slope)).lo)

/-- Sound contract for the proposed 446-cell middle cover. Every analytic jet
link is unconditional; the finite replay must supply the stated enclosures. -/
theorem stableL_pos_of_centered_enclosures {p : ℕ}
    {alpha slope : DyadicInterval p} {center whole : DyadicJetEnclosure p} {c x : ℝ}
    (hc : alpha.Contains c) (hx : alpha.Contains x)
    (hpos : ∀ a : ℝ, alpha.Contains a → 0 < a)
    (hd : slope.Contains (x - c))
    (hcenter : center.Contains compactJet c)
    (hwhole : ∀ a : ℝ, alpha.Contains a → whole.Contains compactJet a)
    (hcheck : centeredTaylorCheck center whole slope = true) : 0 < stableL x := by
  let seg := Jet2.segment c x
  have hs : (compactJet.comp seg).SoundOn (Icc (0 : ℝ) 1) := by
    intro t ht
    have hmem := DyadicInterval.contains_segment hc hx ht
    exact (compactJet_sound (hpos _ hmem)).comp
      (Jet2.soundOn_segment c x (Icc (0 : ℝ) 1) t ht)
  let cb : DyadicJetEnclosure p :=
    ⟨center.value, center.first.mul slope,
      (center.second.mul (slope.mul slope)).add (center.first.mul (DyadicInterval.ofInt p 0))⟩
  let wb : DyadicJetEnclosure p :=
    ⟨whole.value, whole.first.mul slope,
      whole.second.mul (slope.mul slope)⟩
  have hcz : cb.Contains (compactJet.comp seg) 0 := by
    have hcenter' : center.Contains compactJet ((Jet2.segment c x).value 0) := by
      simpa only [Jet2.segment_value_zero] using hcenter
    have h := hcenter'.comp (DyadicJetEnclosure.contains_segment_zero hc hd)
    simpa only [cb, seg, DyadicJetEnclosure.comp, DyadicJetEnclosure.segmentBox,
      Jet2.segment_value_zero] using h
  have hwz : wb.ContainsOn (compactJet.comp seg) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hv := hwhole _ (DyadicInterval.contains_segment hc hx ht)
    refine ⟨hv.1, DyadicInterval.mul_sound hv.2.1 hd, ?_⟩
    have hb := DyadicInterval.mul_sound hv.2.2 (DyadicInterval.mul_sound hd hd)
    simpa only [wb, Jet2.comp, seg, Jet2.segment, mul_zero, add_zero, pow_two] using hb
  have h := DyadicJetEnclosure.value_pos_of_separate_taylor hs hcz hwz hcheck
  simpa only [Jet2.comp, seg, Jet2.segment_value_one, compactJet_value (hpos _ hx)] using h

#print axioms compactJet_sound
#print axioms compactJet_value
#print axioms stableL_pos_of_centered_enclosures

end GeneralCK.E8RatioMonotonicity

end


