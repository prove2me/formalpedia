-- Prove2me | Definitions.Def_CK_E8CompactInterval
-- name    : CK_E8CompactInterval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:29:12.490988+00:00
-- url     : https://prove2.me/theorems/7473d019-1ebb-46c4-a067-3cbbf82666e1
-- title:
--   Courtade–Kumar proof module `E8CompactInterval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8CompactInterval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8CompactInterval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8CompactInterval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8CompactInterval.lean)

import Definitions.Def_CK_E8CompactTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module E8CompactInterval =====
section

namespace GeneralCK.E8RatioMonotonicity

open Certificates DyadicInterval
open Certificates.E8TAxisStableJet5
open Certificates.E8TAxisStableInterval

def truncateBox {p : ℕ} (j : DyadicJet5Enclosure p) : DyadicJetEnclosure p :=
  ⟨j.d0, j.d1, j.d2⟩

theorem truncateBox_contains {p : ℕ} {box : DyadicJet5Enclosure p} {j : Jet5} {a : ℝ}
    (hc : box.Contains j a) :
    (truncateBox box).Contains ⟨j.d0, j.d1, j.d2⟩ a := ⟨hc.1, hc.2.1, hc.2.2.1⟩

def factorBox {p : ℕ} (jr jk jh jq : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  let c := DyadicJetEnclosure.const p
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

def FactorDenominators {p : ℕ} (jr jk jh : DyadicJetEnclosure p) : Prop :=
  0 < jk.value.lo ∧ 0 < jh.value.lo ∧ 0 < (jr.mul jr).value.lo ∧
    0 < (((DyadicJetEnclosure.const p 2).mul jk).add (jr.mul jr).neg).value.lo

instance {p : ℕ} (jr jk jh : DyadicJetEnclosure p) : Decidable (FactorDenominators jr jk jh) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem factorBox_contains {p : ℕ} {br bk bh bq : DyadicJetEnclosure p}
    {jr jk jh jq : Jet2} {a : ℝ}
    (hr : br.Contains jr a) (hk : bk.Contains jk a)
    (hh : bh.Contains jh a) (hq : bq.Contains jq a)
    (hn : FactorDenominators br bk bh) :
    (factorBox br bk bh bq).Contains (factorJet jr jk jh jq) a := by
  let hc := fun n : ℤ => DyadicJetEnclosure.contains_const p n a
  have ht := hr.mul hr
  have hki := hk.inv hn.1
  have hd := (((hq.mul hk).mul (hh.inv hn.2.1)).add (hc 1).neg).mul (ht.inv hn.2.2.1)
  have hw := ht.mul (((hc 2).mul hk |>.add ht.neg).inv hn.2.2.2)
  have hb := ((((((hc 6).mul (hd.mul hd)).add
    (((hc 4).mul hd).mul (((hc 1).add ((hc 2).mul hw)).add ((hc 3).mul hki).neg)).neg).add
    (hc 2)).add ((hc 4).mul hw)).add ((hc 8).mul (hw.mul hw))).add
    ((((hc 8).add ((hc 10).mul hw)).mul hki).neg)
  have hb := hb.add ((hc 3).mul (hki.mul hki))
  have hresult := ((((hc 6).mul hki).add (hc 4).neg).add
    (((hc 6).mul ((hc 1).add ht.neg)).mul hw).neg).add (ht.mul hb)
  simpa only [factorBox, factorJet, Int.cast_ofNat, Int.cast_one, Nat.cast_one] using hresult

def compactBox {p : ℕ} (i : Inputs p) : DyadicJetEnclosure p :=
  factorBox (truncateBox (rBox i)) (truncateBox (ellBox i))
    (truncateBox (hBox i)) (truncateBox (qBox i))

def CompactDenominators {p : ℕ} (i : Inputs p) : Prop :=
  0 < (onePlusZBox i).d0.lo ∧
  0 < ((onePlusZBox i).mul (onePlusZBox i)).d0.lo ∧
  FactorDenominators (truncateBox (rBox i)) (truncateBox (ellBox i)) (truncateBox (hBox i))

instance {p : ℕ} (i : Inputs p) : Decidable (CompactDenominators i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem compactBox_contains {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hp : CompactDenominators i) : (compactBox i).Contains compactJet a := by
  have a0 := DyadicJet5Enclosure.contains_variable ha
  have c1 : (DyadicJet5Enclosure.const p 1).Contains (Jet5.const 1) a := by
    simpa using DyadicJet5Enclosure.contains_const p 1 a
  have c2 : (DyadicJet5Enclosure.const p 2).Contains (Jet5.const 2) a := by
    simpa using DyadicJet5Enclosure.contains_const p 2 a
  have c4 : (DyadicJet5Enclosure.const p 4).Contains (Jet5.const 4) a := by
    simpa using DyadicJet5Enclosure.contains_const p 4 a
  have hz := zBox_sound he
  have ho : (onePlusZBox i).Contains onePlusZJet a := c1.add hz
  have hr : (rBox i).Contains rJet a :=
    (c1.add (negative_sound hz)).mul (ho.inv hp.1)
  have hq : (qBox i).Contains E8TAxisStableJet5.qJet a :=
    (c4.mul hz).mul ((ho.mul ho).inv hp.2.1)
  have hlog : (l1Box i).Contains l1Jet a := by
    apply ho.log hp.1
    simpa [onePlusZJet, zJet, Jet5.add, Jet5.const, Jet5.expAffine] using hl
  have hell : (ellBox i).Contains ellJet a := a0.add hlog
  have hh : (hBox i).Contains hJet a :=
    hlog.add (((c2.mul a0).mul hz).mul (ho.inv hp.1))
  exact factorBox_contains (truncateBox_contains hr) (truncateBox_contains hell)
    (truncateBox_contains hh) (truncateBox_contains hq) hp.2.2

#print axioms factorBox_contains
#print axioms compactBox_contains

end GeneralCK.E8RatioMonotonicity

end


