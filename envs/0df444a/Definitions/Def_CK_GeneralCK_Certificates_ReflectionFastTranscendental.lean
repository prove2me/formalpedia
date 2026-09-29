-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionFastTranscendental
-- name    : CK_GeneralCK_Certificates_ReflectionFastTranscendental
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:10:35.512582+00:00
-- url     : https://prove2.me/theorems/532f42c5-5f33-4e83-aded-e8cd58f4587e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionFastTranscendental` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionFastTranscendental` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionFastTranscendental` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionFastTranscendental (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionFastTranscendental.lean)

import Definitions.Def_CK_GeneralCK_Certificates_CorrectionIntegerLogTableKernel
import Definitions.Def_CK_GeneralCK_Certificates_ProvedTranscendental

-- ===== source module GeneralCK.Certificates.ReflectionFastTranscendental =====
section

/-! Compact executable transcendental witnesses for reflection programs. -/

namespace GeneralCK.Certificates.ReflectionFastTranscendental

open GeneralCK.Reflection
open CorrectionIntegerLogTableKernel

structure LogWitness where
  lower : Datum
  upper : Datum
  deriving DecidableEq, Repr

def LogWitness.check (input output : DyadicInterval 40) (w : LogWitness) : Bool :=
  decide (0 < input.lo ∧ w.lower.z = input.lo ∧ w.upper.z = input.hi) &&
    w.lower.check && w.upper.check &&
    w.lower.output.subsetCheck output && w.upper.output.subsetCheck output

theorem LogWitness.sound {input output : DyadicInterval 40} {w : LogWitness}
    (h : w.check input output = true) :
    ProvedTranscendental.LogEncloses input output := by
  simp only [LogWitness.check, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨guards, hl⟩, hu⟩, hsl⟩, hsu⟩
  have g := of_decide_eq_true guards
  apply ProvedTranscendental.log_of_endpoints
  · exact g.1
  · rw [← g.2.1]
    exact DyadicInterval.subsetCheck_sound hsl (Datum.sound_of_check hl)
  · rw [← g.2.2]
    exact DyadicInterval.subsetCheck_sound hsu (Datum.sound_of_check hu)

theorem LogWitness.input_positive {input output : DyadicInterval 40} {w : LogWitness}
    (h : w.check input output = true) : 0 < input.lo := by
  simp only [LogWitness.check, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.1.1.1.1).1

structure EntropyWitness where
  two : DyadicInterval 40
  plus : DyadicInterval 40
  minus : DyadicInterval 40
  output : DyadicInterval 40
  twoLog : LogWitness
  plusLog : LogWitness
  minusLog : LogWitness
  deriving DecidableEq, Repr

def EntropyWitness.check (c : DyadicInterval 40) (w : EntropyWitness) : Bool :=
  w.twoLog.check (DyadicInterval.ofInt 40 2) w.two &&
    w.plusLog.check ((DyadicInterval.ofInt 40 1).add c) w.plus &&
    w.minusLog.check ((DyadicInterval.ofInt 40 1).sub c) w.minus &&
    (ProvedTranscendental.entropyRaw c w.two w.plus w.minus).subsetCheck w.output

theorem EntropyWitness.sound {c : DyadicInterval 40} {w : EntropyWitness}
    (h : w.check c = true) {x : ℝ} (hx : c.Contains x) :
    w.output.Contains (Reflection.biasE x) := by
  simp only [EntropyWitness.check, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨h2, hp⟩, hm⟩, hsub⟩
  exact ProvedTranscendental.entropy_encloses
    (w.twoLog.sound h2 2 (by
      norm_num [DyadicInterval.Contains, DyadicInterval.ofInt, DyadicInterval.scale]))
    (w.plusLog.sound hp)
    (w.minusLog.sound hm) hsub hx

structure BWitness where
  two : DyadicInterval 40
  gapLog : DyadicInterval 40
  output : DyadicInterval 40
  twoLog : LogWitness
  gapLogWitness : LogWitness
  deriving DecidableEq, Repr

def BWitness.check (c : DyadicInterval 40) (w : BWitness) : Bool :=
  w.twoLog.check (DyadicInterval.ofInt 40 2) w.two &&
    w.gapLogWitness.check
      ((DyadicInterval.ofInt 40 1).sub (c.mul c)) w.gapLog &&
    (ProvedTranscendental.denominatorRaw w.two w.gapLog).subsetCheck w.output

theorem BWitness.sound {c : DyadicInterval 40} {w : BWitness}
    (h : w.check c = true) {x : ℝ} (hx : c.Contains x) :
    w.output.Contains (Reflection.biasB x) := by
  simp only [BWitness.check, Bool.and_eq_true] at h
  rcases h with ⟨⟨h2, hg⟩, hsub⟩
  exact ProvedTranscendental.denominator_encloses
    (w.twoLog.sound h2 2 (by
      norm_num [DyadicInterval.Contains, DyadicInterval.ofInt, DyadicInterval.scale]))
    (w.gapLogWitness.sound hg) hsub hx

structure ContactWitness where
  contact : DyadicInterval 40
  denominator : DyadicInterval 40
  outer : DyadicJetEnclosure 40
  entropyLo : EntropyWitness
  entropyHi : EntropyWitness
  bWitness : BWitness
  deriving DecidableEq, Repr

def ContactWitness.check (input : DyadicInterval 40) (w : ContactWitness) : Bool :=
  decide (0 ≤ w.contact.lo ∧ w.contact.hi ≤ DyadicInterval.scale 40 ∧
    w.contact.lo ≤ w.contact.hi ∧ 0 < input.lo) &&
    w.entropyLo.check (DyadicContact.point w.contact.lo) &&
    w.entropyHi.check (DyadicContact.point w.contact.hi) &&
    decide ((input.mul (DyadicContact.point w.contact.lo)).hi ≤ w.entropyLo.output.lo ∧
      w.entropyHi.output.hi ≤ (input.mul (DyadicContact.point w.contact.hi)).lo) &&
    w.bWitness.check w.contact &&
    decide (w.bWitness.output = w.denominator ∧ 0 < w.denominator.lo ∧
      0 < (DyadicContact.gap w.contact).lo) &&
    (DyadicContact.enclosure w.contact w.denominator).subsetCheck w.outer

theorem ContactWitness.sound {input : DyadicInterval 40} {w : ContactWitness}
    (h : w.check input = true) {y : ℝ} (hy : input.Contains y) :
    w.outer.Contains reflectionContactJet y := by
  simp only [ContactWitness.check, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨guards, hlo⟩, hhi⟩, compares⟩, hb⟩, positive⟩, hsub⟩
  have g := of_decide_eq_true guards
  have cmp := of_decide_eq_true compares
  have pos := of_decide_eq_true positive
  have hden : w.bWitness.output = w.denominator := pos.1
  have hc : w.contact.Contains (biasContact y) :=
    ProvedTranscendental.contact_bracket g.1 g.2.1 g.2.2.1 g.2.2.2
      (w.entropyLo.sound hlo (DyadicContact.point_contains 40 w.contact.lo))
      (w.entropyHi.sound hhi (DyadicContact.point_contains 40 w.contact.hi))
      cmp.1 cmp.2 hy
  exact DyadicJetEnclosure.subsetCheck_sound hsub
    (DyadicContact.enclosure_sound
      (DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using g.2.2.2) hy)
      hc (by simpa [hden] using w.bWitness.sound hb hc) pos.2.1 pos.2.2)

theorem ContactWitness.input_positive {input : DyadicInterval 40} {w : ContactWitness}
    (h : w.check input = true) : 0 < input.lo := by
  simp only [ContactWitness.check, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.1.1.1.1.1.1).2.2.2

#print axioms LogWitness.sound
#print axioms EntropyWitness.sound
#print axioms BWitness.sound
#print axioms ContactWitness.sound

end GeneralCK.Certificates.ReflectionFastTranscendental

end


