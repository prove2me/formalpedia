-- Prove2me | Definitions.Def_CK_E8CompactCertificate
-- name    : CK_E8CompactCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:01:42.081099+00:00
-- url     : https://prove2.me/theorems/96e58555-d1a9-4dfd-b604-f97d750402f2
-- title:
--   Courtade–Kumar proof module `E8CompactCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8CompactCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8CompactCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8CompactCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8CompactCertificate.lean)

import Definitions.Def_CK_E8CompactInterval

-- ===== source module E8CompactCertificate =====
section

namespace GeneralCK.E8RatioMonotonicity
open Certificates DyadicInterval Certificates.E8TAxisStableInterval
open Certificates.E8TAxisStableJet5
open Certificates.E8HistoricalLogConvexityBridge

theorem checked_compactBox_contains {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hp : CompactDenominators i) {a : ℝ} (ha : i.alpha.Contains a) :
    (compactBox i).Contains compactJet a := by
  have hz : i.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound p (-2)) ha)
  have hc1 : (ofInt p 1).Contains (1 : ℝ) := by simpa using ofInt_sound p 1
  exact compactBox_contains ha hz (logBoxCheck_sound hl (add_sound hc1 hz)) hp

theorem stableL_pos_of_checked_cell {p : ℕ} {center whole : Inputs p} {c : ℤ}
    {wec wew : ExpWitness p} {wlc wlw : FastLogBoxWitness}
    (hpoint : center.alpha = ⟨c,c⟩)
    (hgeom : 0 < whole.alpha.lo ∧ whole.alpha.lo ≤ c ∧ c ≤ whole.alpha.hi)
    (hec : expBoxCheck ((ofInt p (-2)).mul center.alpha) center.expNegTwo wec = true)
    (hlc : logBoxCheck ((ofInt p 1).add center.expNegTwo) center.logOnePlusExp wlc = true)
    (hew : expBoxCheck ((ofInt p (-2)).mul whole.alpha) whole.expNegTwo wew = true)
    (hlw : logBoxCheck ((ofInt p 1).add whole.expNegTwo) whole.logOnePlusExp wlw = true)
    (hpc : CompactDenominators center) (hpw : CompactDenominators whole)
    (hcheck : centeredTaylorCheck (compactBox center) (compactBox whole)
      (whole.alpha.sub center.alpha) = true)
    {a : ℝ} (ha : whole.alpha.Contains a) : 0 < stableL a := by
  let mid : ℝ := (c : ℝ) / scale p
  have hscale := scale_cast_pos p
  have hmid : (scale p : ℝ) * mid = c := by
    dsimp [mid]
    field_simp
  have hc : center.alpha.Contains mid := by
    rw [hpoint]
    exact ⟨hmid.ge, hmid.le⟩
  have hwc : whole.alpha.Contains mid := by
    change (whole.alpha.lo : ℝ) ≤ (scale p : ℝ) * mid ∧
      (scale p : ℝ) * mid ≤ whole.alpha.hi
    rw [hmid]
    exact ⟨by exact_mod_cast hgeom.2.1, by exact_mod_cast hgeom.2.2⟩
  have hpos : ∀ x : ℝ, whole.alpha.Contains x → 0 < x := by
    intro x hx
    have hlo : (0 : ℝ) < whole.alpha.lo := by exact_mod_cast hgeom.1
    exact (mul_pos_iff_of_pos_left hscale).mp (hlo.trans_le hx.1)
  exact stableL_pos_of_centered_enclosures hwc ha hpos (sub_sound ha hc)
    (checked_compactBox_contains hec hlc hpc hc)
    (fun x hx => checked_compactBox_contains hew hlw hpw hx) hcheck

def PositiveInterval (p : ℕ) (lo hi : ℤ) : Prop :=
  ∀ a : ℝ, (⟨lo,hi⟩ : DyadicInterval p).Contains a → 0 < stableL a

theorem PositiveInterval.split {p : ℕ} {lo mid hi : ℤ}
    (hl : PositiveInterval p lo mid) (hr : PositiveInterval p mid hi) :
    PositiveInterval p lo hi := by
  intro a ha
  by_cases hm : (scale p : ℝ) * a ≤ mid
  · exact hl a ⟨ha.1,hm⟩
  · exact hr a ⟨(not_le.mp hm).le,ha.2⟩

#print axioms checked_compactBox_contains
#print axioms stableL_pos_of_checked_cell
#print axioms PositiveInterval.split
end GeneralCK.E8RatioMonotonicity

end


