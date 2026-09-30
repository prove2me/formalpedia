-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactCell
-- name    : CK_CKLaneC3_CompactCell
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:48:26.196145+00:00
-- url     : https://prove2.me/theorems/574db95d-eef2-4382-8022-f1683eb73a65
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactCell` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactCell` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactCell` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactCell (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactCell.lean)

import Definitions.Def_CK_CKLaneC3_SlopeChain
import Definitions.Def_CK_GeneralCK_Certificates_E8CompactDeltaDirectionalExpansion

-- ===== source module CKLaneC3.CompactCell =====
section

/-!
# Lane C3 — cubic Taylor cell certificates for the actual E8 determinant

`CellW.check T w = true` (with a valid slope table `T`) proves
`0 < e8Delta e8Q s t` at every point of the closed rational rectangle of `w`.
The argument is the cubic Lagrange bound along the segment from the cell centre
(`E8CompactAnchorTaylor3.lower_of_third_bound`), with centre coefficients from
Taylor-form point jets and third-order remainder coefficients from Taylor-form
jets on the four slope intervals of the cell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.CompactCell

open Set GeneralCK GeneralCK.Certificates DyadicInterval
open E8TAxisDeltaDirectionalJet E8CompactAnchorDeltaJet E8CompactAnchorInterval
open E8CompactDeltaDirectionalExpansion E8TAxisMixedCoefficients
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain

noncomputable def lowerBound (b : DyadicInterval P) : ℝ := (b.lo : ℝ) / (scale P : ℝ)

theorem lowerBound_le {b : DyadicInterval P} {x : ℝ} (h : b.Contains x) : lowerBound b ≤ x :=
  (div_le_iff₀ (scale_cast_pos P)).mpr (by simpa only [mul_comm] using h.1)

theorem lowerBound_contains {b : DyadicInterval P} (ho : b.lo ≤ b.hi) :
    b.Contains (lowerBound b) := by
  have he : (scale P : ℝ) * lowerBound b = b.lo := by
    unfold lowerBound
    field_simp [(scale_cast_pos P).ne']
  change (b.lo : ℝ) ≤ (scale P : ℝ) * lowerBound b ∧ (scale P : ℝ) * lowerBound b ≤ b.hi
  rw [he]
  exact ⟨le_rfl, by exact_mod_cast ho⟩

def offBox (lo hi : ℚ) : DyadicInterval P := ⟨⌊(scale P : ℚ) * lo⌋, ⌈(scale P : ℚ) * hi⌉⟩

theorem offBox_contains {lo hi : ℚ} {x : ℝ} (h0 : (lo : ℝ) ≤ x) (h1 : x ≤ hi) :
    (offBox lo hi).Contains x := by
  have hs := scale_cast_pos P
  have hfl : ((⌊(scale P : ℚ) * lo⌋ : ℤ) : ℝ) ≤ (scale P : ℝ) * lo := by
    have := Int.floor_le ((scale P : ℚ) * lo)
    exact_mod_cast this
  have hce : (scale P : ℝ) * hi ≤ ((⌈(scale P : ℚ) * hi⌉ : ℤ) : ℝ) := by
    have := Int.le_ceil ((scale P : ℚ) * hi)
    exact_mod_cast this
  constructor
  · simp only [offBox]; nlinarith
  · simp only [offBox]; nlinarith

def half : DyadicInterval P := (ofInt P 2).recip
def sixth : DyadicInterval P := (ofInt P 6).recip

theorem half_contains : half.Contains (1 / 2 : ℝ) := by
  simpa only [half, one_div, Int.cast_ofNat] using recip_sound
    (show 0 < (ofInt P 2).lo by decide +kernel) (ofInt_sound P 2)

theorem sixth_contains : sixth.Contains (1 / 6 : ℝ) := by
  simpa only [sixth, one_div, Int.cast_ofNat] using recip_sound
    (show 0 < (ofInt P 6).lo by decide +kernel) (ofInt_sound P 6)

def second (pcS pcT : DyadicJet5Enclosure P) (pc11 offS offT : DyadicInterval P) :
    DyadicInterval P :=
  (((pcS.d2.mul offS).mul offS).add ((((ofInt P 2).mul pc11).mul offS).mul offT)).add
    ((pcT.d2.mul offT).mul offT)

def remainder (bbS bbT : DyadicJet5Enclosure P) (bb21 bb12 offS offT : DyadicInterval P) :
    DyadicInterval P :=
  (((((bbS.d3.mul offS).mul offS).mul offS).add
    (((((ofInt P 3).mul bb21).mul offS).mul offS).mul offT)).add
    (((((ofInt P 3).mul bb12).mul offS).mul offT).mul offT)).add
    (((bbT.d3.mul offT).mul offT).mul offT)

def replay (pc bb : Boxes P) (offS offT : DyadicInterval P) : DyadicInterval P :=
  ((((pc.direction 1 0).d0.add ((pc.direction 1 0).d1.mul offS)).add
    ((pc.direction 0 1).d1.mul offT)).add
    ((second (pc.direction 1 0) (pc.direction 0 1) (pc.coeff 1 1) offS offT).mul half)).add
    ((remainder (bb.direction 1 0) (bb.direction 0 1) (bb.coeff 2 1) (bb.coeff 1 2)
      offS offT).mul sixth)

theorem second_contains {pcS pcT : DyadicJet5Enclosure P} {pc11 offS offT : DyadicInterval P}
    {s2 st t2 ds dt : ℝ}
    (hs2 : pcS.d2.Contains s2) (hst : pc11.Contains st) (ht2 : pcT.d2.Contains t2)
    (hs : offS.Contains ds) (ht : offT.Contains dt) :
    (second pcS pcT pc11 offS offT).Contains (s2 * ds ^ 2 + 2 * st * ds * dt + t2 * dt ^ 2) := by
  unfold second
  convert add_sound (add_sound (mul_sound (mul_sound hs2 hs) hs)
    (mul_sound (mul_sound (mul_sound (ofInt_sound P 2) hst) hs) ht))
    (mul_sound (mul_sound ht2 ht) ht) using 1
  push_cast
  ring

theorem remainder_contains {bbS bbT : DyadicJet5Enclosure P} {bb21 bb12 offS offT : DyadicInterval P}
    {s3 s2t st2 t3 ds dt : ℝ}
    (hs3 : bbS.d3.Contains s3) (hs2t : bb21.Contains s2t)
    (hst2 : bb12.Contains st2) (ht3 : bbT.d3.Contains t3)
    (hs : offS.Contains ds) (ht : offT.Contains dt) :
    (remainder bbS bbT bb21 bb12 offS offT).Contains (s3 * ds ^ 3 + 3 * s2t * ds ^ 2 * dt +
      3 * st2 * ds * dt ^ 2 + t3 * dt ^ 3) := by
  unfold remainder
  convert add_sound (add_sound (add_sound
    (mul_sound (mul_sound (mul_sound hs3 hs) hs) hs)
    (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound P 3) hs2t) hs) hs) ht))
    (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound P 3) hst2) hs) ht) ht))
    (mul_sound (mul_sound (mul_sound ht3 ht) ht) ht) using 1
  push_cast
  ring

/-- The generic cubic cell theorem. -/
theorem cell_positive {pc bb : Boxes P} {offS offT : DyadicInterval P} {cS cT : ℝ}
    {InC : ℝ → ℝ → Prop}
    (hpc : pc.ContainsAt cS cT)
    (hbb : ∀ s t, InC s t → bb.ContainsAt s t)
    (hrange : ∀ s t, InC s t → InputsInRange s t)
    (hoff : ∀ s t, InC s t → offS.Contains (s - cS) ∧ offT.Contains (t - cT))
    (hseg : ∀ s t v, InC s t → v ∈ Icc (0 : ℝ) 1 →
      InC (cS + (s - cS) * v) (cT + (t - cT) * v))
    (hpos : (replay pc bb offS offT).positiveCheck = true) :
    ∀ s t, InC s t → 0 < e8Delta e8Q s t := by
  intro s t h
  have hds := (hoff s t h).1
  have hdt := (hoff s t h).2
  have hj : Sound4On (deltaJet cS cT (s - cS) (t - cT)) (Icc (0 : ℝ) 1) := by
    apply deltaJet_sound4On
    intro v hv
    exact hrange _ _ (hseg s t v h hv)
  set rem := remainder (bb.direction 1 0) (bb.direction 0 1) (bb.coeff 2 1) (bb.coeff 1 2)
    offS offT with hrem
  have hremc : ∀ v ∈ Ioo (0 : ℝ) 1,
      rem.Contains ((deltaJet cS cT (s - cS) (t - cT)).d3 v) := by
    intro v hv
    have hpt := hseg s t v h ⟨hv.1.le, hv.2.le⟩
    have hbbp := hbb _ _ hpt
    have hS : (bb.direction 1 0).Contains
        (deltaJet (cS + (s - cS) * v) (cT + (t - cT) * v) 1 0) 0 := by
      simpa only [Int.cast_zero, Int.cast_one] using Boxes.directionAt_contains 1 0 hbbp
    have hT : (bb.direction 0 1).Contains
        (deltaJet (cS + (s - cS) * v) (cT + (t - cT) * v) 0 1) 0 := by
      simpa only [Int.cast_zero, Int.cast_one] using Boxes.directionAt_contains 0 1 hbbp
    have hc := remainder_contains hS.2.2.2.1 (Boxes.coeff_contains hbbp 2 1)
      (Boxes.coeff_contains hbbp 1 2) hT.2.2.2.1 hds hdt
    rw [deltaJet_directional_d3_translate, deltaJet_directional_d3_expansion]
    exact hc
  have hR : ∀ v ∈ Ioo (0 : ℝ) 1,
      lowerBound rem ≤ (deltaJet cS cT (s - cS) (t - cT)).d3 v :=
    fun v hv => lowerBound_le (hremc v hv)
  have hordered : rem.lo ≤ rem.hi := by
    have hc := hremc (1 / 2) ⟨by norm_num, by norm_num⟩
    have h1 := hc.1
    have h2 := hc.2
    exact_mod_cast h1.trans h2
  have hTaylor := E8CompactAnchorTaylor3.lower_of_third_bound
    (fun v hv => (hj v hv).1) (fun v hv => (hj v hv).2.1) (fun v hv => (hj v hv).2.2.1) hR
  -- centre coefficients
  have hcS : (pc.direction 1 0).Contains (deltaJet cS cT 1 0) 0 := by
    simpa only [Int.cast_zero, Int.cast_one] using Boxes.directionAt_contains 1 0 hpc
  have hcT : (pc.direction 0 1).Contains (deltaJet cS cT 0 1) 0 := by
    simpa only [Int.cast_zero, Int.cast_one] using Boxes.directionAt_contains 0 1 hpc
  have hc11 := Boxes.coeff_contains hpc 1 1
  have hsec := second_contains hcS.2.2.1 hc11 hcT.2.2.1 hds hdt
  have hrep : (replay pc bb offS offT).Contains
      ((deltaJet cS cT 1 0).d0 0 + ((deltaJet cS cT 1 0).d1 0 * (s - cS) +
        (deltaJet cS cT 0 1).d1 0 * (t - cT)) +
        ((deltaJet cS cT 1 0).d2 0 * (s - cS) ^ 2 + 2 * mixed qJet cS cT 1 1 * (s - cS) * (t - cT) +
          (deltaJet cS cT 0 1).d2 0 * (t - cT) ^ 2) / 2 + lowerBound rem / 6) := by
    unfold replay
    rw [← hrem]
    convert add_sound (add_sound (add_sound (add_sound hcS.1 (mul_sound hcS.2.1 hds))
      (mul_sound hcT.2.1 hdt)) (mul_sound hsec half_contains))
      (mul_sound (lowerBound_contains hordered) sixth_contains) using 1
    ring
  have hpos' := positiveCheck_sound hpos hrep
  have hzero : (deltaJet cS cT (s - cS) (t - cT)).d0 0 = (deltaJet cS cT 1 0).d0 0 := by
    simp only [deltaJet_d0_eq_e8Delta, mul_zero, add_zero]
  have hend : (deltaJet cS cT (s - cS) (t - cT)).d0 1 = e8Delta e8Q s t := by
    rw [deltaJet_d0_eq_e8Delta]
    congr 1 <;> ring
  rw [deltaJet_directional_d1_expansion, deltaJet_directional_d2_expansion, hzero, hend]
    at hTaylor
  linarith

/-! ## Executable cell witnesses -/

structure CellW where
  s0 : ℚ
  s1 : ℚ
  t0 : ℚ
  t1 : ℚ
  cS : ℚ
  cT : ℚ
  ra : ℕ × ℕ
  rb : ℕ × ℕ
  rc : ℕ × ℕ
  rd : ℕ × ℕ
  wa : List (ℕ × ℕ)
  wb : List (ℕ × ℕ)
  wc : List (ℕ × ℕ)
  wd : List (ℕ × ℕ)

def CellW.InCell (w : CellW) (s t : ℝ) : Prop :=
  (w.s0 : ℝ) ≤ s ∧ s ≤ w.s1 ∧ (w.t0 : ℝ) ≤ t ∧ t ≤ w.t1

def CellW.boxes (T : List (List Piece)) (w : CellW) : Option (Boxes P × Boxes P) :=
  match chainJet T [w.ra] w.cT w.cT, chainJet T [w.rb] (2 * w.cS + w.cT) (2 * w.cS + w.cT),
      chainJet T [w.rc] (w.cS + w.cT) (w.cS + w.cT), chainJet T [w.rd] w.cS w.cS,
      chainJet T w.wa w.t0 w.t1, chainJet T w.wb (2 * w.s0 + w.t0) (2 * w.s1 + w.t1),
      chainJet T w.wc (w.s0 + w.t0) (w.s1 + w.t1), chainJet T w.wd w.s0 w.s1 with
  | some a, some b, some c, some d, some a', some b', some c', some d' =>
    some (⟨a, b, c, d⟩, ⟨a', b', c', d'⟩)
  | _, _, _, _, _, _, _, _ => none

def CellW.check (T : List (List Piece)) (w : CellW) : Bool :=
  decide (w.s0 ≤ w.cS) && decide (w.cS ≤ w.s1) && decide (w.t0 ≤ w.cT) && decide (w.cT ≤ w.t1) &&
  (match w.boxes T with
   | some (pc, bb) =>
     (replay pc bb (offBox (w.s0 - w.cS) (w.s1 - w.cS))
       (offBox (w.t0 - w.cT) (w.t1 - w.cT))).positiveCheck
   | none => false)

theorem CellW.check_sound {T : List (List Piece)} (hT : TableValid T) {w : CellW}
    (h : w.check T = true) : ∀ s t, w.InCell s t → 0 < e8Delta e8Q s t := by
  simp only [CellW.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsc0, hsc1⟩, htc0⟩, htc1⟩, hb⟩ := h
  cases hbx : w.boxes T with
  | none => rw [hbx] at hb; exact absurd hb (by simp)
  | some bx =>
    obtain ⟨pc, bb⟩ := bx
    rw [hbx] at hb
    simp only at hb
    -- unpack the eight chains
    unfold CellW.boxes at hbx
    split at hbx
    · rename_i a b c d a' b' c' d' ha hb' hc hd ha' hb2 hc' hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbx
      obtain ⟨rfl, rfl⟩ := hbx
      have hsc0R : (w.s0 : ℝ) ≤ w.cS := by exact_mod_cast hsc0
      have hsc1R : (w.cS : ℝ) ≤ w.s1 := by exact_mod_cast hsc1
      have htc0R : (w.t0 : ℝ) ≤ w.cT := by exact_mod_cast htc0
      have htc1R : (w.cT : ℝ) ≤ w.t1 := by exact_mod_cast htc1
      have cA := chainJet_sound hT _ _ _ _ ha (w.cT : ℝ) (by push_cast; linarith) (by push_cast; linarith)
      have cB := chainJet_sound hT _ _ _ _ hb' (2 * (w.cS : ℝ) + w.cT) (by push_cast; linarith)
        (by push_cast; linarith)
      have cC := chainJet_sound hT _ _ _ _ hc ((w.cS : ℝ) + w.cT) (by push_cast; linarith)
        (by push_cast; linarith)
      have cD := chainJet_sound hT _ _ _ _ hd (w.cS : ℝ) (by push_cast; linarith) (by push_cast; linarith)
      apply cell_positive (pc := ⟨a, b, c, d⟩) (bb := ⟨a', b', c', d'⟩) (cS := (w.cS : ℝ))
        (cT := (w.cT : ℝ)) (InC := w.InCell) ⟨cA.1, cB.1, cC.1, cD.1⟩
      · intro s t hin
        obtain ⟨h1, h2, h3, h4⟩ := hin
        exact ⟨(chainJet_sound hT _ _ _ _ ha' t (by push_cast; linarith) (by push_cast; linarith)).1,
          (chainJet_sound hT _ _ _ _ hb2 (2 * s + t) (by push_cast; linarith)
            (by push_cast; linarith)).1,
          (chainJet_sound hT _ _ _ _ hc' (s + t) (by push_cast; linarith) (by push_cast; linarith)).1,
          (chainJet_sound hT _ _ _ _ hd' s (by push_cast; linarith) (by push_cast; linarith)).1⟩
      · intro s t hin
        obtain ⟨h1, h2, h3, h4⟩ := hin
        exact ⟨(chainJet_sound hT _ _ _ _ ha' t (by push_cast; linarith) (by push_cast; linarith)).2,
          (chainJet_sound hT _ _ _ _ hb2 (2 * s + t) (by push_cast; linarith)
            (by push_cast; linarith)).2,
          (chainJet_sound hT _ _ _ _ hc' (s + t) (by push_cast; linarith) (by push_cast; linarith)).2,
          (chainJet_sound hT _ _ _ _ hd' s (by push_cast; linarith) (by push_cast; linarith)).2⟩
      · intro s t hin
        obtain ⟨h1, h2, h3, h4⟩ := hin
        exact ⟨offBox_contains (lo := w.s0 - w.cS) (hi := w.s1 - w.cS)
            (by push_cast; linarith) (by push_cast; linarith),
          offBox_contains (lo := w.t0 - w.cT) (hi := w.t1 - w.cT)
            (by push_cast; linarith) (by push_cast; linarith)⟩
      · intro s t v hin hv
        obtain ⟨h1, h2, h3, h4⟩ := hin
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hv.1, hv.2]
      · exact hb
    · exact absurd hbx (by simp)

#print axioms cell_positive
#print axioms CellW.check_sound

end CKLaneC3.CompactCell

end


