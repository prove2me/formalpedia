-- Prove2me | Definitions.Def_CK_CKLaneA_Cell
-- name    : CK_CKLaneA_Cell
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:03:25.315024+00:00
-- url     : https://prove2.me/theorems/7e90e556-fb5b-489c-8973-9d2e66db6eae
-- title:
--   Courtade–Kumar proof module `CKLaneA.Cell` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA.Cell` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA.Cell` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA.Cell (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA/Cell.lean)

import Definitions.Def_CK_CKLaneA_Semantics

/-!
# Lane A: reflective cell and tree checkers for `0 < m11` and `0 < actualDetGapCoefficient`

`cellOK` is a `Bool` evaluated by the kernel (`decide +kernel`); `treeOK_sound` is proved once.
-/

namespace CKLaneA.Cell
open GeneralCK GeneralCK.Certificates CKLaneA CKLaneA.Prog Correction

/-- precomputed enclosure of `log 2` at `p = 100` -/
def L2c : DyadicInterval 100 := ⟨878668439483319573618263538034, 878668439483319573618263538068⟩

theorem L2c_eq : (log2Enc (p := 100) 40 : DyadicInterval 100) = L2c := by decide +kernel
theorem L2c_ok : log2OK (p := 100) 40 = true := by decide +kernel
theorem L2c_sound : L2c.Contains (Real.log 2) := L2c_eq ▸ log2Enc_sound L2c_ok

structure CellData where
  ac : ℤ
  zc : ℤ
  ra : ℤ
  rz : ℤ
  hc : ℤ × ℤ
  hw : ℤ × ℤ

local notation "S" => DyadicInterval.scale 100

def floorS (q : ℚ) : ℤ := DyadicInterval.floorDiv (q.num * S) (q.den : ℤ)
def ceilS (q : ℚ) : ℤ := DyadicInterval.ceilDiv (q.num * S) (q.den : ℤ)

def centerRegs (d : CellData) : List (DJ 100) :=
  [DyadicBivariateJetEnclosure.coordinateZ (DI.pt d.zc),
   DyadicBivariateJetEnclosure.coordinateA (DI.pt d.ac)]

def wholeRegs (u0 u1 r0 r1 : ℚ) : List (DJ 100) :=
  [DyadicBivariateJetEnclosure.coordinateZ ⟨floorS r0, ceilS r1⟩,
   DyadicBivariateJetEnclosure.coordinateA ⟨floorS u0, ceilS u1⟩]

def magI (i : DyadicInterval 100) : ℤ := max |i.lo| |i.hi|

def taylorOK (c w : DJ 100) (RA RZ : ℤ) : Bool :=
  decide (0 < 2 * c.value.lo * S ^ 2 - 2 * (magI c.firstA * RA + magI c.firstZ * RZ) * S -
    (magI w.secondAA * RA ^ 2 + 2 * magI w.secondAZ * RA * RZ + magI w.secondZZ * RZ ^ 2))

def geomOK (u0 u1 r0 r1 : ℚ) (d : CellData) : Bool :=
  decide (0 < u0) && decide (u1 < 1 / 2) && decide (0 ≤ r0) && decide (r1 < 1) &&
  decide (0 ≤ d.ra) && decide (0 ≤ d.rz) &&
  decide (u0 * S ≤ d.ac) && decide ((d.ac : ℚ) ≤ u1 * S) &&
  decide (r0 * S ≤ d.zc) && decide ((d.zc : ℚ) ≤ r1 * S) &&
  decide (((d.ac - d.ra : ℤ) : ℚ) ≤ u0 * S) && decide (u1 * S ≤ ((d.ac + d.ra : ℤ) : ℚ)) &&
  decide (((d.zc - d.rz : ℤ) : ℚ) ≤ r0 * S) && decide (r1 * S ≤ ((d.zc + d.rz : ℤ) : ℚ))

def cellOK (u0 u1 r0 r1 : ℚ) (d : CellData) : Bool :=
  geomOK u0 u1 r0 r1 d &&
  match evalProg L2c d.hc prog (centerRegs d), evalProg L2c d.hw prog (wholeRegs u0 u1 r0 r1) with
  | some oc, some ow =>
      taylorOK (oc.getD idxD zeroDJ) (ow.getD idxD zeroDJ) d.ra d.rz &&
      taylorOK (oc.getD idxM zeroDJ) (ow.getD idxM zeroDJ) d.ra d.rz
  | _, _ => false

/-! ## soundness -/

theorem S_pos : (0 : ℝ) < (S : ℝ) := DI.scale_pos' 100

theorem floorS_le (q : ℚ) : ((floorS q : ℤ) : ℝ) ≤ (S : ℝ) * (q : ℝ) := by
  have hd : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.pos
  have h := DyadicInterval.floorDiv_mul_le (q.num * S) hd
  have h' : ((floorS q : ℤ) : ℝ) * (q.den : ℝ) ≤ (q.num : ℝ) * (S : ℝ) := by
    unfold floorS; exact_mod_cast h
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
  have hdr : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  rw [hq, mul_div_assoc', le_div_iff₀ hdr]; linarith

theorem le_ceilS (q : ℚ) : (S : ℝ) * (q : ℝ) ≤ ((ceilS q : ℤ) : ℝ) := by
  have hd : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.pos
  have h := DyadicInterval.le_ceilDiv_mul (q.num * S) hd
  have h' : (q.num : ℝ) * (S : ℝ) ≤ ((ceilS q : ℤ) : ℝ) * (q.den : ℝ) := by
    unfold ceilS; exact_mod_cast h
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
  have hdr : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  rw [hq, mul_div_assoc', div_le_iff₀ hdr]; linarith

theorem magnitude_toReal (i : DyadicInterval 100) :
    i.toReal.magnitude = (magI i : ℝ) / (S : ℝ) := by
  have hs := S_pos
  simp only [JetBounds.Interval.magnitude, DyadicInterval.toReal, magI]
  rw [abs_div, abs_div, abs_of_pos hs]
  push_cast
  rw [max_div_div_right hs.le]

theorem taylorOK_sound {c w : DJ 100} {RA RZ : ℤ} (h : taylorOK c w RA RZ = true) :
    0 < BivariateJetEnclosure.taylorLower c.toReal w.toReal ((RA : ℝ) / S) ((RZ : ℝ) / S) := by
  simp only [taylorOK, decide_eq_true_eq] at h
  have hs := S_pos
  have h' : (0 : ℝ) < 2 * (c.value.lo : ℝ) * (S : ℝ) ^ 2 -
      2 * ((magI c.firstA : ℝ) * RA + (magI c.firstZ : ℝ) * RZ) * S -
      ((magI w.secondAA : ℝ) * RA ^ 2 + 2 * (magI w.secondAZ : ℝ) * RA * RZ + (magI w.secondZZ : ℝ) * RZ ^ 2) := by
    exact_mod_cast h
  simp only [BivariateJetEnclosure.taylorLower, DyadicBivariateJetEnclosure.toReal, magnitude_toReal]
  simp only [DyadicInterval.toReal]
  have key : (c.value.lo : ℝ) / S - (magI c.firstA : ℝ) / S * ((RA : ℝ) / S) -
      (magI c.firstZ : ℝ) / S * ((RZ : ℝ) / S) -
      ((magI w.secondAA : ℝ) / S * ((RA : ℝ) / S) ^ 2 +
        2 * ((magI w.secondAZ : ℝ) / S) * ((RA : ℝ) / S) * ((RZ : ℝ) / S) +
        (magI w.secondZZ : ℝ) / S * ((RZ : ℝ) / S) ^ 2) / 2 =
      (2 * (c.value.lo : ℝ) * (S : ℝ) ^ 2 -
      2 * ((magI c.firstA : ℝ) * RA + (magI c.firstZ : ℝ) * RZ) * S -
      ((magI w.secondAA : ℝ) * RA ^ 2 + 2 * (magI w.secondAZ : ℝ) * RA * RZ +
        (magI w.secondZZ : ℝ) * RZ ^ 2)) / (2 * (S : ℝ) ^ 3) := by
    field_simp; ring
  rw [key]
  positivity

theorem regs_init {L : List (DJ 100)} {b0 b1 : DJ 100} {j0 j1 : BJ} {da dz t : ℝ}
    (hL : L = [b0, b1]) (h0 : b0.Contains j0 t) (h1 : b1.Contains j1 t)
    (s0 : j0.DirectionalSoundAt da dz t) (s1 : j1.DirectionalSoundAt da dz t) :
    Regs L [j0, j1] da dz t := by
  subst hL
  intro i
  match i with
  | 0 => exact ⟨h0, s0⟩
  | 1 => exact ⟨h1, s1⟩
  | i + 2 => exact ⟨by simpa using zeroDJ_contains t, by simpa using zeroBJ_sound da dz t⟩

theorem cellOK_sound {u0 u1 r0 r1 : ℚ} {d : CellData} (h : cellOK u0 u1 r0 r1 d = true)
    {a z : ℝ} (ha0 : (u0 : ℝ) ≤ a) (ha1 : a ≤ u1) (hz0 : (r0 : ℝ) ≤ z) (hz1 : z ≤ r1) :
    0 < r147_D a z ∧ 0 < r170_M a z := by
  simp only [cellOK, Bool.and_eq_true] at h
  obtain ⟨hg, hrest⟩ := h
  simp only [geomOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu0, hu1⟩, hr0⟩, hr1⟩, hra⟩, hrz⟩, hac0⟩, hac1⟩, hzc0⟩, hzc1⟩, hcov0⟩, hcov1⟩,
    hcov2⟩, hcov3⟩ := hg
  have hs := S_pos
  set ac : ℝ := (d.ac : ℝ) / S
  set zc : ℝ := (d.zc : ℝ) / S
  -- real versions of the rational geometry facts
  have cast_le : ∀ {x y : ℚ}, x ≤ y → (x : ℝ) ≤ (y : ℝ) := fun h => by exact_mod_cast h
  have hac0' : (u0 : ℝ) ≤ ac := by
    have := cast_le hac0; push_cast at this; rw [le_div_iff₀ hs]; linarith
  have hac1' : ac ≤ (u1 : ℝ) := by
    have := cast_le hac1; push_cast at this; rw [div_le_iff₀ hs]; linarith
  have hzc0' : (r0 : ℝ) ≤ zc := by
    have := cast_le hzc0; push_cast at this; rw [le_div_iff₀ hs]; linarith
  have hzc1' : zc ≤ (r1 : ℝ) := by
    have := cast_le hzc1; push_cast at this; rw [div_le_iff₀ hs]; linarith
  have hda : |a - ac| ≤ (d.ra : ℝ) / S := by
    have c0 := cast_le hcov0; have c1 := cast_le hcov1
    push_cast at c0 c1
    rw [abs_le]; constructor
    · rw [show -((d.ra : ℝ) / S) = ((d.ac : ℝ) - d.ra) / S - ac by simp only [ac]; ring]
      have : ((d.ac : ℝ) - d.ra) / S ≤ u0 := by rw [div_le_iff₀ hs]; linarith
      linarith
    · rw [show (d.ra : ℝ) / S = ((d.ac : ℝ) + d.ra) / S - ac by simp only [ac]; ring]
      have : (u1 : ℝ) ≤ ((d.ac : ℝ) + d.ra) / S := by rw [le_div_iff₀ hs]; linarith
      linarith
  have hdz : |z - zc| ≤ (d.rz : ℝ) / S := by
    have c0 := cast_le hcov2; have c1 := cast_le hcov3
    push_cast at c0 c1
    rw [abs_le]; constructor
    · rw [show -((d.rz : ℝ) / S) = ((d.zc : ℝ) - d.rz) / S - zc by simp only [zc]; ring]
      have : ((d.zc : ℝ) - d.rz) / S ≤ r0 := by rw [div_le_iff₀ hs]; linarith
      linarith
    · rw [show (d.rz : ℝ) / S = ((d.zc : ℝ) + d.rz) / S - zc by simp only [zc]; ring]
      have : (r1 : ℝ) ≤ ((d.zc : ℝ) + d.rz) / S := by rw [le_div_iff₀ hs]; linarith
      linarith
  have hraR : (0 : ℝ) ≤ (d.ra : ℝ) / S := div_nonneg (by exact_mod_cast hra) hs.le
  have hrzR : (0 : ℝ) ≤ (d.rz : ℝ) / S := div_nonneg (by exact_mod_cast hrz) hs.le
  -- input jets
  set jets : List BJ := [BivariateJet2.affineZ zc z, BivariateJet2.affineA ac a]
  have sZ := BivariateJet2.soundOn_affineZ zc z (a - ac) Set.univ
  have sA := BivariateJet2.soundOn_affineA ac a (z - zc) Set.univ
  have hC : Regs (centerRegs d) jets (a - ac) (z - zc) 0 := by
    apply regs_init rfl
    · apply DyadicBivariateJetEnclosure.contains_coordinateZ
      simpa [zc] using DI.pt_contains (p := 100) d.zc
    · apply DyadicBivariateJetEnclosure.contains_coordinateA
      simpa [ac] using DI.pt_contains (p := 100) d.ac
    · exact sZ 0 trivial
    · exact sA 0 trivial
  have hW : ∀ t ∈ Set.Icc (0:ℝ) 1, Regs (wholeRegs u0 u1 r0 r1) jets (a - ac) (z - zc) t := by
    intro t ht
    have convex : ∀ {c x lo hi : ℝ}, lo ≤ c → c ≤ hi → lo ≤ x → x ≤ hi →
        lo ≤ c + t * (x - c) ∧ c + t * (x - c) ≤ hi := by
      intro c x lo hi h1 h2 h3 h4
      constructor <;> nlinarith [ht.1, ht.2]
    apply regs_init rfl
    · apply DyadicBivariateJetEnclosure.contains_coordinateZ
      obtain ⟨l, r⟩ := convex hzc0' hzc1' hz0 hz1
      constructor
      · exact (floorS_le r0).trans (mul_le_mul_of_nonneg_left l hs.le)
      · exact (mul_le_mul_of_nonneg_left r hs.le).trans (le_ceilS r1)
    · apply DyadicBivariateJetEnclosure.contains_coordinateA
      obtain ⟨l, r⟩ := convex hac0' hac1' ha0 ha1
      constructor
      · exact (floorS_le u0).trans (mul_le_mul_of_nonneg_left l hs.le)
      · exact (mul_le_mul_of_nonneg_left r hs.le).trans (le_ceilS u1)
    · exact sZ t trivial
    · exact sA t trivial
  -- run both programs
  split at hrest
  · next oc ow hoc how =>
    simp only [Bool.and_eq_true] at hrest
    obtain ⟨tD, tM⟩ := hrest
    have RC := evalProg_sound L2c_sound prog hC hoc
    have RW : ∀ t ∈ Set.Icc (0:ℝ) 1, Regs ow (realProg 100 prog jets) (a - ac) (z - zc) t :=
      fun t ht => evalProg_sound L2c_sound prog (hW t ht) how
    have hval : ∀ i, ((realProg 100 prog jets).getD i zeroBJ).value 1 =
        (valProg 100 prog [z, a]).getD i 0 := by
      intro i
      rw [getD_value, realProg_value]
      congr 2
      simp [jets, BivariateJet2.affineZ, BivariateJet2.affineA, BivariateJet2.coordinateZ,
        BivariateJet2.coordinateA]
    have pos : ∀ i, taylorOK (oc.getD i zeroDJ) (ow.getD i zeroDJ) d.ra d.rz = true →
        0 < (valProg 100 prog [z, a]).getD i 0 := by
      intro i hi
      rw [← hval i]
      exact DyadicBivariateJetEnclosure.value_pos_of_separate_taylor
        (fun t ht => (RW t ht i).2) (RC i).1 (fun t ht => (RW t ht i).1)
        hraR hrzR hda hdz (taylorOK_sound hi)
    exact ⟨prog_D a z ▸ pos idxD tD, prog_M a z ▸ pos idxM tM⟩
  · exact absurd hrest (by simp)

/-! ## trees of cells -/

inductive Tree where
  | leaf (d : CellData)
  | su (m : ℚ) (l r : Tree)
  | sr (m : ℚ) (l r : Tree)

def treeOK : ℚ → ℚ → ℚ → ℚ → Tree → Bool
  | u0, u1, r0, r1, .leaf d => cellOK u0 u1 r0 r1 d
  | u0, u1, r0, r1, .su m l r =>
      decide (u0 ≤ m) && decide (m ≤ u1) && treeOK u0 m r0 r1 l && treeOK m u1 r0 r1 r
  | u0, u1, r0, r1, .sr m l r =>
      decide (r0 ≤ m) && decide (m ≤ r1) && treeOK u0 u1 r0 m l && treeOK u0 u1 m r1 r

theorem treeOK_sound : ∀ (T : Tree) {u0 u1 r0 r1 : ℚ}, treeOK u0 u1 r0 r1 T = true →
    ∀ {a z : ℝ}, (u0 : ℝ) ≤ a → a ≤ u1 → (r0 : ℝ) ≤ z → z ≤ r1 →
      0 < r147_D a z ∧ 0 < r170_M a z
  | .leaf d, u0, u1, r0, r1, h, a, z, h1, h2, h3, h4 => cellOK_sound h h1 h2 h3 h4
  | .su m l r, u0, u1, r0, r1, h, a, z, h1, h2, h3, h4 => by
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
    rcases le_total a (m : ℝ) with ham | ham
    · exact treeOK_sound l hl h1 ham h3 h4
    · exact treeOK_sound r hr ham h2 h3 h4
  | .sr m l r, u0, u1, r0, r1, h, a, z, h1, h2, h3, h4 => by
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
    rcases le_total z (m : ℝ) with hzm | hzm
    · exact treeOK_sound l hl h1 h2 h3 hzm
    · exact treeOK_sound r hr h1 h2 hzm h4

/-! ## from the program to the actual correction minors -/

theorem actual_of_prog {a z : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hz : 0 < z) (hz1 : z < 1)
    (hD : 0 < r147_D a z) (hM : 0 < r170_M a z) : ActualRatioMinorsPositive a z := by
  obtain ⟨hd, haw, hw⟩ := geom ha ha2 hz hz1
  rw [D_eq ha ha2 hz hz1] at hD
  rw [M_eq ha ha2 hz hz1] at hM
  have heq := Natural.kernel_eq_actual ha haw hw
  have hk := HighU.kdet_eq_gap_sq_mul_coefficient ha haw hw
  have hkpos : 0 < Natural.kdet a (a + z * (1 / 2 - a)) := by
    rw [hk]; exact mul_pos (by nlinarith) hD
  rw [heq.2] at hkpos
  rw [heq.1] at hM
  have hf0 := H_pos (ha.trans haw) (show a + z * (1 / 2 - a) < 1 by linarith)
  have hf1 : H (a + z * (1 / 2 - a)) < 1 := by
    have h := H_strictMonoOn ⟨(ha.trans haw).le, hw.le⟩ (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2)) hw
    simpa only [H_half] using h
  exact ⟨hM, (Mdet_pos_iff_Kfactored_pos hf0 hf1).mpr hkpos⟩

/-- the conclusion of a checked tree on a rectangle, in the strict actual-minor form -/
theorem actual_of_tree {T : Tree} {u0 u1 r0 r1 : ℚ} (h : treeOK u0 u1 r0 r1 T = true)
    {u rho : ℝ} (hu0 : (u0 : ℝ) ≤ u) (hu1 : u ≤ u1) (hr0 : (r0 : ℝ) ≤ rho) (hr1 : rho ≤ r1)
    (hu : 0 < u) (hu2 : u < 1 / 2) (hr : 0 < rho) (hr1' : rho < 1) :
    ActualRatioMinorsPositive u rho := by
  obtain ⟨hD, hM⟩ := treeOK_sound T h hu0 hu1 hr0 hr1
  exact actual_of_prog hu hu2 hr hr1' hD hM

end CKLaneA.Cell


