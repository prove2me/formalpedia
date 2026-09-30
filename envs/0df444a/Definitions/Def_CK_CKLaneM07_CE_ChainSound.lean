-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_ChainSound
-- name    : CK_CKLaneM07_CE_ChainSound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:44:05.517568+00:00
-- url     : https://prove2.me/theorems/5279eed4-4582-401b-aa34-e117beadd855
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.ChainSound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.ChainSound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.ChainSound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.ChainSound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/ChainSound.lean)

import Definitions.Def_CK_CKLaneM07_CE_Model

-- ===== source module CKLaneM07.CE.ChainSound =====
section

/-!
# Lane M07 / CE-stat: soundness of chain v2, part B (stages and the four modes)

Pointwise at a fixed `(x, y) ∈ [-1,1]²`: if the real chart values satisfy their defining residual
equations (`RealPt.Valid`) and the cell inputs are enclosed, every accepted stage check propagates
enclosures; the final checks give
* mode 0: `0 < G` (natural-log pure gap),
* mode 1: `t_C < b`,
* mode 2: `a + c ≤ 1/10000`,
* mode 3: `1 ≤ λ`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open GeneralCK Set CKLaneD

/-! ## the real chart point -/

structure RealPt where
  A : ℝ
  tC : ℝ
  tA : ℝ
  tB : ℝ
  a : ℝ
  b : ℝ
  tD : ℝ
  uE : ℝ

namespace RealPt

variable (R : RealPt)

noncomputable def B : ℝ := Real.log 2 * (1 / LnR R.tB)
noncomputable def lam : ℝ := (R.B - R.A) * LnR R.tC * (1 / 2 * (1 / Real.log 2))
noncomputable def E : ℝ := (1 - 2 * R.a) * (1 / (R.A + R.B))
noncomputable def c : ℝ := 1 / 2 * (1 - R.E * (R.B - R.A))

/-- the pure gap in natural-log units, as a function of the chart values -/
noncomputable def G : ℝ :=
  -((R.b - R.a) * JnR R.tD) + 1 / 2 * (-(R.b - R.a) * (JnR R.b - JnR R.a)) +
    -((1 - 2 * R.uE) * JnR R.uE) + 1 / 2 * ((1 - 2 * R.b) * JnR R.b) + (R.c - R.a) * JnR R.tA +
    (1 - R.a - R.c) * JnR R.tB + -(1 / 2 * ((1 - 2 * R.c) * JnR R.tC))

/-- the defining residual equations of the chart values -/
structure Valid : Prop where
  hA : 0 < R.A
  htA : 0 < R.tA ∧ R.tA < 1 / 2
  eA : R.A * LnR R.tA - Real.log 2 = 0
  htB : 0 < R.tB ∧ R.tB < 1 / 2
  eB : UpsR R.tB - (UpsR R.tA + UpsR R.tC) = 0
  ha : 0 < R.a ∧ R.a < 1 / 2
  hAB : 0 < R.A + R.B
  ea : LnR R.a * (R.A + R.B) - 2 * (1 - R.lam) * Real.log 2 = 0
  hb : 0 < R.b ∧ R.b < 1 / 2
  eb : HnR R.b - R.lam * R.E * Real.log 2 = 0
  hba : 0 < R.b - R.a
  htD : 0 < R.tD ∧ R.tD < 1 / 2
  eD : (R.b - R.a) * LnR R.tD - R.E * Real.log 2 = 0
  huE : 0 < R.uE ∧ R.uE < 1 / 2
  eU : HnR R.uE - 1 / 2 * (R.E * Real.log 2) = 0

end RealPt

/-! ## stages -/

section stages

variable {K : ℕ} {cl : CellV} {w : WitV} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
include hx hy

theorem stageA {A tA : ℝ} (hA : EnclAt x y A cl.A) (hA0 : 0 < A)
    (htA : 0 < tA ∧ tA < 1 / 2) (eA : A * LnR tA - Real.log 2 = 0) (h : V2.chkA K cl w = true) :
    EnclAt x y tA w.sA.z ∧ FnsE x y tA w.sA.F := by
  unfold V2.chkA at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hP, hM⟩, hB⟩, hrp⟩, hrm⟩, hinc⟩ := h
  obtain ⟨-, -, hFp⟩ := site_P hx hy hP
  obtain ⟨hzm0, -, hFm⟩ := site_M hx hy hM
  have hzp := site_band hx hy hB
  obtain ⟨-, hrdp⟩ := recOK_sound hx hy (hFp.den hx hy) hrp
  obtain ⟨-, hrdm⟩ := recOK_sound hx hy (hFm.den hx hy) hrm
  have hRp := (EnclAt.mul hx hy K hA (hFp.LnW hx hy K hrdp)).sub (encl_ln2 x y)
  have hRm := (EnclAt.mul hx hy K hA (hFm.LnW hx hy K hrdm)).sub (encl_ln2 x y)
  unfold incrOK at hinc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hinc
  have hp := pos_of_lo hx hy hRp hinc.1
  have hm := neg_of_hi hx hy hRm hinc.2
  have hmono : MonotoneOn (fun z => A * LnR z - Real.log 2) (Ioo 0 (1 / 2)) := by
    intro u hu v hv huv
    have := mul_le_mul_of_nonneg_left (LnR_mono hu hv huv) hA0.le
    simp only
    linarith
  exact site_encl hx hy hP hM (bracket_incr hmono htA.1 htA.2 eA hzm0 (zm_le_zp x y _) hzp hm hp)

theorem stageC {tC : ℝ} (hT : EnclAt x y tC cl.tC) (h : V2.chkC K cl w = true) :
    FnsE x y tC (V2.FC cl w) := by
  unfold V2.chkC at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, hl⟩ := logOK_sound hx hy hT h.1
  obtain ⟨-, hl1⟩ := logOK_sound hx hy ((encl_one x y).sub hT) h.2
  exact ⟨hT, hl, hl1⟩

theorem stageU {tA tC : ℝ} (hFA : FnsE x y tA w.sA.F) (hFC : FnsE x y tC (V2.FC cl w))
    (h : V2.chkU K cl w = true) : EnclAt x y (UpsR tA + UpsR tC) (V2.UAC K cl w) := by
  unfold V2.chkU at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h1⟩ := recOK_sound hx hy (hFA.qarg hx hy K) h.1
  obtain ⟨-, h2⟩ := recOK_sound hx hy (hFC.qarg hx hy K) h.2
  exact (hFA.UpsW hx hy K h1).add (hFC.UpsW hx hy K h2)

theorem stageB {tA tC tB : ℝ} (hUAC : EnclAt x y (UpsR tA + UpsR tC) (V2.UAC K cl w))
    (htB : 0 < tB ∧ tB < 1 / 2) (eB : UpsR tB - (UpsR tA + UpsR tC) = 0)
    (h : V2.chkB K cl w = true) : EnclAt x y tB w.sB.z ∧ FnsE x y tB w.sB.F := by
  unfold V2.chkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hP, hM⟩, hB⟩, hrp⟩, hrm⟩, hdec⟩ := h
  obtain ⟨-, -, hFp⟩ := site_P hx hy hP
  obtain ⟨hzm0, -, hFm⟩ := site_M hx hy hM
  have hzp := site_band hx hy hB
  obtain ⟨-, hrqp⟩ := recOK_sound hx hy (hFp.qarg hx hy K) hrp
  obtain ⟨-, hrqm⟩ := recOK_sound hx hy (hFm.qarg hx hy K) hrm
  have hRp := (hFp.UpsW hx hy K hrqp).sub hUAC
  have hRm := (hFm.UpsW hx hy K hrqm).sub hUAC
  unfold decrOK at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  have hp := neg_of_hi hx hy hRp hdec.1
  have hm := pos_of_lo hx hy hRm hdec.2
  have hanti : AntitoneOn (fun z => UpsR z - (UpsR tA + UpsR tC)) (Ioo 0 (1 / 2)) := by
    intro u hu v hv huv
    have := UpsR_anti hu hv huv
    simp only
    linarith
  exact site_encl hx hy hP hM (bracket_decr hanti htB.1 htB.2 eB hzm0 (zm_le_zp x y _) hzp hm hp)

theorem stageL {A tB tC : ℝ} (hA : EnclAt x y A cl.A) (hFB : FnsE x y tB w.sB.F)
    (hFC : FnsE x y tC (V2.FC cl w)) (h : V2.chkL K cl w = true) :
    EnclAt x y (Real.log 2 * (1 / LnR tB)) (V2.B K w) ∧
      EnclAt x y ((Real.log 2 * (1 / LnR tB) - A) * LnR tC * (1 / 2 * (1 / Real.log 2)))
        (V2.lam K cl w) := by
  unfold V2.chkL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨-, hrd⟩ := recOK_sound hx hy (hFB.den hx hy) h1
  have hLB : EnclAt x y (LnR tB) (V2.LB K w) := hFB.LnW hx hy K hrd
  obtain ⟨-, hrB⟩ := recOK_sound hx hy hLB h2
  have hB : EnclAt x y (Real.log 2 * (1 / LnR tB)) (V2.B K w) :=
    EnclAt.mul hx hy K (encl_ln2 x y) hrB
  obtain ⟨-, hrC⟩ := recOK_sound hx hy (hFC.den hx hy) h3
  have hLC : EnclAt x y (LnR tC) (V2.LnC K cl w) := hFC.LnW hx hy K hrC
  obtain ⟨-, hrl⟩ := recOK_sound hx hy (encl_ln2 x y) h4
  exact ⟨hB, EnclAt.mul hx hy K (EnclAt.mul hx hy K (hB.sub hA) hLC) (EnclAt.half hx hy hrl)⟩

theorem stagea {AB rhs a : ℝ} (hAB : EnclAt x y AB (V2.AB K cl w))
    (hrhs : EnclAt x y rhs (V2.rhsA K cl w)) (hABpos : 0 < AB) (ha : 0 < a ∧ a < 1 / 2)
    (ea : LnR a * AB - rhs = 0) (h : V2.chka K cl w = true) :
    EnclAt x y a w.sa.z ∧ a < zpR x y w.sa ∧ zpR x y w.sa < 1 / 2 ∧
      FnsE x y (zpR x y w.sa) w.sa.Fp := by
  unfold V2.chka at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hP, hB⟩, hrp⟩, hpos⟩, hrest⟩ := h
  obtain ⟨hzp0, -, hFp⟩ := site_P hx hy hP
  have hzp := site_band hx hy hB
  obtain ⟨-, hrdp⟩ := recOK_sound hx hy (hFp.den hx hy) hrp
  have hRp := (EnclAt.mul hx hy K (hFp.LnW hx hy K hrdp) hAB).sub hrhs
  have hp := pos_of_lo hx hy hRp hpos
  have hmono : MonotoneOn (fun z => LnR z * AB - rhs) (Ioo 0 (1 / 2)) := by
    intro u hu v hv huv
    have := mul_le_mul_of_nonneg_right (LnR_mono hu hv huv) hABpos.le
    simp only
    linarith
  have hlt : a < zpR x y w.sa := by
    by_contra hc
    push Not at hc
    have := hmono ⟨hzp0, hzp⟩ ⟨ha.1, ha.2⟩ hc
    simp only at this
    linarith
  have hgt : zmR x y w.sa < a := by
    cases he : w.edge
    · simp only [he, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hrest
      obtain ⟨⟨hM, hrm⟩, hneg⟩ := hrest
      obtain ⟨hzm0, -, hFm⟩ := site_M hx hy hM
      obtain ⟨-, hrdm⟩ := recOK_sound hx hy (hFm.den hx hy) hrm
      have hRm := (EnclAt.mul hx hy K (hFm.LnW hx hy K hrdm) hAB).sub hrhs
      have hm := neg_of_hi hx hy hRm hneg
      exact (bracket_incr hmono ha.1 ha.2 ea hzm0 (zm_le_zp x y _) hzp hm hp).1
    · simp only [he, ↓reduceIte, decide_eq_true_eq] at hrest
      exact lt_of_le_of_lt (site_dn_nonpos hx hy hrest) ha.1
  exact ⟨encl_z_of_bracket ⟨hgt, hlt⟩, hlt, hzp, hFp⟩

theorem stageE {AB a : ℝ} (hAB : EnclAt x y AB (V2.AB K cl w)) (ha : EnclAt x y a w.sa.z)
    (h : V2.chkE K cl w = true) : EnclAt x y ((1 - 2 * a) * (1 / AB)) (V2.E K w) := by
  unfold V2.chkE at h
  obtain ⟨-, hr⟩ := recOK_sound hx hy hAB h
  exact EnclAt.mul hx hy K ((encl_one x y).sub (EnclAt.two hx hy ha)) hr

/-- an `Hn`-residual site -/
theorem siteHn {s : Site} {T : TMI} {q z : ℝ} (hq : EnclAt x y q T) (hz : 0 < z ∧ z < 1 / 2)
    (ez : HnR z - q = 0) (hP : s.logsP K = true) (hM : s.logsM K = true) (hB : s.band = true)
    (hinc : incrOK ((s.Fp.Hn K).sub T) ((s.Fm.Hn K).sub T) = true) :
    EnclAt x y z s.z ∧ FnsE x y z s.F := by
  obtain ⟨-, -, hFp⟩ := site_P hx hy hP
  obtain ⟨hzm0, -, hFm⟩ := site_M hx hy hM
  have hzp := site_band hx hy hB
  have hRp := (hFp.Hn hx hy K).sub hq
  have hRm := (hFm.Hn hx hy K).sub hq
  unfold incrOK at hinc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hinc
  have hp := pos_of_lo hx hy hRp hinc.1
  have hm := neg_of_hi hx hy hRm hinc.2
  have hmono : MonotoneOn (fun z => HnR z - q) (Ioo 0 (1 / 2)) := by
    intro u hu v hv huv
    have := HnR_mono hu hv huv
    simp only
    linarith
  exact site_encl hx hy hP hM (bracket_incr hmono hz.1 hz.2 ez hzm0 (zm_le_zp x y _) hzp hm hp)

theorem stageb {q b : ℝ} (hq : EnclAt x y q (V2.lamEln2 K cl w)) (hb : 0 < b ∧ b < 1 / 2)
    (eb : HnR b - q = 0) (h : V2.chkb K cl w = true) : EnclAt x y b w.sb.z ∧ FnsE x y b w.sb.F := by
  unfold V2.chkb at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hP, hM⟩, hB⟩, hinc⟩ := h
  exact siteHn hx hy hq hb eb hP hM hB hinc

theorem stageUE {q u : ℝ} (hq : EnclAt x y q (V2.hEln2 K w)) (hu : 0 < u ∧ u < 1 / 2)
    (eu : HnR u - q = 0) (h : V2.chkUE K w = true) : EnclAt x y u w.sU.z ∧ FnsE x y u w.sU.F := by
  unfold V2.chkUE at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hP, hM⟩, hB⟩, hinc⟩ := h
  exact siteHn hx hy hq hu eu hP hM hB hinc

theorem stageD {m q tD : ℝ} (hm : EnclAt x y m (V2.bma w)) (hq : EnclAt x y q (V2.Eln2 K w))
    (hm0 : 0 < m) (htD : 0 < tD ∧ tD < 1 / 2) (eD : m * LnR tD - q = 0) (h : V2.chkD K w = true) :
    EnclAt x y tD w.sD.z ∧ FnsE x y tD w.sD.F := by
  unfold V2.chkD at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hP, hM⟩, hB⟩, hrp⟩, hrm⟩, hinc⟩ := h
  obtain ⟨-, -, hFp⟩ := site_P hx hy hP
  obtain ⟨hzm0, -, hFm⟩ := site_M hx hy hM
  have hzp := site_band hx hy hB
  obtain ⟨-, hrdp⟩ := recOK_sound hx hy (hFp.den hx hy) hrp
  obtain ⟨-, hrdm⟩ := recOK_sound hx hy (hFm.den hx hy) hrm
  have hRp := (EnclAt.mul hx hy K hm (hFp.LnW hx hy K hrdp)).sub hq
  have hRm := (EnclAt.mul hx hy K hm (hFm.LnW hx hy K hrdm)).sub hq
  unfold incrOK at hinc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hinc
  have hp := pos_of_lo hx hy hRp hinc.1
  have hn := neg_of_hi hx hy hRm hinc.2
  have hmono : MonotoneOn (fun z => m * LnR z - q) (Ioo 0 (1 / 2)) := by
    intro u hu v hv huv
    have := mul_le_mul_of_nonneg_left (LnR_mono hu hv huv) hm0.le
    simp only
    linarith
  exact site_encl hx hy hP hM (bracket_incr hmono htD.1 htD.2 eD hzm0 (zm_le_zp x y _) hzp hn hp)

theorem stageG {a b c tA tB tC tD uE zpa : ℝ}
    (ha : EnclAt x y a w.sa.z) (hb : EnclAt x y b w.sb.z) (hFb : FnsE x y b w.sb.F)
    (hFpa : FnsE x y zpa w.sa.Fp) (hFD : FnsE x y tD w.sD.F) (huE : EnclAt x y uE w.sU.z)
    (hFU : FnsE x y uE w.sU.F) (hc : EnclAt x y c (V2.cT K cl w)) (hFA : FnsE x y tA w.sA.F)
    (hFB : FnsE x y tB w.sB.F) (hFC : FnsE x y tC (V2.FC cl w)) :
    EnclAt x y (-((b - a) * JnR tD) + 1 / 2 * (-(b - a) * (JnR b - JnR zpa)) +
      -((1 - 2 * uE) * JnR uE) + 1 / 2 * ((1 - 2 * b) * JnR b) + (c - a) * JnR tA +
      (1 - a - c) * JnR tB + -(1 / 2 * ((1 - 2 * c) * JnR tC))) (V2.Gt K cl w) := by
  have hbma : EnclAt x y (b - a) (V2.bma w) := hb.sub ha
  have t1 := (EnclAt.mul hx hy K hbma hFD.Jn).neg
  have t2 := EnclAt.half hx hy (EnclAt.mul hx hy K hbma.neg (hFb.Jn.sub hFpa.Jn))
  have t3 := (EnclAt.mul hx hy K ((encl_one x y).sub (EnclAt.two hx hy huE)) hFU.Jn).neg
  have t4 := EnclAt.half hx hy (EnclAt.mul hx hy K ((encl_one x y).sub (EnclAt.two hx hy hb)) hFb.Jn)
  have t5 := EnclAt.mul hx hy K (hc.sub ha) hFA.Jn
  have t6 := EnclAt.mul hx hy K (((encl_one x y).sub ha).sub hc) hFB.Jn
  have t7 := (EnclAt.half hx hy
    (EnclAt.mul hx hy K ((encl_one x y).sub (EnclAt.two hx hy hc)) hFC.Jn)).neg
  exact (((((t1.add t2).add t3).add t4).add t5).add t6).add t7

end stages

/-! ## the four modes -/

section modes

variable {K : ℕ} {cl : CellV} {w : WitV} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
  (R : RealPt) (hR : R.Valid) (hAx : EnclAt x y R.A cl.A) (hTy : EnclAt x y R.tC cl.tC)
include hx hy hR hAx hTy

/-- the common prefix: stages `A, C, U, B, L` -/
theorem prefixL (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true) :
    FnsE x y R.tA w.sA.F ∧ FnsE x y R.tC (V2.FC cl w) ∧ FnsE x y R.tB w.sB.F ∧
      EnclAt x y R.B (V2.B K w) ∧ EnclAt x y R.lam (V2.lam K cl w) := by
  obtain ⟨-, hFA⟩ := stageA hx hy hAx hR.hA hR.htA hR.eA h1
  have hFC := stageC hx hy hTy h2
  have hUAC := stageU hx hy hFA hFC h3
  obtain ⟨-, hFB⟩ := stageB hx hy hUAC hR.htB hR.eB h4
  obtain ⟨hB, hlam⟩ := stageL hx hy hAx hFB hFC h5
  exact ⟨hFA, hFC, hFB, hB, hlam⟩

theorem sound_mode3 (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true)
    (hfin : V2.finL K cl w = true) : 1 ≤ R.lam := by
  obtain ⟨-, -, -, -, hlam⟩ := prefixL hx hy R hR hAx hTy h1 h2 h3 h4 h5
  unfold V2.finL at hfin
  rw [decide_eq_true_eq] at hfin
  have h := hlam.lo_le hx hy
  have hS := SC_pos
  have h' : ((ONE : ℤ) : ℝ) ≤ (((V2.lam K cl w).lo : ℤ) : ℝ) := by exact_mod_cast hfin
  rw [← SC_eq] at h'
  have : 1 ≤ (((V2.lam K cl w).lo : ℤ) : ℝ) / SC := by rw [le_div_iff₀ hS]; linarith
  linarith

/-- the prefix through `a` and `E` -/
theorem prefixE (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true)
    (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true) :
    EnclAt x y R.a w.sa.z ∧ R.a < zpR x y w.sa ∧ zpR x y w.sa < 1 / 2 ∧
      FnsE x y (zpR x y w.sa) w.sa.Fp ∧ EnclAt x y R.E (V2.E K w) ∧ EnclAt x y R.c (V2.cT K cl w) := by
  obtain ⟨-, -, -, hB, hlam⟩ := prefixL hx hy R hR hAx hTy h1 h2 h3 h4 h5
  have hAB : EnclAt x y (R.A + R.B) (V2.AB K cl w) := hAx.add hB
  have hrhs : EnclAt x y (2 * (1 - R.lam) * Real.log 2) (V2.rhsA K cl w) :=
    EnclAt.mul hx hy K (EnclAt.two hx hy ((encl_one x y).sub hlam)) (encl_ln2 x y)
  obtain ⟨hza, hlt, hzp, hFpa⟩ := stagea hx hy hAB hrhs hR.hAB hR.ha hR.ea h6
  have hE : EnclAt x y R.E (V2.E K w) := stageE hx hy hAB hza h7
  have hc : EnclAt x y R.c (V2.cT K cl w) :=
    EnclAt.half hx hy ((encl_one x y).sub (EnclAt.mul hx hy K hE (hB.sub hAx)))
  exact ⟨hza, hlt, hzp, hFpa, hE, hc⟩

theorem sound_mode2 (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true)
    (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true) (hfin : V2.finF K cl w = true) :
    R.a + R.c ≤ 1 / 10000 := by
  obtain ⟨hza, -, -, -, -, hc⟩ := prefixE hx hy R hR hAx hTy h1 h2 h3 h4 h5 h6 h7
  unfold V2.finF at hfin
  rw [decide_eq_true_eq] at hfin
  have h := (hza.add hc).le_hi hx hy
  have hS := SC_pos
  have h' : ((10000 * (w.sa.z.add (V2.cT K cl w)).hi : ℤ) : ℝ) ≤ ((ONE : ℤ) : ℝ) := by
    exact_mod_cast hfin
  rw [← SC_eq] at h'
  push_cast at h'
  have : (((w.sa.z.add (V2.cT K cl w)).hi : ℤ) : ℝ) / SC ≤ 1 / 10000 := by
    rw [div_le_iff₀ hS]; linarith
  linarith

/-- the prefix through `b` -/
theorem prefixb (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true)
    (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true) (h8 : V2.chkb K cl w = true) :
    EnclAt x y R.b w.sb.z ∧ FnsE x y R.b w.sb.F := by
  obtain ⟨-, -, -, -, hlam⟩ := prefixL hx hy R hR hAx hTy h1 h2 h3 h4 h5
  obtain ⟨-, -, -, -, hE, -⟩ := prefixE hx hy R hR hAx hTy h1 h2 h3 h4 h5 h6 h7
  have hq : EnclAt x y (R.lam * R.E * Real.log 2) (V2.lamEln2 K cl w) :=
    EnclAt.mul hx hy K (EnclAt.mul hx hy K hlam hE) (encl_ln2 x y)
  exact stageb hx hy hq hR.hb hR.eb h8

theorem sound_mode1 (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true)
    (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true) (h8 : V2.chkb K cl w = true)
    (hfin : V2.finE cl w = true) : R.tC < R.b := by
  obtain ⟨hzb, -⟩ := prefixb hx hy R hR hAx hTy h1 h2 h3 h4 h5 h6 h7 h8
  unfold V2.finE at hfin
  rw [decide_eq_true_eq] at hfin
  have := pos_of_lo hx hy (hzb.sub hTy) hfin
  linarith

theorem sound_mode0 (h1 : V2.chkA K cl w = true) (h2 : V2.chkC K cl w = true)
    (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true) (h5 : V2.chkL K cl w = true)
    (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true) (h8 : V2.chkb K cl w = true)
    (h9 : V2.chkD K w = true) (h10 : V2.chkUE K w = true) (hfin : V2.finG K cl w = true) :
    0 < R.G := by
  obtain ⟨hFA, hFC, hFB, -, -⟩ := prefixL hx hy R hR hAx hTy h1 h2 h3 h4 h5
  obtain ⟨hza, hlt, hzp, hFpa, hE, hc⟩ := prefixE hx hy R hR hAx hTy h1 h2 h3 h4 h5 h6 h7
  obtain ⟨hzb, hFb⟩ := prefixb hx hy R hR hAx hTy h1 h2 h3 h4 h5 h6 h7 h8
  have hbma : EnclAt x y (R.b - R.a) (V2.bma w) := hzb.sub hza
  have hEl : EnclAt x y (R.E * Real.log 2) (V2.Eln2 K w) := EnclAt.mul hx hy K hE (encl_ln2 x y)
  obtain ⟨-, hFD⟩ := stageD hx hy hbma hEl hR.hba hR.htD hR.eD h9
  obtain ⟨hzU, hFU⟩ := stageUE hx hy (EnclAt.half hx hy hEl) hR.huE hR.eU h10
  have hGe := stageG hx hy hza hzb hFb hFpa hFD hzU hFU hc hFA hFB hFC
  unfold V2.finG at hfin
  rw [decide_eq_true_eq] at hfin
  have hpos := pos_of_lo hx hy hGe hfin
  set zp := zpR x y w.sa
  have hJ : JnR zp ≤ JnR R.a := by
    unfold JnR
    have h1' : Real.log (1 - zp) ≤ Real.log (1 - R.a) := Real.log_le_log (by linarith) (by linarith)
    have h2' : Real.log R.a ≤ Real.log zp := Real.log_le_log hR.ha.1 hlt.le
    linarith
  have key : R.G = (-((R.b - R.a) * JnR R.tD) + 1 / 2 * (-(R.b - R.a) * (JnR R.b - JnR zp)) +
      -((1 - 2 * R.uE) * JnR R.uE) + 1 / 2 * ((1 - 2 * R.b) * JnR R.b) + (R.c - R.a) * JnR R.tA +
      (1 - R.a - R.c) * JnR R.tB + -(1 / 2 * ((1 - 2 * R.c) * JnR R.tC))) +
      1 / 2 * ((R.b - R.a) * (JnR R.a - JnR zp)) := by
    unfold RealPt.G; ring
  have hnn : 0 ≤ 1 / 2 * ((R.b - R.a) * (JnR R.a - JnR zp)) :=
    mul_nonneg (by norm_num) (mul_nonneg hR.hba.le (sub_nonneg.mpr hJ))
  rw [key]
  linarith

end modes

end CKLaneM07.CE

end


