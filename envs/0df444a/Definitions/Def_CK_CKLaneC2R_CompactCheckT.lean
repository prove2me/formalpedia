-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCheckT
-- name    : CK_CKLaneC2R_CompactCheckT
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T07:26:34.870975+00:00
-- url     : https://prove2.me/theorems/f57ed083-05eb-4a1f-ae25-57f15d7f7d7a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCheckT` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCheckT` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCheckT` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCheckT (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCheckT.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCheck

-- ===== source module CKLaneC2R.CompactCheckT =====
section

/-!
# Lane C2 (reflection compact): table-deduplicated reflective checker

Same semantics as `CKLaneC2R.cellOk`, but every executable logarithm datum is checked once per
cell: a cell carries a `table` of datums, `allCheck table` is evaluated once, and each witness datum
is looked up in the table (`memD`).  Soundness re-derives the log / entropy / B / contact witness
facts of `ReflectionFastTranscendental` from the table, then `Accepted` for both programs directly.
-/

namespace CKLaneC2R.T

open GeneralCK GeneralCK.Certificates CKLaneC2R
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet Shape)
open BivariateProvedProgram ReflectionCompactProgramKernel
open ReflectionFastTranscendental CorrectionIntegerLogTableKernel
open Set

def memD (d : Datum) : List Datum → Bool
  | [] => false
  | x :: xs => decide (d = x) || memD d xs

theorem memD_check {T : List Datum} (hT : allCheck T = true) {d : Datum} (h : memD d T = true) :
    d.check = true := by
  induction T with
  | nil => simp [memD] at h
  | cons x xs ih =>
      simp only [allCheck, Bool.and_eq_true] at hT
      simp only [memD, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · rw [h]; exact hT.1
      · exact ih hT.2 h

def logCheckT (T : List Datum) (input output : DyadicInterval 40) (w : LogWitness) : Bool :=
  decide (0 < input.lo ∧ w.lower.z = input.lo ∧ w.upper.z = input.hi) &&
    memD w.lower T && memD w.upper T &&
    w.lower.output.subsetCheck output && w.upper.output.subsetCheck output

theorem logCheckT_sound {T : List Datum} (hT : allCheck T = true) {input output : DyadicInterval 40}
    {w : LogWitness} (h : logCheckT T input output w = true) :
    ProvedTranscendental.LogEncloses input output := by
  simp only [logCheckT, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨guards, hl⟩, hu⟩, hsl⟩, hsu⟩
  have g := of_decide_eq_true guards
  apply ProvedTranscendental.log_of_endpoints
  · exact g.1
  · rw [← g.2.1]
    exact DyadicInterval.subsetCheck_sound hsl (Datum.sound_of_check (memD_check hT hl))
  · rw [← g.2.2]
    exact DyadicInterval.subsetCheck_sound hsu (Datum.sound_of_check (memD_check hT hu))

theorem logCheckT_pos {T : List Datum} {input output : DyadicInterval 40} {w : LogWitness}
    (h : logCheckT T input output w = true) : 0 < input.lo := by
  simp only [logCheckT, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.1.1.1.1).1

def entCheckT (T : List Datum) (c : DyadicInterval 40) (w : EntropyWitness) : Bool :=
  logCheckT T (DyadicInterval.ofInt 40 2) w.two w.twoLog &&
    logCheckT T ((DyadicInterval.ofInt 40 1).add c) w.plus w.plusLog &&
    logCheckT T ((DyadicInterval.ofInt 40 1).sub c) w.minus w.minusLog &&
    (ProvedTranscendental.entropyRaw c w.two w.plus w.minus).subsetCheck w.output

theorem entCheckT_sound {T : List Datum} (hT : allCheck T = true) {c : DyadicInterval 40}
    {w : EntropyWitness} (h : entCheckT T c w = true) {x : ℝ} (hx : c.Contains x) :
    w.output.Contains (Reflection.biasE x) := by
  simp only [entCheckT, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨h2, hp⟩, hm⟩, hsub⟩
  exact ProvedTranscendental.entropy_encloses
    (logCheckT_sound hT h2 2 (by
      norm_num [DyadicInterval.Contains, DyadicInterval.ofInt, DyadicInterval.scale]))
    (logCheckT_sound hT hp) (logCheckT_sound hT hm) hsub hx

def bCheckT (T : List Datum) (c : DyadicInterval 40) (w : BWitness) : Bool :=
  logCheckT T (DyadicInterval.ofInt 40 2) w.two w.twoLog &&
    logCheckT T ((DyadicInterval.ofInt 40 1).sub (c.mul c)) w.gapLog w.gapLogWitness &&
    (ProvedTranscendental.denominatorRaw w.two w.gapLog).subsetCheck w.output

theorem bCheckT_sound {T : List Datum} (hT : allCheck T = true) {c : DyadicInterval 40}
    {w : BWitness} (h : bCheckT T c w = true) {x : ℝ} (hx : c.Contains x) :
    w.output.Contains (Reflection.biasB x) := by
  simp only [bCheckT, Bool.and_eq_true] at h
  rcases h with ⟨⟨h2, hg⟩, hsub⟩
  exact ProvedTranscendental.denominator_encloses
    (logCheckT_sound hT h2 2 (by
      norm_num [DyadicInterval.Contains, DyadicInterval.ofInt, DyadicInterval.scale]))
    (logCheckT_sound hT hg) hsub hx

def conCheckT (T : List Datum) (input : DyadicInterval 40) (w : ContactWitness) : Bool :=
  decide (0 ≤ w.contact.lo ∧ w.contact.hi ≤ DyadicInterval.scale 40 ∧
    w.contact.lo ≤ w.contact.hi ∧ 0 < input.lo) &&
    entCheckT T (DyadicContact.point w.contact.lo) w.entropyLo &&
    entCheckT T (DyadicContact.point w.contact.hi) w.entropyHi &&
    decide ((input.mul (DyadicContact.point w.contact.lo)).hi ≤ w.entropyLo.output.lo ∧
      w.entropyHi.output.hi ≤ (input.mul (DyadicContact.point w.contact.hi)).lo) &&
    bCheckT T w.contact w.bWitness &&
    decide (w.bWitness.output = w.denominator ∧ 0 < w.denominator.lo ∧
      0 < (DyadicContact.gap w.contact).lo) &&
    (DyadicContact.enclosure w.contact w.denominator).subsetCheck w.outer

theorem conCheckT_sound {T : List Datum} (hT : allCheck T = true) {input : DyadicInterval 40}
    {w : ContactWitness} (h : conCheckT T input w = true) {y : ℝ} (hy : input.Contains y) :
    w.outer.Contains reflectionContactJet y := by
  simp only [conCheckT, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨guards, hlo⟩, hhi⟩, compares⟩, hb⟩, positive⟩, hsub⟩
  have g := of_decide_eq_true guards
  have cmp := of_decide_eq_true compares
  have pos := of_decide_eq_true positive
  have hden : w.bWitness.output = w.denominator := pos.1
  have hc := ProvedTranscendental.contact_bracket g.1 g.2.1 g.2.2.1 g.2.2.2
    (entCheckT_sound hT hlo (DyadicContact.point_contains 40 w.contact.lo))
    (entCheckT_sound hT hhi (DyadicContact.point_contains 40 w.contact.hi))
    cmp.1 cmp.2 hy
  exact DyadicJetEnclosure.subsetCheck_sound hsub
    (DyadicContact.enclosure_sound
      (DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using g.2.2.2) hy)
      hc (by simpa [hden] using bCheckT_sound hT hb hc) pos.2.1 pos.2.2)

theorem conCheckT_pos {T : List Datum} {input : DyadicInterval 40} {w : ContactWitness}
    (h : conCheckT T input w = true) : 0 < input.lo := by
  simp only [conCheckT, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.1.1.1.1.1.1).2.2.2

def payloadCheckT (T : List Datum) (shape : Shape) (boxes : List (DyadicBivariateJetEnclosure 40))
    (payload : Payload) : Bool :=
  match shape, payload with
  | .log i, .log proposed witness =>
      logCheckT T (boxes.getD i (zeroBox 40)).value proposed.value witness &&
        ((boxes.getD i (zeroBox 40)).log proposed.value).subsetCheck proposed
  | .contact i, .contact proposed witness =>
      conCheckT T (boxes.getD i (zeroBox 40)).value witness &&
        (DyadicBivariateJetEnclosure.outerCompose witness.outer
          (boxes.getD i (zeroBox 40))).subsetCheck proposed
  | _, _ => false

/-- Single-pass runner with table-checked transcendental witnesses. -/
def runProgT (T : List Datum) : List Shape → List Payload → List (DyadicBivariateJetEnclosure 40) →
    Option (List (DyadicBivariateJetEnclosure 40))
  | [], _, boxes => some boxes
  | shape :: shapes, payloads, boxes =>
      match needsPayload shape, payloads with
      | true, payload :: rest =>
          match decide (InRange shape boxes.length) && payloadCheckT T shape boxes payload with
          | true => runProgT T shapes rest (payload.proposed :: boxes)
          | false => none
      | true, [] => none
      | false, _ =>
          match stepGuard shape boxes with
          | true => runProgT T shapes payloads (arithmeticOutput shape boxes :: boxes)
          | false => none

theorem stepValid_arith {shape : Shape} {boxes : List (DyadicBivariateJetEnclosure 40)}
    (hp : needsPayload shape = false) (hg : stepGuard shape boxes = true) :
    StepValid shape boxes (arithmeticOutput shape boxes) := by
  apply CorrectionHybridProgramKernel.arithmeticStepCheck_sound_of_nonlinear
    (arithmeticStepCheck_self hp hg)
  cases shape with
  | add i j => exact True.intro
  | neg i => exact True.intro
  | mul i j => exact True.intro
  | inv i => exact True.intro
  | log i => simp [needsPayload] at hp
  | contact i => simp [needsPayload] at hp

theorem stepValid_log {T : List Datum} (hT : allCheck T = true) {i : ℕ}
    {boxes : List (DyadicBivariateJetEnclosure 40)} {proposed : DyadicBivariateJetEnclosure 40}
    {witness : LogWitness} (hr : InRange (.log i) boxes.length)
    (h : payloadCheckT T (.log i) boxes (.log proposed witness) = true) :
    StepValid (.log i) boxes proposed := by
  simp only [payloadCheckT, Bool.and_eq_true] at h
  exact ⟨hr, logCheckT_pos h.1, logCheckT_sound hT h.1, h.2⟩

theorem stepValid_contact {T : List Datum} (hT : allCheck T = true) {i : ℕ}
    {boxes : List (DyadicBivariateJetEnclosure 40)} {proposed : DyadicBivariateJetEnclosure 40}
    {witness : ContactWitness} (hr : InRange (.contact i) boxes.length)
    (h : payloadCheckT T (.contact i) boxes (.contact proposed witness) = true) :
    StepValid (.contact i) boxes proposed := by
  simp only [payloadCheckT, Bool.and_eq_true] at h
  exact ⟨hr, conCheckT_pos h.1, witness.outer, (fun y hy => conCheckT_sound hT h.1 hy), h.2⟩

theorem runProgT_sound (T : List Datum) (hT : allCheck T = true) :
    ∀ (shapes : List Shape) (payloads : List Payload)
      (boxes final : List (DyadicBivariateJetEnclosure 40)),
      runProgT T shapes payloads boxes = some final →
      Accepted (build40 shapes payloads boxes) boxes ∧
      BivariateProvedProgram.shapes (build40 shapes payloads boxes) = shapes ∧
      finalBoxes (build40 shapes payloads boxes) boxes = final
  | [], payloads, boxes, final, h => by
      simp only [runProgT, Option.some.injEq] at h
      subst h
      exact ⟨trivial, rfl, rfl⟩
  | shape :: shapes, payloads, boxes, final, h => by
      cases hp : needsPayload shape with
      | false =>
          cases hg : stepGuard shape boxes with
          | false => simp [runProgT, hp, hg] at h
          | true =>
              have h' : runProgT T shapes payloads (arithmeticOutput shape boxes :: boxes) =
                  some final := by
                simpa [runProgT, hp, hg] using h
              obtain ⟨ha, hs, hf⟩ := runProgT_sound T hT shapes payloads _ final h'
              have hb : build40 (shape :: shapes) payloads boxes =
                  ⟨shape, arithmeticOutput shape boxes⟩ ::
                    build40 shapes payloads (arithmeticOutput shape boxes :: boxes) := by
                simp only [build40, hp, Bool.false_eq_true, ↓reduceIte]
              rw [hb]
              refine ⟨⟨stepValid_arith hp hg, ha⟩, ?_, hf⟩
              show shape :: BivariateProvedProgram.shapes
                (build40 shapes payloads (arithmeticOutput shape boxes :: boxes)) = shape :: shapes
              rw [hs]
      | true =>
          cases payloads with
          | nil => simp [runProgT, hp] at h
          | cons payload rest =>
              cases hc : (decide (InRange shape boxes.length) && payloadCheckT T shape boxes payload) with
              | false => simp [runProgT, hp, hc] at h
              | true =>
                  have h' : runProgT T shapes rest (payload.proposed :: boxes) = some final := by
                    simpa [runProgT, hp, hc] using h
                  obtain ⟨ha, hs, hf⟩ := runProgT_sound T hT shapes rest _ final h'
                  have hc' := Bool.and_eq_true_iff.mp hc
                  have hr : InRange shape boxes.length := of_decide_eq_true hc'.1
                  have hb : build40 (shape :: shapes) (payload :: rest) boxes =
                      ⟨shape, payload.proposed⟩ :: build40 shapes rest (payload.proposed :: boxes) := by
                    simp only [build40, hp, ↓reduceIte]
                  rw [hb]
                  refine ⟨⟨?_, ha⟩, ?_, hf⟩
                  · cases shape with
                    | log i =>
                        cases payload with
                        | log proposed witness => exact stepValid_log hT hr hc'.2
                        | contact proposed witness => simp [payloadCheckT] at hc'
                    | contact i =>
                        cases payload with
                        | contact proposed witness => exact stepValid_contact hT hr hc'.2
                        | log proposed witness => simp [payloadCheckT] at hc'
                    | add i j => simp [needsPayload] at hp
                    | neg i => simp [needsPayload] at hp
                    | mul i j => simp [needsPayload] at hp
                    | inv i => simp [needsPayload] at hp
                  · show shape :: BivariateProvedProgram.shapes
                      (build40 shapes rest (payload.proposed :: boxes)) = shape :: shapes
                    rw [hs]

theorem output_valueT (pay : List Payload) (regs : List (DyadicBivariateJetEnclosure 40))
    (hs : BivariateProvedProgram.shapes (build40 refShapes pay regs) = refShapes) (ac zc a z : ℝ) :
    ((finalJets (build40 refShapes pay regs) (inputJets ac zc a z)).getD 0 zeroJet).value 1 =
      ReflectionExpression.normalizedValue a z := by
  rw [finalJet_value, CorrectionProgramKernel.evalRealProgram_eq_of_shapes_eq
    (right := BivariateFastPilot.wholeProgram) (by rw [hs, refShapes_eq])]
  have hmap : List.map (fun j => j.value 1) (inputJets ac zc a z) = [a, z, 1, 2] := by
    simp [inputJets, BivariateJet2.affineA, BivariateJet2.affineZ, BivariateJet2.coordinateA,
      BivariateJet2.coordinateZ, BivariateJet2.const]
  rw [hmap, BivariateFastPilot.scalar_program, BivariateFastPilot.scalarCore_eq]

theorem sound_of_accepted (c : CCell) (hbox : boxOk c = true)
    (haC : Accepted (build40 refShapes c.cpay (initRegs c.ca c.cz)) (initRegs c.ca c.cz))
    (hsC : BivariateProvedProgram.shapes (build40 refShapes c.cpay (initRegs c.ca c.cz)) = refShapes)
    (haW : Accepted (build40 refShapes c.wpay (initRegs c.wa c.wz)) (initRegs c.wa c.wz))
    (hsW : BivariateProvedProgram.shapes (build40 refShapes c.wpay (initRegs c.wa c.wz)) = refShapes)
    (ht : 0 < taylorQ (outBox c.cpay (initRegs c.ca c.cz)) (outBox c.wpay (initRegs c.wa c.wz))
      ((c.au - c.al) / 2) ((c.zu - c.zl) / 2))
    {a z : ℝ} (ha1 : (c.al : ℝ) ≤ a) (ha2 : a ≤ (c.au : ℝ))
    (hz1 : (c.zl : ℝ) ≤ z) (hz2 : z ≤ (c.zu : ℝ)) :
    0 < Reflection.curvature a (a * z) := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hal, halu⟩, hau⟩, hzl⟩, hzlu⟩, hzu⟩, hca⟩, hcz⟩, hwa1⟩, hwa2⟩, hwz1⟩, hwz2⟩ :=
    hbox
  have hal' : (0 : ℝ) < c.al := by exact_mod_cast hal
  have hau' : (c.au : ℝ) < 1 := by exact_mod_cast hau
  have hzl' : (0 : ℝ) < c.zl := by exact_mod_cast hzl
  have hzu' : (c.zu : ℝ) < 1 := by exact_mod_cast hzu
  have hacR : ((((c.al + c.au) / 2 : ℚ)) : ℝ) = ((c.al : ℝ) + c.au) / 2 := by push_cast; ring
  have hzcR : ((((c.zl + c.zu) / 2 : ℚ)) : ℝ) = ((c.zl : ℝ) + c.zu) / 2 := by push_cast; ring
  have hraR : ((((c.au - c.al) / 2 : ℚ)) : ℝ) = ((c.au : ℝ) - c.al) / 2 := by push_cast; ring
  have hrzR : ((((c.zu - c.zl) / 2 : ℚ)) : ℝ) = ((c.zu : ℝ) - c.zl) / 2 := by push_cast; ring
  have hcA : c.ca.Contains ((((c.al + c.au) / 2 : ℚ)) : ℝ) :=
    contains_of_memQ hca hca le_rfl le_rfl
  have hcZ : c.cz.Contains ((((c.zl + c.zu) / 2 : ℚ)) : ℝ) :=
    contains_of_memQ hcz hcz le_rfl le_rfl
  have hacIn1 : (c.al : ℝ) ≤ ((((c.al + c.au) / 2 : ℚ)) : ℝ) := by rw [hacR]; linarith
  have hacIn2 : ((((c.al + c.au) / 2 : ℚ)) : ℝ) ≤ (c.au : ℝ) := by rw [hacR]; linarith
  have hzcIn1 : (c.zl : ℝ) ≤ ((((c.zl + c.zu) / 2 : ℚ)) : ℝ) := by rw [hzcR]; linarith
  have hzcIn2 : ((((c.zl + c.zu) / 2 : ℚ)) : ℝ) ≤ (c.zu : ℝ) := by rw [hzcR]; linarith
  have hkey : (0 : ℝ) < ((taylorQ (outBox c.cpay (initRegs c.ca c.cz))
      (outBox c.wpay (initRegs c.wa c.wz)) ((c.au - c.al) / 2) ((c.zu - c.zl) / 2) : ℚ) : ℝ) := by
    exact_mod_cast ht
  rw [taylorQ_cast] at hkey
  have hp := value_pos_of_accepted_taylor (build40 refShapes c.cpay (initRegs c.ca c.cz))
    (build40 refShapes c.wpay (initRegs c.wa c.wz))
    (da := a - ((((c.al + c.au) / 2 : ℚ)) : ℝ)) (dz := z - ((((c.zl + c.zu) / 2 : ℚ)) : ℝ))
    (ra := ((((c.au - c.al) / 2 : ℚ)) : ℝ)) (rz := ((((c.zu - c.zl) / 2 : ℚ)) : ℝ)) 0
    (by rw [hsC, hsW])
    (initial_center hcA hcZ a z)
    (initial_whole (contains_of_memQ hwa1 hwa2 hacIn1 hacIn2) (contains_of_memQ hwa1 hwa2 ha1 ha2)
      (contains_of_memQ hwz1 hwz2 hzcIn1 hzcIn2) (contains_of_memQ hwz1 hwz2 hz1 hz2))
    (initial_sound _ _ a z)
    haC haW
    (by rw [hraR]; linarith) (by rw [hrzR]; linarith)
    (by rw [abs_le, hraR, hacR]; constructor <;> linarith)
    (by rw [abs_le, hrzR, hzcR]; constructor <;> linarith)
    hkey
  rw [output_valueT _ _ hsW] at hp
  exact Reflection.curvature_pos_of_normalizedValue_pos (by linarith) (by linarith)
    (by linarith) (by linarith) hp

/-- A compact cell with its deduplicated datum table. -/
structure CCellT extends CCell where
  table : List Datum

/-- The table-deduplicated reflective cell checker. -/
def cellOkT (c : CCellT) : Bool :=
  boxOk c.toCCell && allCheck c.table &&
    match runProgT c.table refShapes c.cpay (initRegs c.ca c.cz),
        runProgT c.table refShapes c.wpay (initRegs c.wa c.wz) with
    | some fc, some fw => taylorOk c.toCCell fc fw
    | _, _ => false

theorem cellOkT_sound (c : CCellT) (hc : cellOkT c = true) {a z : ℝ}
    (ha1 : (c.al : ℝ) ≤ a) (ha2 : a ≤ (c.au : ℝ)) (hz1 : (c.zl : ℝ) ≤ z) (hz2 : z ≤ (c.zu : ℝ)) :
    0 < Reflection.curvature a (a * z) := by
  simp only [cellOkT, Bool.and_eq_true] at hc
  obtain ⟨⟨hbox, hT⟩, hrun⟩ := hc
  cases hC : runProgT c.table refShapes c.cpay (initRegs c.ca c.cz) with
  | none => simp [hC] at hrun
  | some fc =>
      cases hW : runProgT c.table refShapes c.wpay (initRegs c.wa c.wz) with
      | none => simp [hC, hW] at hrun
      | some fw =>
          simp only [hC, hW, taylorOk, decide_eq_true_eq] at hrun
          obtain ⟨haC, hsC, hfC⟩ := runProgT_sound _ hT _ _ _ _ hC
          obtain ⟨haW, hsW, hfW⟩ := runProgT_sound _ hT _ _ _ _ hW
          refine sound_of_accepted c.toCCell hbox haC hsC haW hsW ?_ ha1 ha2 hz1 hz2
          simpa [outBox, hfC, hfW] using hrun

end CKLaneC2R.T

end


