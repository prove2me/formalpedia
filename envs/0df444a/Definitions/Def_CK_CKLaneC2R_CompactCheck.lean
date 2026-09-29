-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCheck
-- name    : CK_CKLaneC2R_CompactCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:21:27.221855+00:00
-- url     : https://prove2.me/theorems/06659100-d465-48df-9182-d72173709819
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCheck.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionCompactProgramKernel
import Definitions.Def_CK_GeneralCK_Certificates_CorrectionProgramKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_BivariateFastPilot
import Definitions.Def_CK_GeneralCK_ReflectionNormalized

-- ===== source module CKLaneC2R.CompactCheck =====
section

/-!
# Lane C2 (reflection compact): one reflective checker for compact reflection cells

A cell is a rational box `[al,au] × [zl,zu]` together with dyadic coordinate enclosures and the
transcendental payloads (log / contact enclosures with executable witnesses) for the fixed
134-step compact reflection program, evaluated once at the box centre (`center`) and once on the
whole box (`whole`).  `cellOk` recomputes every arithmetic step, re-checks every payload with the
proved compact kernel `ReflectionCompactProgramKernel`, and evaluates the second-order Taylor
lower bound exactly in `ℚ`.  `cellOk_sound` turns `cellOk c = true` (discharged per cell by
`decide +kernel`) into `0 < Reflection.curvature a (a*z)` on the whole box.
-/

namespace CKLaneC2R

open GeneralCK GeneralCK.Certificates
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet Shape)
open BivariateProvedProgram ReflectionCompactProgramKernel
open Set

/-- The fixed shape skeleton of the compact reflection program (134 steps). -/
def refShapes : List Shape :=
  [.log 3,.mul 1 2,.add 4 2,.log 0,.mul 1 0,.neg 5,.add 8 0,.log 0,.mul 1 0,.add 4 0,.inv 13,
   .mul 1 0,.neg 0,.add 12 0,.add 16 12,.log 0,.mul 1 0,.neg 15,.add 20 0,.log 0,.mul 1 0,
   .add 4 0,.mul 0 11,.neg 0,.add 23 0,.add 11 0,.mul 0 15,.neg 28,.add 30 0,.mul 29 0,
   .mul 0 19,.inv 0,.mul 5 0,.contact 0,.add 36 35,.mul 35 0,.mul 0 25,.inv 0,.mul 11 0,
   .contact 0,.inv 33,.mul 38 0,.log 0,.mul 0 32,.mul 47 44,.mul 0 43,.mul 46 46,.neg 0,
   .add 50 0,.mul 0 0,.inv 0,.mul 5 0,.add 54 18,.log 0,.mul 1 0,.neg 21,.add 58 0,.log 0,
   .mul 1 0,.add 4 0,.mul 0 49,.neg 0,.add 61 0,.mul 29 29,.neg 0,.add 67 0,.log 0,.mul 0 56,
   .neg 0,.add 68 0,.mul 73 0,.add 0 6,.mul 9 0,.mul 39 29,.add 11 0,.mul 0 0,.mul 3 0,
   .mul 80 50,.mul 12 12,.mul 1 0,.mul 10 10,.mul 11 0,.mul 2 0,.inv 0,.mul 7 0,.mul 36 19,
   .mul 0 16,.inv 0,.mul 24 0,.add 4 0,.add 38 0,.add 93 51,.log 0,.mul 1 0,.neg 54,.add 97 0,
   .log 0,.mul 1 0,.add 4 0,.mul 0 88,.neg 0,.add 100 0,.mul 62 62,.neg 0,.add 106 0,.log 0,
   .mul 0 95,.neg 0,.add 107 0,.mul 112 0,.add 0 6,.mul 9 0,.mul 72 68,.add 11 0,.mul 0 0,
   .mul 3 0,.mul 11 11,.mul 39 0,.mul 9 9,.mul 10 0,.mul 2 0,.inv 0,.mul 6 0,.mul 74 18,
   .mul 0 15,.inv 0,.mul 23 0,.add 4 0,.neg 0,.add 38 0,.mul 130 83,.mul 0 129,.inv 0,.mul 3 0]

theorem refShapes_eq : refShapes = shapes BivariateFastPilot.wholeProgram := by rfl

/-- One compact cell: box, initial coordinate enclosures, and the two payload lists. -/
structure CCell where
  al : ℚ
  au : ℚ
  zl : ℚ
  zu : ℚ
  ca : DyadicInterval 40
  cz : DyadicInterval 40
  wa : DyadicInterval 40
  wz : DyadicInterval 40
  cpay : List Payload
  wpay : List Payload

/-- Initial registers `[A, Z, 1, 2]`. -/
def initRegs (va vz : DyadicInterval 40) : List (DyadicBivariateJetEnclosure 40) :=
  [DyadicBivariateJetEnclosure.coordinateA va, DyadicBivariateJetEnclosure.coordinateZ vz,
    DyadicBivariateJetEnclosure.const 40 1, DyadicBivariateJetEnclosure.const 40 2]

/-- Exact membership test of a rational in a dyadic interval at scale `2^40`. -/
def memQ (d : DyadicInterval 40) (q : ℚ) : Bool :=
  decide ((d.lo : ℚ) ≤ 2 ^ 40 * q) && decide (2 ^ 40 * q ≤ (d.hi : ℚ))

def magQ (d : DyadicInterval 40) : ℚ := max |(d.lo : ℚ) / 2 ^ 40| |(d.hi : ℚ) / 2 ^ 40|

def taylorQ (c w : DyadicBivariateJetEnclosure 40) (ra rz : ℚ) : ℚ :=
  (c.value.lo : ℚ) / 2 ^ 40 - magQ c.firstA * ra - magQ c.firstZ * rz -
    (magQ w.secondAA * ra ^ 2 + 2 * magQ w.secondAZ * ra * rz + magQ w.secondZZ * rz ^ 2) / 2

def progOk (pay : List Payload) (regs : List (DyadicBivariateJetEnclosure 40)) : Bool :=
  CorrectionHybridProgramKernel.arithmeticCheck (build40 refShapes pay regs) regs &&
    nonlinearCheck refShapes pay regs

def outBox (pay : List Payload) (regs : List (DyadicBivariateJetEnclosure 40)) :
    DyadicBivariateJetEnclosure 40 :=
  (finalBoxes (build40 refShapes pay regs) regs).getD 0 (zeroBox 40)

def boxOk (c : CCell) : Bool :=
  decide (0 < c.al) && decide (c.al < c.au) && decide (c.au < 1) &&
  decide (0 < c.zl) && decide (c.zl < c.zu) && decide (c.zu < 1) &&
  memQ c.ca ((c.al + c.au) / 2) && memQ c.cz ((c.zl + c.zu) / 2) &&
  memQ c.wa c.al && memQ c.wa c.au && memQ c.wz c.zl && memQ c.wz c.zu

/-- Cheap step guard for the single-pass runner: the arithmetic output is computed exactly once,
so its self-inclusion check is trivially true; only range and reciprocal positivity remain. -/
def stepGuard (shape : Shape) (boxes : List (DyadicBivariateJetEnclosure 40)) : Bool :=
  decide (InRange shape boxes.length) &&
    match shape with
    | .inv i => (boxes.getD i (zeroBox 40)).value.positiveCheck
    | _ => true

/-- Single-pass runner: computes every arithmetic output once, checks every payload and every
register range, and returns the final register file. -/
def runProg : List Shape → List Payload → List (DyadicBivariateJetEnclosure 40) →
    Option (List (DyadicBivariateJetEnclosure 40))
  | [], _, boxes => some boxes
  | shape :: shapes, payloads, boxes =>
      match needsPayload shape, payloads with
      | true, payload :: rest =>
          match decide (InRange shape boxes.length) && payloadCheck shape boxes payload with
          | true => runProg shapes rest (payload.proposed :: boxes)
          | false => none
      | true, [] => none
      | false, _ =>
          match stepGuard shape boxes with
          | true => runProg shapes payloads (arithmeticOutput shape boxes :: boxes)
          | false => none

def taylorOk (c : CCell) (fc fw : List (DyadicBivariateJetEnclosure 40)) : Bool :=
  decide (0 < taylorQ (fc.getD 0 (zeroBox 40)) (fw.getD 0 (zeroBox 40))
    ((c.au - c.al) / 2) ((c.zu - c.zl) / 2))

/-- The reflective cell checker. -/
def cellOk (c : CCell) : Bool :=
  boxOk c &&
    match runProg refShapes c.cpay (initRegs c.ca c.cz),
        runProg refShapes c.wpay (initRegs c.wa c.wz) with
    | some fc, some fw => taylorOk c fc fw
    | _, _ => false

/-! ## Soundness -/

noncomputable def inputJets (ac zc a z : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA ac a, BivariateJet2.affineZ zc z,
    BivariateJet2.const ((1 : ℤ) : ℝ), BivariateJet2.const ((2 : ℤ) : ℝ)]

theorem contains_of_memQ {d : DyadicInterval 40} {ql qh : ℚ}
    (h1 : memQ d ql = true) (h2 : memQ d qh = true) {x : ℝ}
    (hl : (ql : ℝ) ≤ x) (hh : x ≤ (qh : ℝ)) : d.Contains x := by
  simp only [memQ, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  have e1 : ((d.lo : ℚ) : ℝ) ≤ ((2 ^ 40 * ql : ℚ) : ℝ) := by exact_mod_cast h1.1
  have e2 : ((2 ^ 40 * qh : ℚ) : ℝ) ≤ ((d.hi : ℚ) : ℝ) := by exact_mod_cast h2.2
  push_cast at e1 e2
  simp only [DyadicInterval.Contains, DyadicInterval.scale]
  push_cast
  constructor <;> nlinarith

theorem magQ_cast (d : DyadicInterval 40) : ((magQ d : ℚ) : ℝ) = d.toReal.magnitude := by
  simp only [magQ, DyadicInterval.toReal, JetBounds.Interval.magnitude, DyadicInterval.scale]
  push_cast
  norm_num

theorem taylorQ_cast (c w : DyadicBivariateJetEnclosure 40) (ra rz : ℚ) :
    ((taylorQ c w ra rz : ℚ) : ℝ) =
      BivariateJetEnclosure.taylorLower c.toReal w.toReal (ra : ℝ) (rz : ℝ) := by
  simp only [taylorQ, BivariateJetEnclosure.taylorLower, DyadicBivariateJetEnclosure.toReal]
  push_cast
  simp only [magQ_cast, DyadicInterval.toReal, DyadicInterval.scale]
  push_cast
  ring

theorem initial_center {va vz : DyadicInterval 40} {ac zc : ℝ}
    (hva : va.Contains ac) (hvz : vz.Contains zc) (a z : ℝ) :
    RegistersContain (initRegs va vz) (inputJets ac zc a z) 0 := by
  have hA : (DyadicBivariateJetEnclosure.coordinateA va).Contains
      (BivariateJet2.affineA ac a) 0 := by
    apply DyadicBivariateJetEnclosure.contains_coordinateA
    simpa using hva
  have hZ : (DyadicBivariateJetEnclosure.coordinateZ vz).Contains
      (BivariateJet2.affineZ zc z) 0 := by
    apply DyadicBivariateJetEnclosure.contains_coordinateZ
    simpa using hvz
  exact ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
    (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons hZ).cons hA

theorem initial_whole {va vz : DyadicInterval 40} {ac zc a z : ℝ}
    (hac : va.Contains ac) (ha : va.Contains a) (hzc : vz.Contains zc) (hz : vz.Contains z) :
    ∀ t ∈ Icc (0 : ℝ) 1, RegistersContain (initRegs va vz) (inputJets ac zc a z) t := by
  intro t ht
  have hA : (DyadicBivariateJetEnclosure.coordinateA va).Contains
      (BivariateJet2.affineA ac a) t := by
    apply DyadicBivariateJetEnclosure.contains_coordinateA
    exact DyadicInterval.contains_segment hac ha ht
  have hZ : (DyadicBivariateJetEnclosure.coordinateZ vz).Contains
      (BivariateJet2.affineZ zc z) t := by
    apply DyadicBivariateJetEnclosure.contains_coordinateZ
    exact DyadicInterval.contains_segment hzc hz ht
  exact ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
    (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons hZ).cons hA

theorem initial_sound (ac zc a z : ℝ) : ∀ i, ((inputJets ac zc a z).getD i zeroJet).DirectionalSoundOn
    (a - ac) (z - zc) (Icc (0 : ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a - ac) (z - zc) t := by
    simpa only [BivariateJet2.DirectionalSoundAt, BivariateJet2.projection_const]
      using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets ac zc a z) (a - ac) (z - zc) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst _)).cons (hconst _)).cons
      (BivariateJet2.soundOn_affineZ zc z (a - ac) _ t ht)).cons
      (BivariateJet2.soundOn_affineA ac a (z - zc) _ t ht)
  exact h i

theorem output_value (pay : List Payload) (regs : List (DyadicBivariateJetEnclosure 40))
    (hn : nonlinearCheck refShapes pay regs = true) (ac zc a z : ℝ) :
    ((finalJets (build40 refShapes pay regs) (inputJets ac zc a z)).getD 0 zeroJet).value 1 =
      ReflectionExpression.normalizedValue a z := by
  rw [finalJet_value, CorrectionProgramKernel.evalRealProgram_eq_of_shapes_eq
    (right := BivariateFastPilot.wholeProgram) (by rw [build40_shapes _ _ _ hn, refShapes_eq])]
  have hmap : List.map (fun j => j.value 1) (inputJets ac zc a z) = [a, z, 1, 2] := by
    simp [inputJets, BivariateJet2.affineA, BivariateJet2.affineZ, BivariateJet2.coordinateA,
      BivariateJet2.coordinateZ, BivariateJet2.const]
  rw [hmap, BivariateFastPilot.scalar_program, BivariateFastPilot.scalarCore_eq]

theorem sound_of_parts (c : CCell) (hbox : boxOk c = true)
    (hpc : progOk c.cpay (initRegs c.ca c.cz) = true)
    (hpw : progOk c.wpay (initRegs c.wa c.wz) = true)
    (ht : 0 < taylorQ (outBox c.cpay (initRegs c.ca c.cz)) (outBox c.wpay (initRegs c.wa c.wz))
      ((c.au - c.al) / 2) ((c.zu - c.zl) / 2))
    {a z : ℝ} (ha1 : (c.al : ℝ) ≤ a) (ha2 : a ≤ (c.au : ℝ))
    (hz1 : (c.zl : ℝ) ≤ z) (hz2 : z ≤ (c.zu : ℝ)) :
    0 < Reflection.curvature a (a * z) := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hal, halu⟩, hau⟩, hzl⟩, hzlu⟩, hzu⟩, hca⟩, hcz⟩, hwa1⟩, hwa2⟩, hwz1⟩, hwz2⟩ :=
    hbox
  simp only [progOk, Bool.and_eq_true] at hpc hpw
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
    (by rw [build40_shapes _ _ _ hpc.2, build40_shapes _ _ _ hpw.2])
    (initial_center hcA hcZ a z)
    (initial_whole (contains_of_memQ hwa1 hwa2 hacIn1 hacIn2) (contains_of_memQ hwa1 hwa2 ha1 ha2)
      (contains_of_memQ hwz1 hwz2 hzcIn1 hzcIn2) (contains_of_memQ hwz1 hwz2 hz1 hz2))
    (initial_sound _ _ a z)
    (accepted40_of_checks _ _ _ hpc.1 hpc.2)
    (accepted40_of_checks _ _ _ hpw.1 hpw.2)
    (by rw [hraR]; linarith) (by rw [hrzR]; linarith)
    (by rw [abs_le, hraR, hacR]; constructor <;> linarith)
    (by rw [abs_le, hrzR, hzcR]; constructor <;> linarith)
    hkey
  rw [output_value _ _ hpw.2] at hp
  exact Reflection.curvature_pos_of_normalizedValue_pos (by linarith) (by linarith)
    (by linarith) (by linarith) hp

theorem subsetCheck_self (b : DyadicBivariateJetEnclosure 40) : b.subsetCheck b = true := by
  simp [DyadicBivariateJetEnclosure.subsetCheck, DyadicInterval.subsetCheck]

theorem arithmeticStepCheck_self {shape : Shape} {boxes : List (DyadicBivariateJetEnclosure 40)}
    (hp : needsPayload shape = false) (hg : stepGuard shape boxes = true) :
    CorrectionHybridProgramKernel.arithmeticStepCheck shape boxes
      (arithmeticOutput shape boxes) = true := by
  cases shape with
  | add i j =>
      simp only [stepGuard, Bool.and_true] at hg
      simp only [CorrectionHybridProgramKernel.arithmeticStepCheck, arithmeticOutput, hg,
        subsetCheck_self, Bool.and_self]
  | neg i =>
      simp only [stepGuard, Bool.and_true] at hg
      simp only [CorrectionHybridProgramKernel.arithmeticStepCheck, arithmeticOutput, hg,
        subsetCheck_self, Bool.and_self]
  | mul i j =>
      simp only [stepGuard, Bool.and_true] at hg
      simp only [CorrectionHybridProgramKernel.arithmeticStepCheck, arithmeticOutput, hg,
        subsetCheck_self, Bool.and_self]
  | inv i =>
      simp only [stepGuard, Bool.and_eq_true] at hg
      simp only [CorrectionHybridProgramKernel.arithmeticStepCheck, arithmeticOutput,
        DyadicBivariateJetEnclosure.invCheck, hg.1, hg.2, subsetCheck_self, Bool.and_self]
  | log i => simp [needsPayload] at hp
  | contact i => simp [needsPayload] at hp

theorem runProg_sound : ∀ (shapes : List Shape) (payloads : List Payload)
    (boxes final : List (DyadicBivariateJetEnclosure 40)),
    runProg shapes payloads boxes = some final →
    CorrectionHybridProgramKernel.arithmeticCheck (build40 shapes payloads boxes) boxes = true ∧
    nonlinearCheck shapes payloads boxes = true ∧
    finalBoxes (build40 shapes payloads boxes) boxes = final
  | [], payloads, boxes, final, h => by
      simp only [runProg, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  | shape :: shapes, payloads, boxes, final, h => by
      cases hp : needsPayload shape with
      | false =>
          cases hg : stepGuard shape boxes with
          | false => simp [runProg, hp, hg] at h
          | true =>
              have h' : runProg shapes payloads (arithmeticOutput shape boxes :: boxes) =
                  some final := by
                simpa [runProg, hp, hg] using h
              obtain ⟨ha, hn, hf⟩ := runProg_sound shapes payloads _ final h'
              have hb : build40 (shape :: shapes) payloads boxes =
                  ⟨shape, arithmeticOutput shape boxes⟩ ::
                    build40 shapes payloads (arithmeticOutput shape boxes :: boxes) := by
                simp only [build40, hp, Bool.false_eq_true, ↓reduceIte]
              have hn' : nonlinearCheck (shape :: shapes) payloads boxes =
                  nonlinearCheck shapes payloads (arithmeticOutput shape boxes :: boxes) := by
                simp only [nonlinearCheck, hp, Bool.false_eq_true, ↓reduceIte]
              rw [hb, hn']
              refine ⟨?_, hn, hf⟩
              show (CorrectionHybridProgramKernel.arithmeticStepCheck shape boxes
                  (arithmeticOutput shape boxes) &&
                CorrectionHybridProgramKernel.arithmeticCheck
                  (build40 shapes payloads (arithmeticOutput shape boxes :: boxes))
                  (arithmeticOutput shape boxes :: boxes)) = true
              rw [arithmeticStepCheck_self hp hg, ha]
              rfl
      | true =>
          cases payloads with
          | nil => simp [runProg, hp] at h
          | cons payload rest =>
              cases hc : (decide (InRange shape boxes.length) && payloadCheck shape boxes payload) with
              | false => simp [runProg, hp, hc] at h
              | true =>
                  have h' : runProg shapes rest (payload.proposed :: boxes) = some final := by
                    simpa [runProg, hp, hc] using h
                  obtain ⟨ha, hn, hf⟩ := runProg_sound shapes rest _ final h'
                  have hc' := Bool.and_eq_true_iff.mp hc
                  have hb : build40 (shape :: shapes) (payload :: rest) boxes =
                      ⟨shape, payload.proposed⟩ :: build40 shapes rest (payload.proposed :: boxes) := by
                    simp only [build40, hp, ↓reduceIte]
                  have hn' : nonlinearCheck (shape :: shapes) (payload :: rest) boxes =
                      (payloadCheck shape boxes payload &&
                        nonlinearCheck shapes rest (payload.proposed :: boxes)) := by
                    simp only [nonlinearCheck, hp, ↓reduceIte]
                  rw [hb, hn', hc'.2, hn]
                  refine ⟨?_, rfl, hf⟩
                  show (CorrectionHybridProgramKernel.arithmeticStepCheck shape boxes payload.proposed &&
                    CorrectionHybridProgramKernel.arithmeticCheck
                      (build40 shapes rest (payload.proposed :: boxes))
                      (payload.proposed :: boxes)) = true
                  rw [ha, Bool.and_true]
                  cases shape with
                  | log i =>
                      simp only [CorrectionHybridProgramKernel.arithmeticStepCheck, hc'.1,
                        Bool.and_true]
                  | contact i =>
                      simp only [CorrectionHybridProgramKernel.arithmeticStepCheck, hc'.1,
                        Bool.and_true]
                  | add i j => simp [needsPayload] at hp
                  | neg i => simp [needsPayload] at hp
                  | mul i j => simp [needsPayload] at hp
                  | inv i => simp [needsPayload] at hp

theorem cellOk_sound (c : CCell) (hc : cellOk c = true) {a z : ℝ}
    (ha1 : (c.al : ℝ) ≤ a) (ha2 : a ≤ (c.au : ℝ)) (hz1 : (c.zl : ℝ) ≤ z) (hz2 : z ≤ (c.zu : ℝ)) :
    0 < Reflection.curvature a (a * z) := by
  simp only [cellOk, Bool.and_eq_true] at hc
  obtain ⟨hbox, hrun⟩ := hc
  cases hC : runProg refShapes c.cpay (initRegs c.ca c.cz) with
  | none => simp [hC] at hrun
  | some fc =>
      cases hW : runProg refShapes c.wpay (initRegs c.wa c.wz) with
      | none => simp [hC, hW] at hrun
      | some fw =>
          simp only [hC, hW, taylorOk, decide_eq_true_eq] at hrun
          obtain ⟨haC, hnC, hfC⟩ := runProg_sound _ _ _ _ hC
          obtain ⟨haW, hnW, hfW⟩ := runProg_sound _ _ _ _ hW
          refine sound_of_parts c hbox (by simp [progOk, haC, hnC]) (by simp [progOk, haW, hnW])
            ?_ ha1 ha2 hz1 hz2
          simpa [outBox, hfC, hfW] using hrun

end CKLaneC2R

end


