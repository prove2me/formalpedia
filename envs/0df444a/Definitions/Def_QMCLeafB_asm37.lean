-- Prove2me | Definitions.Def_QMCLeafB_asm37
-- name    : QMCLeafB_asm37
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:24:41.719226+00:00
-- url     : https://prove2.me/theorems/c95f3722-47bf-471f-ac77-e12d0ade2bd4
-- title:
--   QMCLeafB asm37
-- statement:
--   # `Check_asm37_m2` — phase 37, member m2, direction `assembly37`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm36_m8
import Definitions.Def_QMCLeafB_face36
import Definitions.Def_QMCLeafB_emptybody
/-
# `Check_asm37_m2` — phase 37, member m2, direction `assembly37`

**The assembly of leaf B (`d9f601e5`) with the residual cut down to the COLLAR.**

## What is taken as given (consumed, not re-derived)

* `Asm36M8.solution_of_selfRec (hok) (H : SelfRec)` — the verbatim sentence from the upper slot and
  the all-cut identity at the campaign programme (`Check_asm36_m8`);
* `Asm36M8.selfRec_of_split` — `FatBitTrue + ThinSelfRec ⟹ SelfRec`;
* `Face36M2.bodyRec_of_level` (ph36, m2) — **the record is FREE whenever the relaxation is contained
  in a rational level set** `{z | v ⬝ z = b}`, `v ≠ 0`: no content, no thinness, no programme.

## What this file adds

§1 `LevelContained` — the face condition as a *predicate on the relaxation* (the exact hypothesis of
   `bodyRec_of_level`), and `bodyRec_of_levelContained`: the face's record is a record of the
   campaign's own class (`ThinRec34M4.BodyRec`, definitionally the same object).
§2 **`CollarRec`** — the identity owed only on the COLLAR: bit-`false`, horizon-thin
   (`¬ Fat`), and NOT level-contained.  `thinSelfRec_of_collar` + `selfRec_of_fat_collar` show
   `{FatBitTrue, CollarRec} ⟹ SelfRec`, so **the face stratum leaves the residual**.
§3 `solution_of_fat_collar` — the verbatim `d9f601e5` sentence from `{hok, FatBitTrue, CollarRec}`,
   and its statement-locked twin.  At an ARBITRARY programme: `CollarRecG`, `selfRecG_of_split`,
   `solution_of_two_slots_collar`.
§4 The upper slot's exact reading at the campaign programme, machine-checked: `HokSlot`'s content is
   level-nonemptiness at `t − eps`; the campaign's own `ok` test sits at the level `t + eps`; the two
   levels are separated by `2·eps − dq/2 > 0` (`level_gap`, `dqShallow_le_eps`).  So `hok` is NOT a
   consequence of the campaign round's test — the gate must test membership at
   `levelOf = stT − epsOf + dq/2` (`level_gap_pos`), which is exactly m5/ph36's repair, and the
   radius-free refutations of the record class do not apply at the face.

Discipline: `set_option autoImplicit false`; no `sorry`, no `admit`, no `axiom`, no `native_decide`,
no `unsafe`; `#print axioms` after every load-bearing declaration.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Asm37M2

open QuantumMaxCutEnergy

/-! ## 1.  The face condition, as a predicate on the relaxation

`bodyRec_of_level` (ph36, m2) asks for a NONZERO rational direction `v` and a real level `b` such that
every point of the record's own relaxation `relaxBallP G t P` has `v ⬝ z = b`.  We name that
hypothesis, so that the collar can be defined as its negation. -/

/-- **The relaxation is contained in a rational level set** (the FACE of the thin stratum). -/
def LevelContained (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∃ (v : Fin (G.n * G.n) → ℚ) (b : ℝ), v ≠ 0 ∧
    ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P, QMCLeafB.Face36M2.vR v ⬝ᵥ z = b

#print axioms QMCLeafB.Asm37M2.LevelContained

/-- **The face's record, in the campaign's own record class.**  `Face36M2.BodyRec` and
`ThinRec34M4.BodyRec` are the same object (`Nonempty (RunParts falseBit G t P)`), and their
relaxations are the same set, so ph36's unconditional face record is a record of the class `SelfRec`
consumes. -/
theorem bodyRec_of_levelContained {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (h : LevelContained G t P) :
    QMCLeafB.ThinRec34M4.BodyRec G t P := by
  obtain ⟨v, b, hv, hface⟩ := h
  exact QMCLeafB.Face36M2.bodyRec_of_level (G := G) (t := t) (P := P) hn v hv b hface

#print axioms QMCLeafB.Asm37M2.bodyRec_of_levelContained

/-! ## 2.  The collar: the exact domain of the remaining identity -/

/-- **THE COLLAR.**  The all-cut identity, owed only at bit-`false` interior points whose body is
horizon-thin (`¬ Fat`) and NOT contained in a rational level set.  Both other strata are discharged
by banked theorems: empty bodies by `Asm36M8.selfRec_at_empty`, fat bodies by `FatBitTrue`
(the record class is empty there — `Asm36M8.not_bodyRec_of_fat`), and faces by §1. -/
def CollarRec : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    QMCLeafB.Pbit33.o33 G t = false → ¬ QMCLeafB.Asm36M8.Fat G t →
    ¬ LevelContained G t (QMCLeafB.Pbit33.P33 G) →
    QMCLeafB.ThinRec34M4.BodyRec G t (QMCLeafB.Pbit33.P33 G)

#print axioms QMCLeafB.Asm37M2.CollarRec

/-- **The thin identity from the collar identity**: off the collar the record is the face's, and the
face's record is unconditional. -/
theorem thinSelfRec_of_collar (H : CollarRec) : QMCLeafB.Asm36M8.ThinSelfRec := by
  intro G t hn hlo hlt hb hf
  by_cases hlc : LevelContained G t (QMCLeafB.Pbit33.P33 G)
  · exact bodyRec_of_levelContained hn hlc
  · exact H G t hn hlo hlt hb hf hlc

#print axioms QMCLeafB.Asm37M2.thinSelfRec_of_collar

/-- **`FatBitTrue + CollarRec ⟹ SelfRec`** — the composition of §2 with m8's split. -/
theorem selfRec_of_fat_collar (hFat : QMCLeafB.Asm36M8.FatBitTrue) (H : CollarRec) :
    QMCLeafB.Asm36M8.SelfRec :=
  QMCLeafB.Asm36M8.selfRec_of_split hFat (thinSelfRec_of_collar H)

#print axioms QMCLeafB.Asm37M2.selfRec_of_fat_collar

/-! ## 3.  The leaf from the upper slot and the collar -/

/-- **THE LEAF FROM `{hok, FatBitTrue, CollarRec}`.**  The verbatim sentence `d9f601e5`
(`FinishLine.SolutionStatement`) at the campaign programme.  Everything except the three binders is
banked: `Automatic.Poly o33` is `Pbit33.ho33`, the count is `Pbit33.hKm33`, the top slice is free
(`Pbit33.runParts33_top`), `n ≤ 1` is degenerate. -/
theorem solution_of_fat_collar (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (hFat : QMCLeafB.Asm36M8.FatBitTrue) (H : CollarRec) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_selfRec k hk hok (selfRec_of_fat_collar hFat H)

#print axioms QMCLeafB.Asm37M2.solution_of_fat_collar

/-- The same in the platform's own type (the `d9f601e5` sentence, written out). -/
theorem solution_of_fat_collar_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (hFat : QMCLeafB.Asm36M8.FatBitTrue) (H : CollarRec) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.Asm36M8.solution_of_selfRec_statement k hk hok (selfRec_of_fat_collar hFat H)

#print axioms QMCLeafB.Asm37M2.solution_of_fat_collar_statement

/-! ### 3b.  The same assembly at an ARBITRARY programme

A repaired, membership-equivalent gate re-points the bit, so the collar form is stated
programme-agnostically as well (it is the form a repaired-gate programme must instantiate). -/

/-- The collar identity at an arbitrary bit and parameter family. -/
def CollarRecG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false → ¬ QMCLeafB.Asm36M8.FatG G t (P G) →
    ¬ LevelContained G t (P G) → QMCLeafB.ThinRec34M4.BodyRec G t (P G)

#print axioms QMCLeafB.Asm37M2.CollarRecG

/-- The programme-side fat slot at an arbitrary bit. -/
def FatBitTrueG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    QMCLeafB.Asm36M8.FatG G t (P G) → o G t = true

#print axioms QMCLeafB.Asm37M2.FatBitTrueG

/-- `SelfRecG` from the fat slot and the collar slot, at any programme. -/
theorem selfRecG_of_split {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hFat : FatBitTrueG o P) (H : CollarRecG o P) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  by_cases hf : QMCLeafB.Asm36M8.FatG G t (P G)
  · exact absurd (hFat G t hn hlo hlt hf) (by rw [hb]; simp)
  · by_cases hlc : LevelContained G t (P G)
    · exact bodyRec_of_levelContained hn hlc
    · exact H G t hn hlo hlt hb hf hlc

#print axioms QMCLeafB.Asm37M2.selfRecG_of_split

/-- **THE LEAF AT ANY PROGRAMME, from `{Poly bit, count, top slice, hok, FatBitTrueG,
CollarRecG}`.** -/
theorem solution_of_two_slots_collar
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hFat : FatBitTrueG o P) (Hrec : CollarRecG o P) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_split hFat Hrec)

#print axioms QMCLeafB.Asm37M2.solution_of_two_slots_collar

/-! ## 4.  The upper slot's exact reading: `hok` is a LEVEL statement

`HokSlot` is, definitionally, level-nonemptiness at level `t − eps`: a bit-`true` point must carry a
symmetric rational member of the relaxation at level `t − eps G` and tolerance `dqShallow G`.  The
campaign's own round tests the objective against `t + epsOf` (`RoundT.roundT`).  The two levels are
separated by `2·eps − dq/2`, which is POSITIVE at every input of positive weight — so the campaign
gate is not the membership gate, and `hok` is not a consequence of the round's test.  This is the
machine-checked arithmetic behind m5/ph36's repair (`levelOf = stT − epsOf + dq/2`). -/

/-- The campaign's tolerance is exactly `Rq/40000`. -/
theorem eps_eq (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl

/-- The campaign's oracle tolerance is at most the slack, at positive weight. -/
theorem dqShallow_le_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G ≤ QMCLeafB.RundataCert.eps G := by
  have hzero : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRq
  rw [QMCLeafB.RundataParams.dqShallow, if_neg hzero]
  unfold QMCLeafB.RundataParams.dqShallowCore
  have hden : (1 : ℚ) ≤ 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by
    have := hRq
    linarith
  have hpos : (0 : ℚ) ≤ QMCLeafB.RundataCert.eps G := by
    rw [eps_eq]
    have := hRq
    linarith
  calc QMCLeafB.RundataCert.eps G / (9 * QMCLeafB.EngineRuntime.Rq G + 1)
      ≤ QMCLeafB.RundataCert.eps G / 1 := by
        exact div_le_div_of_nonneg_left hpos (by norm_num) hden
    _ = QMCLeafB.RundataCert.eps G := by ring

#print axioms QMCLeafB.Asm37M2.dqShallow_le_eps

/-- **THE LEVEL GAP**: the campaign's `ok` slack `t + eps` sits `2·eps − dq/2` ABOVE the membership
level `t − eps + dq/2`, and that separation is strictly positive at every input of positive
weight.  (`eps > 0` and `dq ≤ eps`.) -/
theorem level_gap (G : QuantumMaxCutEnergy.Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G / 2 < 2 * QMCLeafB.RundataCert.eps G := by
  have hle := dqShallow_le_eps G hRq
  have hpos : 0 < QMCLeafB.RundataCert.eps G := by
    rw [eps_eq]
    have := hRq
    linarith
  linarith

#print axioms QMCLeafB.Asm37M2.level_gap

/-- The same, in the form the two tests are compared by: the test level minus the membership
level. -/
theorem test_level_sub_mem_level (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (t + QMCLeafB.RundataCert.eps G)
        - (t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallow G / 2)
      = 2 * QMCLeafB.RundataCert.eps G - QMCLeafB.RundataParams.dqShallow G / 2 := by
  ring

#print axioms QMCLeafB.Asm37M2.test_level_sub_mem_level

/-- **`HokSlot`, unfolded**: it is exactly membership at the level `t − eps`, at every bit-`true`
interior bracket point.  No round, no centre, no gate. -/
theorem hokSlot_iff :
    Asm35M4.HokSlot ↔ ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) :=
  Iff.rfl

#print axioms QMCLeafB.Asm37M2.hokSlot_iff

/-- **The collar of `hok`**: a single bracketed point that is bit-`true` with NO member at level
`t − eps` refutes the upper slot outright.  This is the hook a programme-level falsification of the
campaign gate uses (and the reason the gate has to be re-pointed at the membership level). -/
theorem not_hokSlot_of_empty_level
    (h : ∃ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n ∧
      -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ∧
      QMCLeafB.Pbit33.o33 G t = true ∧
      ¬ ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ¬ Asm35M4.HokSlot := by
  intro hok
  obtain ⟨G, t, hn, hlo, hlt, hb, hno⟩ := h
  exact hno (hok G t hn hlo hlt hb)

#print axioms QMCLeafB.Asm37M2.not_hokSlot_of_empty_level


/-! ## 5.  The campaign gate is not the membership gate: a machine-checked straddle

The coordinator's step (A) reads "a round reports `ok` ⟹ the bit is TRUE and `hok` holds at that
round's own centre".  `hok`'s level is `t − eps` (§4).  The campaign round's test level is `t + eps`.
At `G₀` (two vertices, one edge of weight `1/2`) and the interior threshold `t₀ = −99999/100000`
there is an EXPLICIT member at the TEST level (`Xstar` below) and NO member at `hok`'s level
(`EmptyBodyM5.not_relaxMem_G₀`, phase 21) — the body is straddled by the campaign's slack `2·eps`.
So `hok` does not follow from the campaign round, and it *pins the bit*: it forces `o33` to read
`false` at `(G₀, t₀)`.  This is the exact programme-level price the coordinator's dichotomy has to
pay: the `ok` test must be re-pointed at `levelOf = stT − epsOf + dq/2` (m5/ph36's `okTopB`), where
case (A) is then definitional (`Grep36M5.mem_of_StateGateAt`). -/

/-- The explicit `2 × 2` member used for the receipt: the rank-one `1 1ᵀ` at `x = −1`. -/
def Xstar : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; -1, 1]

/-- The campaign's oracle tolerance at `G₀`, in the `HokSlot`'s own vocabulary. -/
theorem dqShallow_G₀ : QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀
    = QMCLeafB.EmptyBodyM5.dq₀ := by
  unfold QMCLeafB.EmptyBodyM5.dq₀ QMCLeafB.EmptyBodyM5.P₀
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]

#print axioms QMCLeafB.Asm37M2.dqShallow_G₀

theorem Xstar_symm : Xstarᵀ = Xstar := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xstar]

#print axioms QMCLeafB.Asm37M2.Xstar_symm

theorem frob_Xstar :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₀) Xstar = -1 := by
  rw [QMCLeafB.SepOracle.frob]
  simp [Xstar, Fin.sum_univ_two, QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_01,
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_10]
  norm_num

#print axioms QMCLeafB.Asm37M2.frob_Xstar

theorem qf_Xstar (x : Fin 2 → ℚ) :
    QMCLeafB.SepOracle.qf Xstar x = (x 0 - x 1) ^ 2 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum]
  simp [Xstar, Fin.sum_univ_two]
  ring

#print axioms QMCLeafB.Asm37M2.qf_Xstar

/-- **The receipt, half 1: the TEST level at `t₀` is inside the body.**  `Xstar` is a symmetric
rational member at level `t₀ + eps G₀` and the campaign's tolerance. -/
theorem mem_at_test_level_G₀ :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₀) Xstar
      (QMCLeafB.EmptyBodyM5.t₀ + QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₀)
      (QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀) := by
  have hdqpos : (0:ℚ) < QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀ :=
    QMCLeafB.RundataParams.dqShallow_pos _
  refine ⟨hdqpos, ?_, ?_, ?_⟩
  · intro x
    have hdq : (0:ℚ) ≤ QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀ := hdqpos.le
    have hq := qf_Xstar x
    have hsum : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : 0 ≤ (x 0 - x 1) ^ 2 := sq_nonneg _
    rw [hq]
    nlinarith
  · intro i
    fin_cases i <;> simp [Xstar] <;> have := hdqpos <;> linarith
  · rw [frob_Xstar, dqShallow_G₀, QMCLeafB.EmptyBodyM5.dq₀_eq,
      QMCLeafB.EmptyBodyM5.eps_G₀]
    unfold QMCLeafB.EmptyBodyM5.t₀
    norm_num

#print axioms QMCLeafB.Asm37M2.mem_at_test_level_G₀

/-- **The receipt, half 2: `hok`'s level at `t₀` is OUTSIDE the body** — no symmetric rational member
at all, by the phase-21 floor `⟪A,Q⟫ ≥ -(1 + 3δ/4)`. -/
theorem mem_level_empty_G₀ (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₀) Q
      (QMCLeafB.EmptyBodyM5.t₀ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₀)
      (QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀) := by
  rw [dqShallow_G₀]
  exact QMCLeafB.EmptyBodyM5.not_relaxMem_G₀ Q

#print axioms QMCLeafB.Asm37M2.mem_level_empty_G₀

/-- **THE STRADDLE**: at `(G₀, t₀)` the campaign's own `ok` slack is satisfiable while `hok`'s
membership level is empty.  So the campaign round supplies a member at ITS level, not at `hok`'s. -/
theorem level_straddle_G₀ :
    (∃ cX : Matrix (Fin 2) (Fin 2) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₀) cX
        (QMCLeafB.EmptyBodyM5.t₀ + QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₀)
        (QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀))
    ∧ (∀ cX : Matrix (Fin 2) (Fin 2) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₀) cX
        (QMCLeafB.EmptyBodyM5.t₀ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₀)
        (QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₀)) :=
  ⟨⟨Xstar, Xstar_symm, mem_at_test_level_G₀⟩, mem_level_empty_G₀⟩

#print axioms QMCLeafB.Asm37M2.level_straddle_G₀

/-- **`hok` PINS THE CAMPAIGN BIT.**  The upper slot forces the campaign's verdict bit to read
`false` at the interior point `(G₀, t₀)` — because a `true` bit there would demand a member at a level
the phase-21 floor proves empty.  This is a *checkable* consequence of the upper slot at the concrete
campaign programme; it is the programme-level content the repaired gate has to change. -/
theorem hok_forces_bit_false_G₀ (hok : Asm35M4.HokSlot) :
    QMCLeafB.Pbit33.o33 QMCLeafB.EmptyBodyM5.G₀ QMCLeafB.EmptyBodyM5.t₀ = false := by
  by_contra hcon
  have hb : QMCLeafB.Pbit33.o33 QMCLeafB.EmptyBodyM5.G₀ QMCLeafB.EmptyBodyM5.t₀ = true := by
    cases h : QMCLeafB.Pbit33.o33 QMCLeafB.EmptyBodyM5.G₀ QMCLeafB.EmptyBodyM5.t₀ with
    | false => exact absurd h hcon
    | true => rfl
  obtain ⟨cX, -, hmem⟩ :=
    hok _ _ (by unfold QMCLeafB.EmptyBodyM5.G₀; norm_num)
      QMCLeafB.EmptyBodyM5.t₀_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₀_mem_bracket.2 hb
  exact mem_level_empty_G₀ cX hmem

#print axioms QMCLeafB.Asm37M2.hok_forces_bit_false_G₀

/-- The same in refutation form: a `true` bit at `(G₀, t₀)` refutes the upper slot outright. -/
theorem not_hokSlot_of_bit_true_G₀
    (hb : QMCLeafB.Pbit33.o33 QMCLeafB.EmptyBodyM5.G₀ QMCLeafB.EmptyBodyM5.t₀ = true) :
    ¬ Asm35M4.HokSlot := by
  intro hok
  rw [hok_forces_bit_false_G₀ hok] at hb
  exact absurd hb (by simp)

#print axioms QMCLeafB.Asm37M2.not_hokSlot_of_bit_true_G₀

end QMCLeafB.Asm37M2


