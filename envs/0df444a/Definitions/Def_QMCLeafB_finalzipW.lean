-- Prove2me | Definitions.Def_QMCLeafB_finalzipW
-- name    : QMCLeafB_finalzipW
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:21:15.563029+00:00
-- url     : https://prove2.me/theorems/94ea5832-4196-4b42-a67e-40e831652f04
-- title:
--   QMCLeafB finalzipW
-- statement:
--   # Leaf B phase 24 — m7, direction `final-zip`, part 2: the zip at the **reported round**
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_finalzip
import Definitions.Def_QMCLeafB_roundwrepoint
/-
# Leaf B phase 24 — m7, direction `final-zip`, part 2: the zip at the **reported round**

`Check_finalzip_m7` assembles the leaf at the phase-23 residual
`PartsM2.ResidParts campaignBit paramsKbc2`, whose bit is
`loopBit init0 RoundProgram.round verdict Tbc2`.  Its campaign-data plug `hok`
(`ok ⇒ RelaxMem` at the run's centres) is **not** the shelf's flag shape at that round:
`Check_verdbridge_m4` proves an `ok` answer of `RoundProgram.round` is the *upper* event
(`stT ≤ fvR`) and that the pinched centre of an `ok` state is then **not** a rational member
(`flagOf_false_of_oracleR_ok`), so at the shelf's round the `ok ⇒ member` plug cannot be discharged
at `cXp := cXst` — it can only be *assumed*, and only if some other member happens to exist at every
`ok` round.  At the reported round `OkLower.roundW` the same implication is a **theorem**
(`VerdictBridge.flag_true_of_okV`, used by `RoundWRepoint.hverdict_at_roundW0`).

So this file re-points the *composition* — not the geometry — from `campaignBit` to

    oW := loopBit InitDq.init0 OkLower.roundW RoundProgram.verdict Tbc2 ,

keeping the drift-free `RunParts` interface.  Three parts:

* §1 the residual `ResidPartsW` and the campaign data `PartsDataW` at `oW`, with the data asked
  **only at interior points** (the only place any `RunParts` producer is ever asked);
* §2 **the campaign data is constructible**: `dataW_of_state_plugs` builds `PartsDataW` with
  `rb := flagOf … cXst`, `cXp := cXst` from m4's `hverdict_at_roundW0` (four state plugs:
  symmetry, the exact descent's `false` at `ok` rounds, and the two flag-conditioned state facts).
  `hok` is then **definitional** (`FlagsM5.relaxMem_of_flagOf_true` — `flagOf` is an `if RelaxMem`);
* §3 the bit is `false` at an empty real body (via `hemptyR`, discharged in `Check_finalzip_m7`),
  the `hd` slot of the ending, and the verbatim `d9f601e5` sentence through phase-16's
  `LedgerW.solution_roundWG_of_init_hd_round` at `init := InitDq.init0`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.FinalZipW_M7

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.FinalStroke (loopBit noTape)
open QMCLeafB.OkLower (roundW okW)

/-- The reported-round programme bit, written out exactly as
`LedgerW.solution_roundWG_of_init_hd_round` states its `hd` slot (and as `RoundWRepoint.oW`). -/
def oW : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  loopBit QMCLeafB.InitDq.init0 roundW QMCLeafB.RoundProgram.verdict
    (fun G' _ => QMCLeafB.UnionShallow.Kbc2
      (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
      * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))

/-- The same bit as `RoundWRepoint.oW` (both are the loop bit of the reported round). -/
theorem oW_eq_repoint (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    oW G t = QMCLeafB.RoundWRepoint.oW G t := rfl

#print axioms QMCLeafB.FinalZipW_M7.oW_eq_repoint

/-! ## 1.  The residual and the data, at `oW` -/

/-- **The phase-23 residual at the reported round**: `RunParts` at every interior point whose real
relaxed body is nonempty, at `paramsKbc2`.  Same shape as `PartsM2.ResidParts`, round replaced. -/
abbrev ResidPartsW : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
    QMCLeafB.FinalStroke.RunParts oW G t (QMCLeafB.UnionShallow.paramsKbc2 G)

/-- **The campaign data at `oW`, asked at interior points only** — the only place a `RunParts`
producer is ever queried (`hd`'s own hypotheses).  `hok` is the slot
`FlagsM5.relaxMem_of_flagOf_true` supplies at this round. -/
structure PartsDataW where
  rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool
  cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    oW G t = QMCLeafB.SimLoop.anyOk (rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m)
  hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ∀ (k : ℕ), rb G t k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq

/-! ## 2.  The campaign data at `oW` is constructible

`rb`/`cXp` are the run's own flag stream and pinched centres
(`FlagsM5.flagOf` at `RecordsM2.cXst`, `RoundWRepoint.runW0`), the read-out equation is m4's
`hverdict_at_roundW0`, and `hok` is definitional because `flagOf` is `if RelaxMem then true else
false`.  What remains is m4's four state plugs — the production directions' obligation, unchanged. -/

/-- **`PartsDataW`, from the state plugs.**  `acc` is the descent's accumulator stream (a free
datum of `hverdict_at_roundW0`). -/
def dataW_of_state_plugs
    (acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc)
    (hsym : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ∀ (k : ℕ) (i j : Fin G.n),
        QMCLeafB.StateDiag.stMat G.n (stX (QMCLeafB.RoundWRepoint.runW0 G t k)) i j
          = QMCLeafB.StateDiag.stMat G.n (stX (QMCLeafB.RoundWRepoint.runW0 G t k)) j i)
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ∀ (k : ℕ), okW (QMCLeafB.RoundWRepoint.runW0 G t k) = true →
        (QMCLeafB.PivotProgram.runPiv
          (toRows (G.n, stX (QMCLeafB.RoundWRepoint.runW0 G t k)), acc G t k)).1 = false)
    (hdv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ∀ (k : ℕ),
        QMCLeafB.FlagsM5.flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
          (QMCLeafB.RecordsM2.cXst G.n (fun j => stX (QMCLeafB.RoundWRepoint.runW0 G t j))
            (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = true →
        dvR (QMCLeafB.RoundWRepoint.runW0 G t k) = 0)
    (hpivf : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ∀ (k : ℕ),
        QMCLeafB.FlagsM5.flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
          (QMCLeafB.RecordsM2.cXst G.n (fun j => stX (QMCLeafB.RoundWRepoint.runW0 G t j))
            (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = true →
        (QMCLeafB.RoundProgram.pivCut (QMCLeafB.RoundWRepoint.runW0 G t k)).1 = false) :
    PartsDataW where
  rb := fun G t k =>
    QMCLeafB.FlagsM5.flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
      (QMCLeafB.RecordsM2.cXst G.n (fun j => stX (QMCLeafB.RoundWRepoint.runW0 G t j))
        (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k
  cXp := fun G t k =>
    QMCLeafB.RecordsM2.cXst G.n (fun j => stX (QMCLeafB.RoundWRepoint.runW0 G t j))
      (QMCLeafB.UnionShallow.paramsKbc2 G).dq k
  hbit := fun G t hlo hhi =>
    QMCLeafB.RoundWRepoint.hverdict_at_roundW0 (G := G) (t := t) hlo hhi
      (X := fun j => stX (QMCLeafB.RoundWRepoint.runW0 G t j)) (acc := acc G t)
      (fun _ => rfl) (hsym G t hlo hhi) (hpiv G t hlo hhi) (hdv G t hlo hhi) (hpivf G t hlo hhi)
  hok := fun G t _ _ k hk =>
    QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t (QMCLeafB.UnionShallow.paramsKbc2 G)
      (QMCLeafB.RecordsM2.cXst G.n (fun j => stX (QMCLeafB.RoundWRepoint.runW0 G t j))
        (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k hk

#print axioms QMCLeafB.FinalZipW_M7.dataW_of_state_plugs

/-- **A `true` bit at `oW` forces the rational body nonempty** — the consequence of the data, now
with both directions available at this round. -/
theorem exists_member_of_bit_trueW (D : PartsDataW) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hbit : oW G t = true) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
  have h1 : QMCLeafB.SimLoop.anyOk (D.rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m) = true := by
    rw [← D.hbit G t hlo hhi]
    exact hbit
  obtain ⟨k, _hk, hokk⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff (D.rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m)).1 h1
  exact ⟨D.cXp G t k, D.hok G t hlo hhi k hokk⟩

#print axioms QMCLeafB.FinalZipW_M7.exists_member_of_bit_trueW

/-- **The campaign data is FREE at a `false`-bit point.**  `rb ≡ false` makes `anyOk` false, so
`hbit` is the hypothesis itself and `hok` is vacuous: at every interior point where the program's
bit is `false` — the whole sliver/crater class — the data plug costs nothing, and the residual
`ResidPartsW` is the *only* obligation there.  (`cXp` may be `0`; `hok` never fires.) -/
theorem partsDataW_pointwise_of_falseBit (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hbit : oW G t = false) :
    ∃ (rb : ℕ → Bool) (cXp : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ),
      oW G t = QMCLeafB.SimLoop.anyOk rb
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m) ∧
      (∀ (k : ℕ), rb k = true →
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp k)
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :=
  ⟨fun _ => false, fun _ => 0,
    by
      rw [hbit]
      exact (QMCLeafB.ResidRefute.anyOk_all_false (fun _ => false)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m) (fun _ _ => rfl)).symm,
    by intro k hk; simp at hk⟩

#print axioms QMCLeafB.FinalZipW_M7.partsDataW_pointwise_of_falseBit

/-! ## 3.  The bit is `false` at an empty real body, the `hd` slot, and the ending -/

/-- **The bit is `false` at an empty real body** (at interior points, where the data lives), with
`hemptyR` supplied by the shelf (`Check_finalzip_m7.hemptyR_parts`). -/
theorem bit_false_at_empty (D : PartsDataW) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
    oW G t = false :=
  fun hbody =>
    QMCLeafB.RefutedM3.bit_false_of_emptyBody (D.hbit G t hlo hhi) (D.hok G t hlo hhi)
      (QMCLeafB.FinalZipM7.hemptyR_parts G t hbody)

#print axioms QMCLeafB.FinalZipW_M7.bit_false_at_empty

/-- **`RunParts` at every interior point, at `oW`.**  Empty real body ⇒ `RefutedM3`'s drift-free
record with bit `false`; nonempty ⇒ the supplied residual.  This is `PartsM2.hdProp_of_parts` with
the round replaced and `hemptyR` discharged. -/
def hdW_of_data_parts (D : PartsDataW) (H : ResidPartsW) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (loopBit QMCLeafB.InitDq.init0 roundW QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  refine QMCLeafB.LedgerW.runParts_congr (o₁ := oW) ?_ rfl
  by_cases hbody : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn (bit_false_at_empty D G t hlo hhi hbody) hbody
  · have hbl : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X := by
      obtain ⟨X, hX⟩ := not_forall.mp hbody
      exact ⟨X, Classical.not_not.mp hX⟩
    exact H G t hn hlo hhi hbl

#print axioms QMCLeafB.FinalZipW_M7.hdW_of_data_parts

/-- **The leaf at the reported round**, from the residual and the campaign data.  The ending is
phase-16's `LedgerW.solution_roundWG_of_init_hd_round` with every init slot discharged at
`InitDq.init0`. -/
theorem solution_statement_at_roundW_of_parts (D : PartsDataW) (H : ResidPartsW) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LedgerW.solution_roundWG_of_init_hd_round QMCLeafB.InitDq.init0 20
    (by norm_num : 20 ≤ 2 ^ 20) QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init_normalised
    QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any QMCLeafB.InitDq.stOks_init0
    QMCLeafB.InitDq.init0_tape (hdW_of_data_parts D H)

#print axioms QMCLeafB.FinalZipW_M7.solution_statement_at_roundW_of_parts

/-- **`d9f601e5`, verbatim**, at the reported round. -/
theorem solution_at_roundW_of_parts (D : PartsDataW) (H : ResidPartsW) :
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
  solution_statement_at_roundW_of_parts D H

#print axioms QMCLeafB.FinalZipW_M7.solution_at_roundW_of_parts

/-- **Both zips prove the same sentence**: it is `FinishLine.SolutionStatement` by
`Check_finalzip_m7.statement_lock`. -/
theorem sentence_agreement :
    QMCLeafB.FinishLine.SolutionStatement =
      (∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :=
  QMCLeafB.FinalZipM7.statement_lock

#print axioms QMCLeafB.FinalZipW_M7.sentence_agreement

end QMCLeafB.FinalZipW_M7


