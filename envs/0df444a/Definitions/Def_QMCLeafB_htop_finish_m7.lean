-- Prove2me | Definitions.Def_QMCLeafB_htop_finish_m7
-- name    : QMCLeafB_htop_finish_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:06:58.240835+00:00
-- url     : https://prove2.me/theorems/0dff2329-3b96-46df-abf0-8edccec71f4a
-- title:
--   QMCLeafB htop_finish_m7
-- statement:
--   # leaf B phase 16 — brick 3 `htop` finished (swarm `smw1ez4a9`, member m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_roundT_m7
import Definitions.Def_QMCLeafB_topSlice
import Definitions.Def_QMCLeafB_guard
/-
# leaf B phase 16 — brick 3 `htop` finished (swarm `smw1ez4a9`, member m7)

`htop` asks the loop's verdict bit to be `true` on the top slice `[-εr, 0]` of the driver's bracket.
The `roundT` design of `Check_roundT_m7` decides it: the `ok` test is moved to the campaign's own
slack, `fvR s ≤ stT s + epsOf s` with `epsOf s = (∑_{q ∈ stA s} |q|)/40000`, and `init0`'s code has
`fvR = 0` (`HtopInit.fvR_init0`), so the *first* round takes the `ok` branch exactly on the top slice
and `Htop.verdict_of_first_ok_of_one` carries it to every later round.

`Check_roundT_m7.htop_roundT` left two things open, and this file closes them:

1. the scalar identification `epsOf (init0 p) = Rq G / 40000` — i.e. the `ℓ¹` mass of the state's
   row-major weight code is `Rq G`.  `init0`'s code is `MatQ.mk n (wVal …)` *by definition*, so the
   flat list is already in `flatMap` form and no block-splitting lemma is needed: `sum_map_mk` and
   `MatQ.list_sum_range` turn `(A.map absq).sum` into `∑ i, ∑ j, |wMatQ i j|`, which is
   `RStInit.abs_sum_wMatQ`.
2. the **verdict agreement** at `roundT`.  `RunParts.hverdict` compares the loop's bit with
   `SimLoop.anyOk ok (K*m)` where `ok` is the run's own `ok`-flag stream;
   `RStInit.verdict_iterate_eq_anyOk` proves that at `RoundProgram.round`, and a `roundT` run needs
   its own version, since the extra `ok` branch appends a flag the oracle did not report.
   `stOks_roundT` reads the appended flag off the state, `stOks_iterateT` unrolls the orbit, and
   `verdict_iterate_eq_anyOk_T` is the equation.  `okOfT` is the flag stream in question.

Then `htop_roundT_of_one_le` is `htop` for *any* positive round count — the driver's count is
`K*m` for either candidate family (`Kpow d m`, `Kbc m`), so both concrete instances are supplied.
`soundEpsOnBracket_roundT` is the form the closing stroke consumes: the top slice is discharged here
and `hd` is only asked on the interior `[-Rq, -εr)`.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.HtopFinish

open QuantumMaxCutEnergy
open QMCNumericRuntime
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-! ## 1.  `epsOf` at `init0`: the state's own `ℓ¹` mass is `Rq G`

`massV s = ((stA s).map absq).sum`; at `init0` the code `stA` is `MatQ.mk G.n (wVal …)`, which is a
`flatMap` of rows, so the mass is the double sum of the absolute entries — `abs_sum_wMatQ`. -/

/-- Summing a mapped `flatMap` is summing the blocks. -/
theorem sum_map_flatMap {α : Type} (l : List α) (h : α → List ℚ) (f : ℚ → ℚ) :
    ((l.flatMap h).map f).sum = (l.map (fun a => ((h a).map f).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- `(l.map g).map f = l.map (fun i => f (g i))`, with the composite written out (the `∘` form is
only propositionally equal, so it needs this lemma rather than `rfl`). -/
theorem map_comp_eq (l : List ℕ) (f : ℚ → ℚ) (g : ℕ → ℚ) :
    (l.map g).map f = l.map (fun i => f (g i)) := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]

/-- **The `ℓ¹` mass of a `MatQ.mk` code** is the double sum of the absolute entries. -/
theorem sum_map_mk (n : ℕ) (g : ℕ → ℕ → ℚ) (f : ℚ → ℚ) :
    ((MatQ.mk n g).map f).sum
      = ((List.range n).map (fun i => ((List.range n).map (fun j => f (g i j))).sum)).sum := by
  unfold MatQ.mk
  rw [sum_map_flatMap]
  simp only [map_comp_eq]

/-- **The code of `init0` is `MatQ.mk G.n (wVal …)`.** -/
theorem stA_init0_eq_mk (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    QMCLeafB.RoundProgram.stA (QMCLeafB.RStInit.init0 ((G, coins), t))
      = MatQ.mk G.n (QMCLeafB.RStInit.wVal (inputEdges G)) := by
  rw [QMCLeafB.RStInit.stA_init0, QMCLeafB.RStInit.wProg_eq,
    QMCNumericRuntime.inputWidth_request, QMCNumericRuntime.parseEdges_request]

/-- **`wVal` reads off `wMatQ G`.** -/
theorem wVal_eq_wMatQ (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ)
    (i j : Fin G.n) :
    QMCLeafB.RStInit.wVal (inputEdges G) (i : ℕ) (j : ℕ)
      = QMCLeafB.RStInit.wMatQ G i j := by
  have h := QMCLeafB.RStInit.stA_correct G coins t
  have h2 : MatQ.entry G.n (QMCLeafB.RoundProgram.stA
      (QMCLeafB.RStInit.init0 ((G, coins), t))) i j = QMCLeafB.RStInit.wMatQ G i j := h.2 i j
  rw [stA_init0_eq_mk, MatQ.entry_mk G.n _ i.isLt j.isLt] at h2
  exact h2

/-- **The `ℓ¹` mass of the initial state's weight code is `Rq G`.** -/
theorem massV_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 := by
  obtain ⟨⟨G, coins⟩, t⟩ := p
  unfold QMCLeafB.RoundT.massV
  rw [stA_init0_eq_mk, sum_map_mk,
    MatQ.list_sum_range
      (fun i => ((List.range G.n).map
        (fun j => QMCLeafB.RoundProgram.absq
          (QMCLeafB.RStInit.wVal (inputEdges G) i j))).sum) G.n]
  rw [← QMCLeafB.RStInit.abs_sum_wMatQ G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MatQ.list_sum_range
    (fun j => QMCLeafB.RoundProgram.absq
      (QMCLeafB.RStInit.wVal (inputEdges G) i j)) G.n]
  exact Finset.sum_congr rfl fun j _ => by
    rw [QMCLeafB.RoundProgram.absq_eq, wVal_eq_wMatQ G coins t i j]

/-- **The state's slack at `init0` is the campaign's `εw = Rq G / 40000`.** -/
theorem epsOf_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.RStInit.init0 p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_init0]
  ring


/-! ## 2.  The verdict agreement at `roundT`

`hverdict` (in `RunParts`) says the loop's bit is `SimLoop.anyOk ok (K*m)` for the run's own `ok`
stream.  `RStInit.verdict_iterate_eq_anyOk` proves that at `RoundProgram.round`; `roundT` has an
*extra* `ok` branch, whose flag the oracle never sees, so it needs its own read-out.  `okOfT` is that
flag stream and `verdict_iterate_eq_anyOk_T` is the equation. -/

/-- **The flag `roundT` appends**, read off the state. -/
theorem stOks_roundT (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT s)
      = QMCLeafB.RoundProgram.stOks s
        ++ [if QMCLeafB.RoundProgram.fvR s
              ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
            then true else !((QMCLeafB.RoundProgram.oracleR s).1)] := by
  by_cases h : QMCLeafB.RoundProgram.fvR s
      ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [QMCLeafB.RoundT.roundT, if_pos h, if_pos h]
    simp [QMCLeafB.RoundProgram.roundOk]
  · rw [QMCLeafB.RoundT.roundT, if_neg h, QMCLeafB.RStInit.stOks_round, if_neg h]

/-- **The `ok` stream of a `roundT` run**, as a function of the state it starts from. -/
noncomputable def okOfT (s : QMCLeafB.RoundProgram.RSt) (k : ℕ) : Bool :=
  if QMCLeafB.RoundProgram.fvR (QMCLeafB.RoundT.roundT^[k] s)
      ≤ QMCLeafB.RoundProgram.stT (QMCLeafB.RoundT.roundT^[k] s)
        + QMCLeafB.RoundT.epsOf (QMCLeafB.RoundT.roundT^[k] s)
    then true else !((QMCLeafB.RoundProgram.oracleR (QMCLeafB.RoundT.roundT^[k] s)).1)

/-- **The flag list after `T` rounds of `roundT`.** -/
theorem stOks_iterateT (s : QMCLeafB.RoundProgram.RSt) (T : ℕ) :
    QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[T] s)
      = QMCLeafB.RoundProgram.stOks s ++ (List.range T).map (fun k => okOfT s k) := by
  induction T with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundT, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]
      rfl

/-- **`hverdict` at `roundT`**: the loop's bit is `anyOk` of the flags `roundT` appends. -/
theorem verdict_iterate_eq_anyOk_T (s : QMCLeafB.RoundProgram.RSt)
    (hs : QMCLeafB.RoundProgram.stOks s = []) (T : ℕ) :
    QMCLeafB.RoundProgram.verdict (QMCLeafB.RoundT.roundT^[T] s)
      = QMCLeafB.SimLoop.anyOk (okOfT s) T := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_iterateT, hs, List.nil_append]
  exact QMCLeafB.RStInit.decide_pos_filter_map_range (okOfT s) T

/-- **`hverdict` on the loop's own `o`**: the concrete bit at `(G,t)` is `anyOk` of the run's flags. -/
theorem loopBit_eq_anyOk_T (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.SimLoop.anyOk
          (okOfT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) (T0 G t) :=
  verdict_iterate_eq_anyOk_T _ (QMCLeafB.RStInit.stOks_init0 _) (T0 G t)

/-! ## 3.  `htop` at `roundT`, for any positive round count

The first round is `ok` on the whole top slice — `fvR (init0 …) = 0` and `epsOf (init0 …) = Rq/40000`
— and the flag is never lost, so the verdict is `true` at every round count `≥ 1`.  The count is
`K*m` in every candidate parameter family, hence the two concrete instances below. -/

/-- **`htop` for `roundT` at any positive count, for EVERY order.**

Note the absence of `2 ≤ G.n`: the route below never uses the refutation half of the soundness
stroke, only the feasible one (the identity at the top of the bracket), which is available at every
order.  This matters because `VerdictSound.soundEpsOnBracket_of_runData_interior`,
`FuelWire.solution_of_runParts_interior_halve` and `Conformance.solution_union` ask `htop` for *all*
`G`, and at `RoundProgram.round` that form is FALSE (`TopSliceRange.htop_interior_false`) — that
falsity is what forced the `2 ≤ G.n` detour of `TopSliceRange`.  At `roundT` it is true, so the
unrestricted strokes are usable again. -/
theorem htop_roundT_all (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0 G t = true := by
  intro G t hlo _
  have hlo' : -(QMCLeafB.EngineRuntime.Rq G / 40000) ≤ t := by exact_mod_cast hlo
  have hslack : 0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) := by
    rw [epsOf_init0]
    show 0 ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000
    linarith
  exact QMCLeafB.RoundT.htop_roundT G t (hpos G t) hslack

/-- **`htop` for `roundT` at `2 ≤ G.n`** — the form the phase-16 routing asks for (a corollary of the
unrestricted version). -/
theorem htop_roundT (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0 G t = true :=
  fun G t _ hlo hhi => htop_roundT_all T0 hpos G t hlo hhi

/-- **The agreement of the two halves of the verdict on the top slice**: the `anyOk` read-out the
interior run's `hverdict` produces is `true` there too, so a `RunParts` bundle covering the whole
bracket is consistent with `htop`. -/
theorem anyOk_okOfT_eq_true (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.SimLoop.anyOk
      (okOfT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) (T0 G t) = true := by
  rw [← loopBit_eq_anyOk_T T0 G t]
  exact htop_roundT T0 hpos G t hn hlo hhi

/-- **`htop` at the monomial round count** `Kpow d m G · m` (`FuelWire.endgame_of_fuel_interior_monomial`'s
family). -/
theorem htop_roundT_Kpow (d m : ℕ) (hm1 : 1 ≤ m) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.FuelWire.Kpow d m G' * m) G t = true :=
  htop_roundT _ (fun G _ => by
    have h1 : 1 ≤ QMCLeafB.FuelWire.Kpow d m G :=
      hm1.trans (Nat.le_add_left m ((G.n + 1) ^ d))
    calc (1 : ℕ) = 1 * 1 := by norm_num
      _ ≤ QMCLeafB.FuelWire.Kpow d m G * m := Nat.mul_le_mul h1 hm1)

/-- **`htop` at m1's round-count factor** `Kbc (mf G) G · mf G`, with a per-order halving time `mf`.
This is the count of `Conformance.solution_union`, of `FuelWire.solution_of_runParts_interior_halve`
and of `UnionShallow.solution_union_shallow` (`mf = mHalve (n·n)`, `KbcShallow = Kbc (mHalve …)`). -/
theorem htop_roundT_KbcF (mf : QuantumMaxCutEnergy.Input → ℕ) (hm : ∀ G, 1 ≤ mf G) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.FuelWire.Kbc (mf G') G' * mf G') G t = true :=
  htop_roundT (fun G' _ => QMCLeafB.FuelWire.Kbc (mf G') G' * mf G') (fun G _ => by
    have hm1 : 0 < mf G := by have := hm G; omega
    have h2 : 0 < (G.n + 1) ^ 2
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10) :=
      Nat.mul_pos (pow_pos (by omega : 0 < G.n + 1) 2)
        (by omega : 0 < QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10)
    rw [QMCLeafB.FuelWire.Kbc_eq]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos hm1 h2) hm1))

/-- **`htop` at the campaign's shallow round factor** `KbcShallow G · mHalve (n·n)` — the exact `htop`
slot `UnionShallow.solution_union_shallow` leaves open. -/
theorem htop_roundT_shallow :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
          * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true :=
  htop_roundT_KbcF (fun G => QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (fun G => QMCLeafB.HalvePerG.one_le_mHalve (G.n * G.n))

/-! ## 4.  The top slice discharged: `SoundεOnBracket` from the interior run only

`soundEpsOnBracket_of_runData_interior_hn` asks `htop` on the top slice and `RunData` on the interior.
The first is now a theorem, so a closing stroke over `roundT` only has to supply the run bundle on
`[-Rq, -εr)`. -/

/-- **`SoundεOnBracket` at the `roundT` loop from the interior run bundle** — the *unrestricted*
stroke `VerdictSound.soundEpsOnBracket_of_runData_interior`, made available by `htop_roundT_all`.
`hd` is only asked on the interior `[-Rq, -εr)`. -/
theorem soundEpsOnBracket_roundT
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ) (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t)
    (P : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict T0) G t (P G)) :
    QMCLeafB.FinishLine.SoundεOnBracket
      (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0) :=
  QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior _
    (htop_roundT_all T0 hpos)
    (fun G t hn hlo hlt => (hd G t hn hlo hlt).toRunData)

/-! ## 5.  Two facts about `dvR` at `init0` — the diagonal repair is NOT free there

`dvR s = ∑ᵢ |Xᵢᵢ − 1|` is the engine's unit-diagonal test: `oracleR` answers **cut** with the
diagonal-repair normal `sign (1 − Xᵢᵢ)` whenever `dvR s ≠ 0`, and only then consults the threshold /
PSD branches.  `init0` packs `initShapeOf n (MOf n) = (MOf n)⁻¹ • 1` with `MOf n = 2n² + 2 ≥ 4`, so
its diagonal is `1/MOf n ≠ 1` and `dvR ≠ 0`.

Two consequences, both relevant to the closing chain:

* `dvR (init0 p) ≠ 0`, so the slack test can **not** be strengthened by a `dvR s = 0` conjunct: that
  would lose `htop` at the top of the bracket (where the very first round has to report `ok`, and the
  only state available is `init0`).  (`ConformanceM8`'s finding on `RunParts.hcert` proposes exactly
  that conjunct; this is the reason it is unavailable as long as `init0` packs `initShapeOf`.)
* at the top-slice `ok` round the state's own shape is not unit-diagonal, so it is not an
  `IsUnitDiagPSD` witness either; the top slice needs no witness (`exists_trace_le_of_neg_eps_le`),
  but an `hcert` read off the state at a slack-`ok` round of the *interior* run must come from
  somewhere else — `dvR = 0` is not an invariant of the orbit.
-/

/-- `entV` is `MatQ.entry`: the two read the row-major code the same way. -/
theorem entV_eq_entry (n : ℕ) (X : List ℚ) (i j : ℕ) :
    QMCLeafB.RoundProgram.entV (n, X) i j = MatQ.entry n X i j := rfl

/-- A constant map sums to `n · c`. -/
theorem sum_map_const (n : ℕ) (c : ℚ) :
    ((List.range n).map (fun _ => c)).sum = (n : ℚ) * c := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp
      ring

/-- A mapped list only sees the values on the list. -/
theorem list_map_congr {l : List ℕ} {f g : ℕ → ℚ} (h : ∀ i ∈ l, f i = g i) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.map_cons, h a (List.mem_cons_self ..),
        ih (fun i hi => h i (List.mem_cons_of_mem a hi))]

/-- **`dvR` does not vanish at `init0`**: the packed shape is `(MOf n)⁻¹ • 1` and `MOf n ≥ 4`. -/
theorem dvR_init0_ne_zero (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    (hn : 1 ≤ QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)) :
    QMCLeafB.RoundProgram.dvR (QMCLeafB.RStInit.init0 p) ≠ 0 := by
  have hlen : (QMCLeafB.RoundProgram.stX (QMCLeafB.RStInit.init0 p)).length
      = QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)
        * QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p) :=
    QMCLeafB.RStInit.stX_length p
  have hdiag : ∀ i : Fin (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)),
      MatQ.entry (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p))
        (QMCLeafB.RoundProgram.stX (QMCLeafB.RStInit.init0 p)) i i
      = (QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)))⁻¹ := by
    intro i
    rw [(QMCLeafB.RStInit.stX_correct p).2 i i, QMCLeafB.InitVerdict.initShapeOf_apply]
    simp
  have hM : QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)) ≠ 1 := by
    intro h
    have h2 : QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p))
        = 2 * ((QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p) : ℚ)) ^ 2 + 2 * (1 : ℚ) := by
      rw [QMCLeafB.InitVerdict.MOf_eq]
      norm_num [QMCLeafB.InitVerdict.dqV]
    rw [h2] at h
    nlinarith [sq_nonneg ((QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p) : ℚ))]
  have hterm : QMCLeafB.RoundProgram.absq
      ((QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)))⁻¹ - 1)
      ≠ 0 := by
    intro h0
    have h1 : (QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)))⁻¹
        - 1 = 0 := by
      have habs := QMCLeafB.RoundProgram.absq_eq
        ((QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)))⁻¹ - 1)
      rw [habs, abs_eq_zero] at h0
      exact h0
    exact hM (inv_eq_one.mp (by linarith))
  unfold QMCLeafB.RoundProgram.dvR QMCLeafB.RoundProgram.diagSumV
  rw [QMCLeafB.HtopInit.idxs_eq_range hlen]
  have hmap : (List.map (fun i => QMCLeafB.RoundProgram.absq
      (QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p),
        QMCLeafB.RoundProgram.stX (QMCLeafB.RStInit.init0 p)) i i - 1))
      (List.range (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p))))
      = (List.map (fun _ => QMCLeafB.RoundProgram.absq
          ((QMCLeafB.InitVerdict.MOf (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)))⁻¹
            - 1))
          (List.range (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p)))) := by
    apply list_map_congr
    intro i hi
    have hi' : i < QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p) := List.mem_range.mp hi
    rw [entV_eq_entry, hdiag ⟨i, hi'⟩]
  rw [hmap]
  rw [sum_map_const]
  have hNpos : (0 : ℚ) < (QMCLeafB.RoundProgram.stN (QMCLeafB.RStInit.init0 p) : ℚ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  exact mul_ne_zero (ne_of_gt hNpos) hterm

/-- **`dvR (init0 p) ≠ 0` at every real order** (`1 ≤ G.n`).  The hypothesis of the previous lemma,
read at `noTape`. -/
theorem dvR_init0_noTape_ne_zero (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 1 ≤ G.n) :
    QMCLeafB.RoundProgram.dvR
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) ≠ 0 := by
  refine dvR_init0_ne_zero _ ?_
  rw [QMCLeafB.RStInit.stN_init0]
  exact hn

/-! ## 6.  The interface brick 4 needs from the verdict agreement

`RunParts.hverdict` is `o G t = anyOk ok (P.K * P.m)`: it asks for the loop's bit *as a number of
rounds `K*m`*, while `loopBit_eq_anyOk_T` gives `anyOk (okOfT (init0 …)) (T0 G t)`.  The two meet once
the run's own `ok` stream agrees pointwise with `okOfT` on the first `K*m` rounds and `K*m` is the
count — that is `hverdict_of_flags` below, and it is the only step brick 4 has to feed.

`okOfT_zero_of_interior` is the one flag that costs nothing: on the interior of the bracket the slack
test cannot fire at round `0` (`fvR (init0 …) = 0 > t + εw`), so the first recorded flag is exactly
the engine's `ok` bit. -/

/-- `anyOk` only reads finitely many flags. -/
theorem anyOk_congr {f g : ℕ → Bool} : ∀ T : ℕ, (∀ k, k < T → f k = g k) →
    QMCLeafB.SimLoop.anyOk f T = QMCLeafB.SimLoop.anyOk g T
  | 0, _ => rfl
  | (k + 1), h => by
      rw [QMCLeafB.SimLoop.anyOk_succ, QMCLeafB.SimLoop.anyOk_succ, h k (by omega),
        anyOk_congr k (fun j hj => h j (by omega))]

/-- **`hverdict` from a pointwise flag agreement.**  If the run's recorded `ok` stream is `okOfT`'s
stream on the `K*m` rounds of the run, the loop's bit *is* the run's `anyOk`. -/
theorem hverdict_of_flags (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (K m : ℕ) (hKm : K * m = T0 G t)
    (ok : ℕ → Bool) (hok : ∀ k, k < K * m → ok k = okOfT (QMCLeafB.RStInit.init0
      (QMCLeafB.FinalStroke.noTape G t)) k) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.SimLoop.anyOk ok (K * m) := by
  rw [loopBit_eq_anyOk_T, ← hKm]
  exact anyOk_congr (K * m) (fun k hk => (hok k hk).symm)

/-- **On the interior of the bracket the first flag is the engine's own `ok` bit.** -/
theorem okOfT_zero_of_interior (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    okOfT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) 0
      = !((QMCLeafB.RoundProgram.oracleR
          (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))).1) := by
  have hfv : QMCLeafB.RoundProgram.fvR
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = 0 :=
    QMCLeafB.HtopInit.fvR_init0 G t
  have hst : QMCLeafB.RoundProgram.stT
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = t :=
    QMCLeafB.RStInit.stT_init0 _
  have heps : QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := epsOf_init0 _
  have hr : (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < 0 := by linarith
  have hq : t + QMCLeafB.EngineRuntime.Rq G / 40000 < 0 := by exact_mod_cast hr
  have hlt : ¬ (QMCLeafB.RoundProgram.fvR
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
        ≤ QMCLeafB.RoundProgram.stT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
          + QMCLeafB.RoundT.epsOf
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) := by
    rw [hfv, hst, heps]
    intro hle
    linarith
  unfold okOfT
  simp only [Function.iterate_zero_apply, hlt, if_false]

/-- The flag lists of `roundU`/`roundT` runs are nested (one flag per round). -/
theorem stOks_prefix_iterateT (s : QMCLeafB.RoundProgram.RSt) {j₀ j : ℕ} (h : j₀ ≤ j) :
    QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[j₀] s)
      <+: QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[j] s) := by
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j _ ih =>
      refine ih.trans ?_
      have hstep : QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[j + 1] s)
          = QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[j] s)
            ++ [if QMCLeafB.RoundProgram.fvR (QMCLeafB.RoundT.roundT^[j] s)
                  ≤ QMCLeafB.RoundProgram.stT (QMCLeafB.RoundT.roundT^[j] s)
                    + QMCLeafB.RoundT.epsOf (QMCLeafB.RoundT.roundT^[j] s) then true
                else !((QMCLeafB.RoundProgram.oracleR (QMCLeafB.RoundT.roundT^[j] s)).1)] := by
        rw [Function.iterate_succ_apply']
        exact stOks_roundT _
      rw [hstep]
      exact List.prefix_append _ _

/-! ## 7.  `roundU`: one program that is `roundT` on the top slice and `round` on the interior

`roundT` decides `htop` but breaks the `hcert` side of `hd`: its extra `ok` branch fires on the
*state's* slack test, and a state's shape carries no `IsUnitDiagPSD` (nor even `RelaxMem`)
certificate, so a slack-`ok` round of an interior run has no witness.  `RunParts`' machinery, on the
other hand, is built for the engine's own `ok` bit — `RelaxMem` at the centre for `ok = true`,
`RelaxCut` for `ok = false` (`Check_runparts_dilate_m5`'s `hmem`/`C`), and `RunParts.hverdict` wants
that very stream.

The two regimes are separated by the sign of `t + εw`, and **that sign is a run invariant**: the
round freezes `stT` (`RStInit.stT_round`) and `stA` (`RStInit.stA_round`), and `epsOf` reads only
`stA` (`epsOf = massV stA / 40000`).  So

    roundU s := if 0 ≤ stT s + epsOf s then roundT s else round s

is `roundT` for the whole orbit of a top-slice start (where the first round reports `ok` and the state
freezes) and *literally `round`* for the whole orbit of an interior start.  Consequently

* `htop_roundU` : the loop's bit is `true` on the top slice (from `htop_roundT_all`);
* `loopBit_U_eq_anyOk_engine` : on the interior the loop's bit is `anyOk` of the **engine's** own
  stream `!((oracleR (round^[k] …)).1)` — `RStInit.loopBit_eq_anyOk_of_count` verbatim, so brick 4
  gets `hverdict` and the `hmem`/`C` dichotomy with no extra certificate to invent.

This is the ok-test the closing chain should run: it keeps `htop` (brick 3) and keeps the `hd` side
(brick 4) exactly as the relax-oracle bricks state it.  `roundGU` below is the same round behind
m1's normalisation guard, which is what the size ledger needs.
-/

/-- `roundT` keeps the threshold. -/
theorem stT_roundT (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stT (QMCLeafB.RoundT.roundT s) = QMCLeafB.RoundProgram.stT s := by
  unfold QMCLeafB.RoundT.roundT
  split_ifs with h
  · rfl
  · exact QMCLeafB.RStInit.stT_round s

/-- `roundT` keeps the weight code. -/
theorem stA_roundT (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stA (QMCLeafB.RoundT.roundT s) = QMCLeafB.RoundProgram.stA s := by
  unfold QMCLeafB.RoundT.roundT
  split_ifs with h
  · rfl
  · exact QMCLeafB.RStInit.stA_round s

/-- **The reported round**: `roundT` above the campaign slack, the engine's own `round` below it. -/
noncomputable def roundU (s : QMCLeafB.RoundProgram.RSt) : QMCLeafB.RoundProgram.RSt :=
  if 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s then QMCLeafB.RoundT.roundT s
  else QMCLeafB.RoundProgram.round s

/-- **The flag `roundU` appends.** -/
noncomputable def okU (s : QMCLeafB.RoundProgram.RSt) : Bool :=
  if 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s then
    (if QMCLeafB.RoundProgram.fvR s
        ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s then true
     else !((QMCLeafB.RoundProgram.oracleR s).1))
  else !((QMCLeafB.RoundProgram.oracleR s).1)

theorem roundU_of_top (s : QMCLeafB.RoundProgram.RSt)
    (h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s) :
    roundU s = QMCLeafB.RoundT.roundT s := by
  unfold roundU
  rw [if_pos h]

theorem roundU_of_interior (s : QMCLeafB.RoundProgram.RSt)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s)) :
    roundU s = QMCLeafB.RoundProgram.round s := by
  unfold roundU
  rw [if_neg h]

theorem stT_roundU (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stT (roundU s) = QMCLeafB.RoundProgram.stT s := by
  by_cases h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundU_of_top s h, stT_roundT]
  · rw [roundU_of_interior s h, QMCLeafB.RStInit.stT_round]

theorem stA_roundU (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stA (roundU s) = QMCLeafB.RoundProgram.stA s := by
  by_cases h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundU_of_top s h, stA_roundT]
  · rw [roundU_of_interior s h, QMCLeafB.RStInit.stA_round]

theorem stT_iterateU (s : QMCLeafB.RoundProgram.RSt) (k : ℕ) :
    QMCLeafB.RoundProgram.stT (roundU^[k] s) = QMCLeafB.RoundProgram.stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundU, ih]

theorem stA_iterateU (s : QMCLeafB.RoundProgram.RSt) (k : ℕ) :
    QMCLeafB.RoundProgram.stA (roundU^[k] s) = QMCLeafB.RoundProgram.stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundU, ih]

theorem stA_iterateT (s : QMCLeafB.RoundProgram.RSt) (k : ℕ) :
    QMCLeafB.RoundProgram.stA (QMCLeafB.RoundT.roundT^[k] s)
      = QMCLeafB.RoundProgram.stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundT, ih]

theorem stT_iterateT (s : QMCLeafB.RoundProgram.RSt) (k : ℕ) :
    QMCLeafB.RoundProgram.stT (QMCLeafB.RoundT.roundT^[k] s)
      = QMCLeafB.RoundProgram.stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundT, ih]

/-- `epsOf` reads the state only through its weight code `stA`. -/
theorem epsOf_congr {s s' : QMCLeafB.RoundProgram.RSt}
    (h : QMCLeafB.RoundProgram.stA s = QMCLeafB.RoundProgram.stA s') :
    QMCLeafB.RoundT.epsOf s = QMCLeafB.RoundT.epsOf s' := by
  unfold QMCLeafB.RoundT.epsOf QMCLeafB.RoundT.massV
  rw [h]

theorem poly_roundU : Automatic.Poly roundU := by
  have hsum : Automatic.Poly
      (fun s : QMCLeafB.RoundProgram.RSt =>
        QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s) := by
    have h1 : Automatic.Poly (fun s : QMCLeafB.RoundProgram.RSt =>
        (QMCLeafB.RoundProgram.stT s, QMCLeafB.RoundT.epsOf s)) :=
      Automatic.Poly.pair (f := QMCLeafB.RoundProgram.stT)
        (g := QMCLeafB.RoundT.epsOf) QMCLeafB.RoundProgram.poly_stT QMCLeafB.RoundT.poly_epsOf
    exact Automatic.Poly.comp (f := fun q : ℚ × ℚ => q.1 + q.2)
      (g := fun s : QMCLeafB.RoundProgram.RSt =>
        (QMCLeafB.RoundProgram.stT s, QMCLeafB.RoundT.epsOf s)) Automatic.Poly.rat_add h1
  have hc : Automatic.Poly (fun s : QMCLeafB.RoundProgram.RSt =>
      decide (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s)) :=
    Automatic.Poly.rat_le_comp (Automatic.Poly.const (0 : ℚ)) hsum
  unfold roundU
  exact Automatic.Poly.ite_prop
    (p := fun s : QMCLeafB.RoundProgram.RSt =>
      0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s) hc
    QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_round

theorem stOks_roundU (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stOks (roundU s) = QMCLeafB.RoundProgram.stOks s ++ [okU s] := by
  by_cases h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundU_of_top s h, okU, if_pos h, stOks_roundT]
  · rw [roundU_of_interior s h, okU, if_neg h]
    exact QMCLeafB.RStInit.stOks_round s

theorem stOks_iterateU (s : QMCLeafB.RoundProgram.RSt) (T : ℕ) :
    QMCLeafB.RoundProgram.stOks (roundU^[T] s)
      = QMCLeafB.RoundProgram.stOks s ++ (List.range T).map (fun k => okU (roundU^[k] s)) := by
  induction T with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundU, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

/-- **`hverdict` at the reported round.** -/
theorem verdict_iterate_eq_anyOk_U (s : QMCLeafB.RoundProgram.RSt)
    (hs : QMCLeafB.RoundProgram.stOks s = []) (T : ℕ) :
    QMCLeafB.RoundProgram.verdict (roundU^[T] s)
      = QMCLeafB.SimLoop.anyOk (fun k => okU (roundU^[k] s)) T := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_iterateU, hs, List.nil_append]
  exact QMCLeafB.RStInit.decide_pos_filter_map_range _ T

/-! ### 7a.  The top slice: `roundU` is `roundT` on the whole orbit -/

theorem roundU_iterate_eq_roundT (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : 0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) :
    ∀ k : ℕ, roundU^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.RoundT.roundT^[k]
          (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      refine roundU_of_top _ ?_
      have heps : QMCLeafB.RoundT.epsOf
          (QMCLeafB.RoundT.roundT^[j]
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))
          = QMCLeafB.RoundT.epsOf
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
        epsOf_congr (stA_iterateT _ j)
      rw [stT_iterateT, heps,
        QMCLeafB.RStInit.stT_init0]
      exact h

theorem loopBit_U_eq_roundT (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : 0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundU
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundU_iterate_eq_roundT G t h]

/-- **`htop` at the reported round**, for every order and every positive count. -/
theorem htop_roundU_all (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundU
        QMCLeafB.RoundProgram.verdict T0 G t = true := by
  intro G t hlo hhi
  have hlo' : -(QMCLeafB.EngineRuntime.Rq G / 40000) ≤ t := by exact_mod_cast hlo
  have h : 0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) := by
    rw [epsOf_init0]
    show 0 ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000
    linarith
  rw [loopBit_U_eq_roundT T0 G t h]
  exact htop_roundT_all T0 hpos G t hlo hhi

/-! ### 7b.  The interior: `roundU` is literally `round`, so the engine's stream is the `ok` stream -/

theorem roundU_iterate_eq_round (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : ¬ (0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))) :
    ∀ k : ℕ, roundU^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.RoundProgram.round^[k]
          (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      refine roundU_of_interior _ ?_
      have heps : QMCLeafB.RoundT.epsOf
          (QMCLeafB.RoundProgram.round^[j]
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))
          = QMCLeafB.RoundT.epsOf
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
        epsOf_congr (QMCLeafB.RStInit.stA_iterate _ j)
      rw [QMCLeafB.RStInit.stT_iterate, heps,
        QMCLeafB.RStInit.stT_init0]
      exact h

theorem loopBit_U_eq_round (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : ¬ (0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundU
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundU_iterate_eq_round G t h]

/-- **The interior `ok` stream is the engine's own**, so `hverdict` at the reported round is
`RStInit.loopBit_eq_anyOk_of_count` verbatim. -/
theorem loopBit_U_eq_anyOk_engine (G : QuantumMaxCutEnergy.Input) (t : ℚ) (T : ℕ)
    (h : ¬ (0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundU
        QMCLeafB.RoundProgram.verdict (fun _ _ => T) G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => !((QMCLeafB.RoundProgram.oracleR
            (QMCLeafB.RoundProgram.round^[k]
              (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))).1)) T := by
  rw [loopBit_U_eq_round (fun _ _ => T) G t h]
  exact QMCLeafB.RStInit.loopBit_eq_anyOk_of_count T G t

/-! ### 7c.  The same round behind m1's normalisation guard

The size ledger needs `GuardedRound.roundG`'s freeze (`LedgerGT`'s `roundOk` branch); the run from
`init0` is normalised, so the guard is inert there and `roundGU` is `roundU` on the whole orbit. -/

theorem roundT_normalised (s : QMCLeafB.RoundProgram.RSt)
    (h : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s) :
    (QMCLeafB.RoundProgram.stX (QMCLeafB.RoundT.roundT s)).length
      = QMCLeafB.RoundProgram.stN (QMCLeafB.RoundT.roundT s)
        * QMCLeafB.RoundProgram.stN (QMCLeafB.RoundT.roundT s) := by
  unfold QMCLeafB.RoundT.roundT
  split_ifs with hc
  · rw [QMCLeafB.GuardedRound.stN_roundOk, QMCLeafB.GuardedRound.stX_roundOk]
    exact h
  · have h1 := QMCLeafB.GuardedRound.roundG_normalised s h
    rwa [QMCLeafB.GuardedRound.roundG_of_normalised s h] at h1

theorem roundU_normalised (s : QMCLeafB.RoundProgram.RSt)
    (h : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s) :
    (QMCLeafB.RoundProgram.stX (roundU s)).length
      = QMCLeafB.RoundProgram.stN (roundU s) * QMCLeafB.RoundProgram.stN (roundU s) := by
  by_cases ht : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundU_of_top s ht]
    exact roundT_normalised s h
  · rw [roundU_of_interior s ht]
    have h1 := QMCLeafB.GuardedRound.roundG_normalised s h
    rwa [QMCLeafB.GuardedRound.roundG_of_normalised s h] at h1

/-- **The reported round behind the normalisation guard.** -/
noncomputable def roundGU (s : QMCLeafB.RoundProgram.RSt) : QMCLeafB.RoundProgram.RSt :=
  if (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s then roundU s
  else QMCLeafB.RoundProgram.roundOk s

/-- **The flag `roundGU` appends.** -/
noncomputable def okGU (s : QMCLeafB.RoundProgram.RSt) : Bool :=
  if (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s then okU s
  else true

theorem roundGU_of_normalised (s : QMCLeafB.RoundProgram.RSt)
    (h : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s) :
    roundGU s = roundU s := by
  unfold roundGU
  rw [if_pos h]

theorem roundGU_of_abnormal (s : QMCLeafB.RoundProgram.RSt)
    (h : ¬ ((QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s)) :
    roundGU s = QMCLeafB.RoundProgram.roundOk s := by
  unfold roundGU
  rw [if_neg h]

theorem poly_roundGU : Automatic.Poly roundGU := by
  have hlen : Automatic.Poly
      (fun s : QMCLeafB.RoundProgram.RSt => (QMCLeafB.RoundProgram.stX s).length) :=
    Automatic.Poly.comp (f := (List.length : List ℚ → ℕ))
      (g := QMCLeafB.RoundProgram.stX) (Automatic.Poly.list_length (α := ℚ))
      QMCLeafB.RoundProgram.poly_stX
  have hnn : Automatic.Poly (fun s : QMCLeafB.RoundProgram.RSt =>
      QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s) :=
    Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
      (g := fun s : QMCLeafB.RoundProgram.RSt =>
        (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stN s)) Automatic.Poly.nat_mul
      (Automatic.Poly.pair QMCLeafB.RoundProgram.poly_stN QMCLeafB.RoundProgram.poly_stN)
  have hp : Automatic.Poly (fun s : QMCLeafB.RoundProgram.RSt =>
      decide ((QMCLeafB.RoundProgram.stX s).length
        = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s)) :=
    Automatic.Poly.nat_eq_comp hlen hnn
  have h := Automatic.Poly.ite_prop
    (p := fun s : QMCLeafB.RoundProgram.RSt => (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s) hp
    poly_roundU QMCLeafB.RoundProgram.poly_roundOk
  exact QMCLeafB.FinishLine.poly_of_pointwise h (fun s => rfl)

theorem roundGU_iterate_normalised {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    → QMCLeafB.RoundProgram.RSt}
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (j : ℕ) :
    (QMCLeafB.RoundProgram.stX (roundGU^[j] (init p))).length
      = QMCLeafB.RoundProgram.stN (roundGU^[j] (init p))
        * QMCLeafB.RoundProgram.stN (roundGU^[j] (init p)) := by
  induction j with
  | zero => simpa using hnorm p
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      unfold roundGU
      split_ifs with h
      · exact roundU_normalised _ h
      · rw [QMCLeafB.GuardedRound.stN_roundOk, QMCLeafB.GuardedRound.stX_roundOk]
        exact ih

/-- **The guard is inert along the run of `roundGU` from a normalised start.** -/
theorem roundGU_iterate_eq_roundU {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    → QMCLeafB.RoundProgram.RSt}
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (j : ℕ) :
    roundGU^[j] (init p) = roundU^[j] (init p) := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      refine roundGU_of_normalised _ ?_
      have hk := roundGU_iterate_normalised hnorm p k
      rw [ih] at hk
      exact hk

theorem loopBit_GU_eq_roundU (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGU
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundU
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundGU_iterate_eq_roundU QMCLeafB.RStInit.init_normalised]

/-- **`htop` at the guarded reported round**, every order, every positive count. -/
theorem htop_roundGU_all (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGU
        QMCLeafB.RoundProgram.verdict T0 G t = true := by
  intro G t hlo hhi
  rw [loopBit_GU_eq_roundU]
  exact htop_roundU_all T0 hpos G t hlo hhi

theorem stOks_roundGU (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stOks (roundGU s) = QMCLeafB.RoundProgram.stOks s ++ [okGU s] := by
  by_cases h : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s
  · rw [roundGU_of_normalised s h, okGU, if_pos h, stOks_roundU]
  · rw [roundGU_of_abnormal s h, okGU, if_neg h]
    rfl

theorem stOks_iterate_GU (s : QMCLeafB.RoundProgram.RSt) (T : ℕ) :
    QMCLeafB.RoundProgram.stOks (roundGU^[T] s)
      = QMCLeafB.RoundProgram.stOks s
        ++ (List.range T).map (fun k => okGU (roundGU^[k] s)) := by
  induction T with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundGU, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

/-- **`hverdict` at the guarded reported round.** -/
theorem verdict_iterate_eq_anyOk_GU (s : QMCLeafB.RoundProgram.RSt)
    (hs : QMCLeafB.RoundProgram.stOks s = []) (T : ℕ) :
    QMCLeafB.RoundProgram.verdict (roundGU^[T] s)
      = QMCLeafB.SimLoop.anyOk (fun k => okGU (roundGU^[k] s)) T := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_iterate_GU, hs, List.nil_append]
  exact QMCLeafB.RStInit.decide_pos_filter_map_range _ T

/-- **On the interior the guarded reported round is the engine's own round**, so the `ok` stream is
the engine's: this is the form `Check_runparts_dilate_m5`'s `hmem`/`C` and `RunParts.hverdict` want. -/
theorem loopBit_GU_eq_anyOk_engine (G : QuantumMaxCutEnergy.Input) (t : ℚ) (T : ℕ)
    (h : ¬ (0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGU
        QMCLeafB.RoundProgram.verdict (fun _ _ => T) G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => !((QMCLeafB.RoundProgram.oracleR
            (QMCLeafB.RoundProgram.round^[k]
              (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))).1)) T := by
  rw [loopBit_GU_eq_roundU]
  exact loopBit_U_eq_anyOk_engine G t T h

/-! ## 8.  The one-step size ledger at `roundGU` is the *branch-wise* ledger

`roundGU` unfolds to `roundOk` or to `round` on every state — `roundU`'s two branches are `roundT`
(itself `roundOk` or `round`) and `round`.  So brick 2's `LedgerGT` (`m8`'s branch-wise form: one
inequality for `roundOk` and one for `round`) implies the ledger at `roundGU` with no extra work, and
the cap slot is untouched.  Both one-step inequalities are below in that shape. -/

theorem ledgerGU_M_of_branches {M : QMCLeafB.RoundProgram.RSt → ℕ} {c : ℕ}
    (hOi : ∀ s, M (QMCLeafB.RoundProgram.roundOk s) ≤ M s + c)
    (hCi : ∀ s, (QMCLeafB.RoundProgram.stX s).length
        = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s →
      M (QMCLeafB.RoundProgram.round s) ≤ M s + c) :
    ∀ s, M (roundGU s) ≤ M s + c := by
  intro s
  unfold roundGU
  split_ifs with hg
  · unfold roundU
    split_ifs with ht
    · unfold QMCLeafB.RoundT.roundT
      split_ifs with hc
      · exact hOi s
      · exact hCi s hg
    · exact hCi s hg
  · exact hOi s

theorem ledgerGU_len_of_branches {M : QMCLeafB.RoundProgram.RSt → ℕ} {c : ℕ}
    (hOs : ∀ s, (enc (QMCLeafB.RoundProgram.roundOk s)).length
      ≤ max ((enc s).length + c) (M s))
    (hCs : ∀ s, (QMCLeafB.RoundProgram.stX s).length
        = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s →
      (enc (QMCLeafB.RoundProgram.round s)).length
        ≤ max ((enc s).length + c) (M s)) :
    ∀ s, (enc (roundGU s)).length ≤ max ((enc s).length + c) (M s) := by
  intro s
  unfold roundGU
  split_ifs with hg
  · unfold roundU
    split_ifs with ht
    · unfold QMCLeafB.RoundT.roundT
      split_ifs with hc
      · exact hOs s
      · exact hCs s hg
    · exact hCs s hg
  · exact hOs s

/-! ## 9.  `htop` from an abstract initial state — so brick 1's rebuilt `init0` plugs in

`Check_roundT_m7.htop_roundT` is stated at `RStInit.init0`, and brick 1 rebuilds that state at
`MOf n = 2n² + 2·(dqShallow G)²` (which is what `RunParts.hwit`'s `Aat … (initShapeOf _ (2n²+2dq²))`
forces).  Nothing in the `htop` route depends on the rest of `init0`: only four facts are used —
`Poly`, normalisation, `fvR = 0`, `stT = t` and the state's own mass.  They are isolated here so the
rebuilt state transfers without touching this file. -/

/-- **One `ok` round at a state whose value is `0` and whose slack is non-negative.** -/
theorem htop_roundT_of_state (s : QMCLeafB.RoundProgram.RSt) {j : ℕ} (hj : 1 ≤ j)
    (hfv : QMCLeafB.RoundProgram.fvR s = 0)
    (hslack : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s) :
    QMCLeafB.RoundProgram.verdict (QMCLeafB.RoundT.roundT^[j] s) = true := by
  have hbranch : QMCLeafB.RoundProgram.fvR s
      ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s := by
    rw [hfv]
    exact hslack
  have hok : QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT s)
      = QMCLeafB.RoundProgram.stOks s ++ [true] := by
    rw [QMCLeafB.RoundT.roundT, if_pos hbranch]
    rfl
  have hmem : true ∈ QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[1] s) := by
    rw [Function.iterate_one, hok]
    exact List.mem_append_right _ (List.mem_singleton_self true)
  have hpref : QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[1] s)
      <+: QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[j] s) := by
    refine stOks_prefix_iterateT s ?_
    exact hj
  exact QMCLeafB.Htop.verdict_of_mem (hpref.mem hmem)

/-- `roundU` is `roundT` on the whole orbit of any state above the campaign slack. -/
theorem roundU_iterate_eq_roundT_of_state (s : QMCLeafB.RoundProgram.RSt)
    (h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s) :
    ∀ k : ℕ, roundU^[k] s = QMCLeafB.RoundT.roundT^[k] s := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      refine roundU_of_top _ ?_
      have heps : QMCLeafB.RoundT.epsOf (QMCLeafB.RoundT.roundT^[j] s)
          = QMCLeafB.RoundT.epsOf s := epsOf_congr (stA_iterateT s j)
      rw [stT_iterateT, heps]
      exact h

/-- **`htop` for `roundGU` from an abstract initial state.**  The five hypotheses are exactly the
`init0` facts the route uses; `RStInit.init0` and brick 1's rebuilt state both satisfy them. -/
theorem htop_roundGU_of_init (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)
      → QMCLeafB.RoundProgram.RSt)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t)
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ p, QMCLeafB.RoundProgram.fvR (init p) = 0)
    (hstT : ∀ p, QMCLeafB.RoundProgram.stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundGU
        QMCLeafB.RoundProgram.verdict T0 G t = true := by
  intro G t hlo _
  have hlo' : -(QMCLeafB.EngineRuntime.Rq G / 40000) ≤ t := by exact_mod_cast hlo
  set p := QMCLeafB.FinalStroke.noTape G t with hp
  have hpG : p.1.1 = G := rfl
  have hpt : p.2 = t := rfl
  have hslack : 0 ≤ QMCLeafB.RoundProgram.stT (init p)
      + QMCLeafB.RoundT.epsOf (init p) := by
    rw [hstT p, hmass p, hpG, hpt]
    linarith
  have h1 : QMCLeafB.FinalStroke.loopBit init roundGU QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict T0 G t := by
    unfold QMCLeafB.FinalStroke.loopBit
    rw [roundGU_iterate_eq_roundU hnorm p, roundU_iterate_eq_roundT_of_state _ hslack]
  rw [h1]
  unfold QMCLeafB.FinalStroke.loopBit
  exact htop_roundT_of_state _ (hpos G t) (hfv p) hslack

/-! ## 10.  The `ok` stream of `roundGU` is the engine's, pointwise, on the interior

`RunParts`' per-round hypotheses (`hcert` via m5's `hcert_of_relaxMem`, `hwit`, `hcut`) are all
guarded by `ok k = true` / `ok k = false`, so brick 4 needs the *pointwise* identification of the
program's flag with the engine's answer, not just the `anyOk` equation.  On the interior that is
exactly what happens: the regime is a run invariant, so every round of the orbit is
`RoundProgram.round`'s round and the flag is `!((oracleR ·).1)`. -/

theorem not_top_iterateU (s : QMCLeafB.RoundProgram.RSt) (k : ℕ)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s)) :
    ¬ (0 ≤ QMCLeafB.RoundProgram.stT (roundU^[k] s)
        + QMCLeafB.RoundT.epsOf (roundU^[k] s)) := by
  have hst : QMCLeafB.RoundProgram.stT (roundU^[k] s) = QMCLeafB.RoundProgram.stT s :=
    stT_iterateU s k
  have heps : QMCLeafB.RoundT.epsOf (roundU^[k] s) = QMCLeafB.RoundT.epsOf s :=
    epsOf_congr (stA_iterateU s k)
  rw [hst, heps]
  exact h

/-- **The flag of `roundU` is the engine's answer below the campaign slack.** -/
theorem okU_eq_engine (s : QMCLeafB.RoundProgram.RSt) (k : ℕ)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s)) :
    okU (roundU^[k] s) = !((QMCLeafB.RoundProgram.oracleR (roundU^[k] s)).1) := by
  unfold okU
  rw [if_neg (not_top_iterateU s k h)]

/-- **The flag of `roundGU` is the engine's answer below the campaign slack**, along the whole orbit
of a normalised start. -/
theorem okGU_eq_engine {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)
      → QMCLeafB.RoundProgram.RSt}
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (k : ℕ)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT (init p) + QMCLeafB.RoundT.epsOf (init p))) :
    okGU (roundGU^[k] (init p))
      = !((QMCLeafB.RoundProgram.oracleR (roundU^[k] (init p))).1) := by
  have hnorm' := roundGU_iterate_normalised hnorm p k
  have heq : roundGU^[k] (init p) = roundU^[k] (init p) :=
    roundGU_iterate_eq_roundU hnorm p k
  have hreg : ¬ (0 ≤ QMCLeafB.RoundProgram.stT (init p) + QMCLeafB.RoundT.epsOf (init p)) := h
  unfold okGU
  rw [if_pos hnorm', heq, okU_eq_engine (init p) k hreg]

/-- **`hverdict` at `roundGU` for an abstract initial state with an empty flag list.** -/
theorem hverdict_roundGU_of_init (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hoks : ∀ p, QMCLeafB.RoundProgram.stOks (init p) = []) (T : ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init roundGU QMCLeafB.RoundProgram.verdict
        (fun _ _ => T) G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => okGU (roundGU^[k] (init (QMCLeafB.FinalStroke.noTape G t)))) T :=
  verdict_iterate_eq_anyOk_GU _ (hoks _) T

theorem roundU_iterate_eq_round_of_interior (s : QMCLeafB.RoundProgram.RSt) (k : ℕ)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s)) :
    roundU^[k] s = QMCLeafB.RoundProgram.round^[k] s := by
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      refine roundU_of_interior _ ?_
      have hst : QMCLeafB.RoundProgram.stT (QMCLeafB.RoundProgram.round^[j] s)
          = QMCLeafB.RoundProgram.stT s := QMCLeafB.RStInit.stT_iterate s j
      have heps : QMCLeafB.RoundT.epsOf (QMCLeafB.RoundProgram.round^[j] s)
          = QMCLeafB.RoundT.epsOf s :=
        epsOf_congr (QMCLeafB.RStInit.stA_iterate s j)
      rw [hst, heps]
      exact h

/-- **The flag of `roundGU`, read against the shelf round's orbit.** -/
theorem okGU_eq_engine_round {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)
      → QMCLeafB.RoundProgram.RSt}
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (k : ℕ)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT (init p) + QMCLeafB.RoundT.epsOf (init p))) :
    okGU (roundGU^[k] (init p))
      = !((QMCLeafB.RoundProgram.oracleR
          (QMCLeafB.RoundProgram.round^[k] (init p))).1) := by
  rw [okGU_eq_engine hnorm p k h, roundU_iterate_eq_round_of_interior _ k h]

/-- **The loop bit of `roundGU` is the shelf loop's bit on the interior**, for an abstract initial
state — the transfer brick 4's `RunParts` bundle needs. -/
theorem loopBit_GU_eq_round_of_init
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : ¬ (0 ≤ QMCLeafB.RoundProgram.stT
        (init (QMCLeafB.FinalStroke.noTape G t))
      + QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t)))) :
    QMCLeafB.FinalStroke.loopBit init roundGU QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundGU_iterate_eq_roundU hnorm, roundU_iterate_eq_round_of_interior _ _ h]

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.HtopFinish.sum_map_flatMap
#print axioms QMCLeafB.HtopFinish.map_comp_eq
#print axioms QMCLeafB.HtopFinish.sum_map_mk
#print axioms QMCLeafB.HtopFinish.stA_init0_eq_mk
#print axioms QMCLeafB.HtopFinish.wVal_eq_wMatQ
#print axioms QMCLeafB.HtopFinish.massV_init0
#print axioms QMCLeafB.HtopFinish.epsOf_init0
#print axioms QMCLeafB.HtopFinish.stOks_roundT
#print axioms QMCLeafB.HtopFinish.stOks_iterateT
#print axioms QMCLeafB.HtopFinish.verdict_iterate_eq_anyOk_T
#print axioms QMCLeafB.HtopFinish.loopBit_eq_anyOk_T
#print axioms QMCLeafB.HtopFinish.htop_roundT_all
#print axioms QMCLeafB.HtopFinish.htop_roundT
#print axioms QMCLeafB.HtopFinish.anyOk_okOfT_eq_true
#print axioms QMCLeafB.HtopFinish.htop_roundT_Kpow
#print axioms QMCLeafB.HtopFinish.htop_roundT_KbcF
#print axioms QMCLeafB.HtopFinish.htop_roundT_shallow
#print axioms QMCLeafB.HtopFinish.soundEpsOnBracket_roundT
#print axioms QMCLeafB.HtopFinish.entV_eq_entry
#print axioms QMCLeafB.HtopFinish.sum_map_const
#print axioms QMCLeafB.HtopFinish.list_map_congr
#print axioms QMCLeafB.HtopFinish.dvR_init0_ne_zero
#print axioms QMCLeafB.HtopFinish.dvR_init0_noTape_ne_zero
#print axioms QMCLeafB.HtopFinish.anyOk_congr
#print axioms QMCLeafB.HtopFinish.hverdict_of_flags
#print axioms QMCLeafB.HtopFinish.okOfT_zero_of_interior
#print axioms QMCLeafB.HtopFinish.stT_roundT
#print axioms QMCLeafB.HtopFinish.stA_roundT
#print axioms QMCLeafB.HtopFinish.roundU_of_top
#print axioms QMCLeafB.HtopFinish.roundU_of_interior
#print axioms QMCLeafB.HtopFinish.stT_roundU
#print axioms QMCLeafB.HtopFinish.stA_roundU
#print axioms QMCLeafB.HtopFinish.stT_iterateU
#print axioms QMCLeafB.HtopFinish.stA_iterateU
#print axioms QMCLeafB.HtopFinish.stA_iterateT
#print axioms QMCLeafB.HtopFinish.stT_iterateT
#print axioms QMCLeafB.HtopFinish.epsOf_congr
#print axioms QMCLeafB.HtopFinish.poly_roundU
#print axioms QMCLeafB.HtopFinish.stOks_roundU
#print axioms QMCLeafB.HtopFinish.stOks_iterateU
#print axioms QMCLeafB.HtopFinish.verdict_iterate_eq_anyOk_U
#print axioms QMCLeafB.HtopFinish.roundU_iterate_eq_roundT
#print axioms QMCLeafB.HtopFinish.loopBit_U_eq_roundT
#print axioms QMCLeafB.HtopFinish.htop_roundU_all
#print axioms QMCLeafB.HtopFinish.roundU_iterate_eq_round
#print axioms QMCLeafB.HtopFinish.loopBit_U_eq_round
#print axioms QMCLeafB.HtopFinish.loopBit_U_eq_anyOk_engine
#print axioms QMCLeafB.HtopFinish.roundT_normalised
#print axioms QMCLeafB.HtopFinish.roundU_normalised
#print axioms QMCLeafB.HtopFinish.roundGU_of_normalised
#print axioms QMCLeafB.HtopFinish.roundGU_of_abnormal
#print axioms QMCLeafB.HtopFinish.poly_roundGU
#print axioms QMCLeafB.HtopFinish.roundGU_iterate_normalised
#print axioms QMCLeafB.HtopFinish.roundGU_iterate_eq_roundU
#print axioms QMCLeafB.HtopFinish.loopBit_GU_eq_roundU
#print axioms QMCLeafB.HtopFinish.htop_roundGU_all
#print axioms QMCLeafB.HtopFinish.stOks_roundGU
#print axioms QMCLeafB.HtopFinish.stOks_iterate_GU
#print axioms QMCLeafB.HtopFinish.verdict_iterate_eq_anyOk_GU
#print axioms QMCLeafB.HtopFinish.loopBit_GU_eq_anyOk_engine
#print axioms QMCLeafB.HtopFinish.ledgerGU_M_of_branches
#print axioms QMCLeafB.HtopFinish.ledgerGU_len_of_branches
#print axioms QMCLeafB.HtopFinish.stOks_prefix_iterateT
#print axioms QMCLeafB.HtopFinish.htop_roundT_of_state
#print axioms QMCLeafB.HtopFinish.roundU_iterate_eq_roundT_of_state
#print axioms QMCLeafB.HtopFinish.htop_roundGU_of_init
#print axioms QMCLeafB.HtopFinish.not_top_iterateU
#print axioms QMCLeafB.HtopFinish.okU_eq_engine
#print axioms QMCLeafB.HtopFinish.okGU_eq_engine
#print axioms QMCLeafB.HtopFinish.hverdict_roundGU_of_init
#print axioms QMCLeafB.HtopFinish.roundU_iterate_eq_round_of_interior
#print axioms QMCLeafB.HtopFinish.okGU_eq_engine_round
#print axioms QMCLeafB.HtopFinish.loopBit_GU_eq_round_of_init

end QMCLeafB.HtopFinish


