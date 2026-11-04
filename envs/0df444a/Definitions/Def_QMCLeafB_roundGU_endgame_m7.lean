-- Prove2me | Definitions.Def_QMCLeafB_roundGU_endgame_m7
-- name    : QMCLeafB_roundGU_endgame_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:13:12.684658+00:00
-- url     : https://prove2.me/theorems/b2c48109-bc17-4a6e-bacc-a727486765cd
-- title:
--   QMCLeafB roundGU_endgame_m7
-- statement:
--   # leaf B phase 16 — the endgame at `roundGU` (swarm `smw1ez4a9`, member m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_finish_m7
import Definitions.Def_QMCLeafB_ledgerG_m3
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 16 — the endgame at `roundGU` (swarm `smw1ez4a9`, member m7)

This file assembles `QMCLeafB.FinishLine.SolutionStatement` over the round the closing chain actually
runs, `HtopFinish.roundGU = guard ∘ (slack-above / engine-below)`, with the size slot, the count side
condition, the fuel arithmetic and `htop` all discharged.  Three compiled deliverables are combined:

* `Check_ledgerG_m3` (m3, brick 2): the `|X|`-based cap `MszG`, its polynomial bound
  `MszG s ≤ 11448595·(|enc s|+1)^6`, the `roundOk` step (`MszG (roundOk s) = MszG s + 6`), the `cut`
  step at a normalised state, and the `roundG` ledger;
* `Check_union_shallow_m5` (m5, brick 5): `solution_union_shallow_final`, the union at the
  `dqShallow` family with `Kbc2`, i.e. with no numeric hypothesis left;
* `Check_htop_finish_m7` (this member, brick 3): `roundGU`, its `Poly` proof, `htop` at every order,
  and the branch-wise ledger glue `ledgerGU_M_of_branches` / `ledgerGU_len_of_branches`.

Why `roundGU` rather than `roundG`: at `roundG` (= the shelf round) the top slice has no `ok` round at
all in the first step — `init0` packs `initShapeOf n (MOf n) = (MOf n)⁻¹ • 1` with `MOf n ≥ 4`, so
`dvR ≠ 0` and the engine's oracle answers *cut* (`HtopFinish.dvR_init0_ne_zero`) — and `htop` is not
known at `RoundProgram.round` for any order; `roundT` fixes `htop` but its `ok` rounds carry no
`RelaxMem` certificate, which is what `hd` needs.  `roundGU` splits the two regimes by the sign of
`t + εw`, a run invariant, so `htop` holds on the top slice and on the interior the run is *literally*
the shelf round's run (engine stream, `hmem`/`C` dichotomy untouched).

Residual after this file: brick 1's rebuilt `init0` (packing `initShapeOf` at
`MOf n = 2n² + 2·(dqShallow G)²`, `Poly`, tape-free, normalised — all of which `RStInit.init0`
already satisfies except the `MOf` value, which only enters through `Boundary.initShapeOf`) and brick
4's `RunParts` bundle on the interior at the shelf round.  Both are single hypotheses below.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundGUEndgame

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.CapGuard
open QMCLeafB.HtopFinish

local instance instRequestCodingRoundGU : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The two branch inequalities of `MszG` in the form the ledger glue wants -/

/-- The `ok` branch: `roundOk` freezes everything but the flag. -/
theorem MszG_roundOk_le (s : RSt) : MszG (roundOk s) ≤ MszG s + 6 :=
  le_of_eq (MszG_roundOk s)

theorem enc_roundOk_le (s : RSt) :
    (enc (roundOk s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  rw [enc_roundOk]
  exact le_max_left _ _

/-- The shelf round's step at a **normalised** state (which is where it runs on the orbit). -/
theorem MszG_round_le_of_normalised (s : RSt) (hn : (stX s).length = stN s * stN s) :
    MszG (round s) ≤ MszG s + 6 := by
  by_cases h : (oracleR s).1 = true
  · exact MszG_round_cut_le_G s hn h
  · have hf : (oracleR s).1 = false := by simpa using h
    rw [round_of_not_cut s hf]
    exact MszG_roundOk_le s

theorem enc_round_le_of_normalised (s : RSt) (hn : (stX s).length = stN s * stN s) :
    (enc (round s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  by_cases h : (oracleR s).1 = true
  · exact le_trans (enc_round_cut_le_G s hn h) (le_max_right _ _)
  · have hf : (oracleR s).1 = false := by simpa using h
    rw [round_of_not_cut s hf]
    exact enc_roundOk_le s

/-! ## 2.  The one-step size ledger at `roundGU`, and the cap -/

theorem MszG_roundGU_le (s : RSt) : MszG (roundGU s) ≤ MszG s + 6 :=
  ledgerGU_M_of_branches MszG_roundOk_le MszG_round_le_of_normalised s

theorem enc_roundGU_le (s : RSt) :
    (enc (roundGU s)).length ≤ max ((enc s).length + 6) (MszG s) :=
  ledgerGU_len_of_branches enc_roundOk_le enc_round_le_of_normalised s

theorem MszG_cap (s : RSt) : MszG s ≤ 11448595 * ((enc s).length + 1) ^ 6 :=
  MszG_le_pow s

/-! ## 3.  The interior is literally the shelf round -/

/-- Below the campaign slack (`t + εw < 0`) the reported round is the shelf round. -/
theorem not_top_of_interior (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ¬ (0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) := by
  have hr : (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < 0 := by linarith
  have hq : t + QMCLeafB.EngineRuntime.Rq G / 40000 < 0 := by exact_mod_cast hr
  rw [epsOf_init0 (QMCLeafB.FinalStroke.noTape G t), QMCLeafB.FinalStroke.noTape_fst]
  intro hle
  linarith

/-- **On the interior the reported loop's bit is the shelf loop's bit.** -/
theorem loopBit_GU_eq_round (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : ¬ (0 ≤ t + QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGU
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict T0 G t := by
  rw [loopBit_GU_eq_roundU, loopBit_U_eq_round T0 G t h]

/-- **`RunParts` only sees the loop bit through `hverdict`**, so an equality of loop bits carries a
run bundle across. -/
def runParts_congr {o₁ o₂ : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o₁ G t P) (h : o₂ G t = o₁ G t) :
    QMCLeafB.FinalStroke.RunParts o₂ G t P :=
  { B with hverdict := by rw [h]; exact B.hverdict }

/-! ## 4.  The endgame

The count family is m5's `Kbc2` at `mHalve (n·n)`: `paramsKbc2`.  `htop` is
`htop_roundGU_all` at `one_le_Kbc2_mul`; the size slot is §2; `init` is m1's `RStInit.init0`. -/

/-- **`SolutionStatement` from one `RunParts` bundle per interior `(G,t)`, at the reported round.** -/
theorem solution_roundGU (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGU
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk
    QMCLeafB.RStInit.init0 roundGU QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 poly_roundGU QMCLeafB.RoundProgram.poly_verdict
    MszG 11448595 6 6 (by norm_num)
    MszG_roundGU_le enc_roundGU_le MszG_cap
    QMCLeafB.RStInit.init0_tape
    (fun G t _ hlo hhi => htop_roundGU_all
      (fun G' _ => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))
      (fun G' _ => QMCLeafB.UnionShallow.one_le_Kbc2_mul G') G t hlo hhi)
    hd

/-- **The same endgame from the run bundle at the SHELF round** — the form brick 4 produces
(`RunPartsShallow.runParts_shallow_dyadic` at `runParamsShallow`, transferred to `paramsKbc2` by the
count monotonicity).  The only conversion needed is the loop-bit equality on the interior. -/
theorem solution_roundGU_of_hd_round (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_roundGU k hk (fun G t hn hlo hlt =>
    runParts_congr (hd G t hn hlo hlt)
      (loopBit_GU_eq_round _ G t (not_top_of_interior G t hlt)))

/-- **The same endgame at an arbitrary monomial round factor** `Kf` — the generic form, so a brick 4
that lands a different count (e.g. `RundataArith.runK`) is a drop-in: `htop` is discharged for any
`Kf` positive in `G` (this is where `roundGU` pays: at `RoundProgram.round` no such statement is
known), and the size slot is §2. -/
theorem solution_roundGU_gen (Kf : QuantumMaxCutEnergy.Input → ℕ) (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (hKpos : ∀ G : QuantumMaxCutEnergy.Input,
      1 ≤ Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGU
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_gen Kf k hKf hseed hK
    QMCLeafB.RStInit.init0 roundGU QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 poly_roundGU QMCLeafB.RoundProgram.poly_verdict
    MszG 11448595 6 6 (by norm_num)
    MszG_roundGU_le enc_roundGU_le MszG_cap
    QMCLeafB.RStInit.init0_tape
    (fun G t _ hlo hhi => htop_roundGU_all
      (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))
      (fun G' _ => hKpos G') G t hlo hhi)
    hd

/-- **The generic endgame from the run bundle at the SHELF round** (brick 4's own form). -/
theorem solution_roundGU_gen_of_hd_round (Kf : QuantumMaxCutEnergy.Input → ℕ) (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (hKpos : ∀ G : QuantumMaxCutEnergy.Input,
      1 ≤ Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_roundGU_gen Kf k hKf hseed hK hKpos (fun G t hn hlo hlt =>
    runParts_congr (hd G t hn hlo hlt)
      (loopBit_GU_eq_round _ G t (not_top_of_interior G t hlt)))


/-! ## 4b.  The endgame from an abstract initial state (brick 1's rebuilt `init0`) -/

/-- **`SolutionStatement` from an initial state, its five `init0`-shaped facts, and one `RunParts`
bundle per interior `(G,t)`.**  Every other slot — the init program's `Poly`, its tape-freeness, the
whole size ledger, the count side condition, the fuel arithmetic and `htop` — is discharged.  This is
the form brick 1's rebuilt `init0` (at `MOf n = 2n² + 2·(dqShallow G)²`, which is what
`RunParts.hwit`'s `Aat … (initShapeOf _ (2n²+2dq²))` forces) plugs into. -/
theorem solution_roundGU_of_init
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hinit : Automatic.Poly init)
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ p, QMCLeafB.RoundProgram.fvR (init p) = 0)
    (hstT : ∀ p, QMCLeafB.RoundProgram.stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init roundGU
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk
    init roundGU QMCLeafB.RoundProgram.verdict
    hinit poly_roundGU QMCLeafB.RoundProgram.poly_verdict
    MszG 11448595 6 6 (by norm_num)
    MszG_roundGU_le enc_roundGU_le MszG_cap
    hinitTape
    (fun G t _ hlo hhi => htop_roundGU_of_init init
      (fun G' _ => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))
      (fun G' _ => QMCLeafB.UnionShallow.one_le_Kbc2_mul G')
      hnorm hfv hstT hmass G t hlo hhi)
    hd


/-- Below the campaign slack on an abstract initial state the regime is the interior one. -/
theorem not_top_of_init (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hstT : ∀ p, QMCLeafB.RoundProgram.stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ¬ (0 ≤ QMCLeafB.RoundProgram.stT (init (QMCLeafB.FinalStroke.noTape G t))
      + QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))) := by
  have hr : (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < 0 := by linarith
  have hq : t + QMCLeafB.EngineRuntime.Rq G / 40000 < 0 := by exact_mod_cast hr
  have hstT' := hstT (QMCLeafB.FinalStroke.noTape G t)
  have hmass' := hmass (QMCLeafB.FinalStroke.noTape G t)
  have hpG : (QMCLeafB.FinalStroke.noTape G t).1.1 = G := rfl
  have hpt : (QMCLeafB.FinalStroke.noTape G t).2 = t := rfl
  rw [hstT', hmass', hpG, hpt]
  intro hle
  linarith

/-- **The same at an abstract initial state, from the run bundle at the SHELF round** — the form brick
4 produces, and the one that carries brick 1's rebuilt `init`. -/
theorem solution_roundGU_of_init_hd_round
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hinit : Automatic.Poly init)
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ p, QMCLeafB.RoundProgram.fvR (init p) = 0)
    (hstT : ∀ p, QMCLeafB.RoundProgram.stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_roundGU_of_init init k hk hinit hnorm hfv hstT hmass hinitTape
    (fun G t hn hlo hlt =>
      runParts_congr (hd G t hn hlo hlt)
        (loopBit_GU_eq_round_of_init init hnorm _ G t (not_top_of_init init hstT hmass G t hlt)))

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.RoundGUEndgame.MszG_roundOk_le
#print axioms QMCLeafB.RoundGUEndgame.enc_roundOk_le
#print axioms QMCLeafB.RoundGUEndgame.MszG_round_le_of_normalised
#print axioms QMCLeafB.RoundGUEndgame.enc_round_le_of_normalised
#print axioms QMCLeafB.RoundGUEndgame.MszG_roundGU_le
#print axioms QMCLeafB.RoundGUEndgame.enc_roundGU_le
#print axioms QMCLeafB.RoundGUEndgame.MszG_cap
#print axioms QMCLeafB.RoundGUEndgame.not_top_of_interior
#print axioms QMCLeafB.RoundGUEndgame.loopBit_GU_eq_round
#print axioms QMCLeafB.RoundGUEndgame.runParts_congr
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU_of_hd_round
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU_gen
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU_gen_of_hd_round
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU_of_init
#print axioms QMCLeafB.RoundGUEndgame.not_top_of_init
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round


