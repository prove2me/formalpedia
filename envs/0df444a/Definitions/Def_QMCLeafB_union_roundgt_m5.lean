-- Prove2me | Definitions.Def_QMCLeafB_union_roundgt_m5
-- name    : QMCLeafB_union_roundgt_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:21:59.649308+00:00
-- url     : https://prove2.me/theorems/7cda58c3-d03f-4f60-aab2-714c810d3ebe
-- title:
--   QMCLeafB union_roundgt_m5
-- statement:
--   # leaf B phase 16 — brick 5 `union-at-roundGT` (swarm `smw1ez4a9`, member m5, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_conformance_m8
import Definitions.Def_QMCLeafB_htop_finish_m7
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 16 — brick 5 `union-at-roundGT` (swarm `smw1ez4a9`, member m5, direction d8)

`Check_union_shallow_m5` closes the *numeric* half of the final mile
(`SolutionStatement` from {init program, size ledger, `htop`, `hd`}, all counts and tolerances
discharged).  This file closes the parts of the remaining three slots that do **not** depend on
brick 4:

* the size ledger, from m3/m8's `CapGuard.LedgerG MszG 6` through m8's branch-wise `LedgerGT` at the
  guarded slack round `roundGT` (so the old, false `hM`-free slot is gone);
* `htop`, but **at an arbitrary init program** — m7's `RoundT.htop_roundT` is stated at
  `RStInit.init0`, and the chain now runs m1's `InitDq.init0` (packed at `2n² + 2·dqShallow²`), so the
  top-slice proof has to be re-run at the new init.  `htop_roundT_of_init` below does exactly that
  from the only three facts it uses — `fvR (init …) = 0`, `stT (init …) = t`,
  `epsOf (init …) = Rq G / 40000` — and `htop_roundGT_of_init` transports it across the guard.

Residual after this file: the init program with those three scalar facts (all in
`Check_initdq_m1`), and brick 4's `RunParts` at `UnionShallow.paramsKbc2`.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.UnionAtGT

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingUnionGT : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The `4·Kbc` run count is positive (the `htop` instances' positivity slot). -/
theorem one_le_Kbc4_mul (G : QuantumMaxCutEnergy.Input) :
    1 ≤ QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
      * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  have hm : 1 ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) :=
    QMCLeafB.HalvePerG.one_le_mHalve (G.n * G.n)
  have hbc : 1 ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10 := by omega
  have hpow : 1 ≤ (G.n + 1) ^ 2 := Nat.one_le_pow 2 (G.n + 1) (by omega)
  have hKbc : 1 ≤ QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := by
    rw [QMCLeafB.FuelWire.Kbc_eq]
    calc (1 : ℕ) = 1 * (1 * 1) := by ring
      _ ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n)
            * ((G.n + 1) ^ 2
                * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10)) :=
          Nat.mul_le_mul hm (Nat.mul_le_mul hpow hbc)
  have h4 : 1 ≤ QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := by
    unfold QMCLeafB.LoopClose.Kbc4
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ 4 * QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G :=
          Nat.mul_le_mul (by norm_num) hKbc
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
          * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := Nat.mul_le_mul h4 hm

/-- From `20 ≤ 2^k` to `21 ≤ 2^k`. -/
theorem pow21_le {k : ℕ} (hk : 20 ≤ 2 ^ k) : 21 ≤ 2 ^ k := by
  have h5 : 5 ≤ k := by
    by_contra h
    have hk4 : k ≤ 4 := by omega
    have hle : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    norm_num at hle
    omega
  calc (21 : ℕ) ≤ 32 := by norm_num
    _ = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h5

/-- **`htop` at `roundT` for an arbitrary init program**, from the three scalar facts the top-slice
argument actually uses.  Same proof as `RoundT.htop_roundT`, with `RStInit.init0`'s lemmas replaced
by hypotheses — this is what `InitDq.init0` (the init packed at the campaign tolerance) satisfies. -/
theorem htop_roundT_of_init
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hstT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0 G t = true := by
  intro G t hlo _
  have hlo' : -(QMCLeafB.EngineRuntime.Rq G / 40000) ≤ t := by exact_mod_cast hlo
  set s := init (QMCLeafB.FinalStroke.noTape G t) with hs
  have hslack : (0 : ℚ) ≤ t + QMCLeafB.RoundT.epsOf s := by
    rw [heps G t]
    linarith
  have hbranch : QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s := by
    rw [hfv G t, hstT G t]
    exact hslack
  have hok : QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT s)
      = QMCLeafB.RoundProgram.stOks s ++ [true] := by
    rw [QMCLeafB.RoundT.roundT, if_pos hbranch]
    rfl
  have hmem : true ∈ QMCLeafB.RoundProgram.stOks ((QMCLeafB.RoundT.roundT^[1]) s) := by
    rw [Function.iterate_one, hok]
    exact List.mem_append_right _ (List.mem_singleton_self true)
  have hle : (1 : ℕ) ≤ T0 G t := hpos G t
  have hpre := QMCLeafB.RoundT.stOks_prefix_iterateT s hle
  exact QMCLeafB.Htop.verdict_of_mem (hpre.mem hmem)

/-- **`htop` at the guarded slack round `roundGT` for an arbitrary normalised init.**  The guard is
inert on the orbit of a normalised init (m8's `roundGT_iterate_eq_roundT`), so this is the previous
lemma transported across `roundGT`. -/
theorem htop_roundGT_of_init
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hnorm : ∀ p : QMCLeafB.FuelWire.Pkg,
      (QMCLeafB.RoundProgram.stX (init p)).length
        = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hstT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init QMCLeafB.ConformanceM8.roundGT
        QMCLeafB.RoundProgram.verdict T0 G t = true := by
  intro G t hlo hhi
  have htop := htop_roundT_of_init init hfv hstT heps T0 hpos G t hlo hhi
  unfold QMCLeafB.FinalStroke.loopBit at htop ⊢
  rw [QMCLeafB.ConformanceM8.roundGT_iterate_eq_roundT hnorm (QMCLeafB.FinalStroke.noTape G t)
    (T0 G t)]
  exact htop

/-- **The final glue at the guarded slack round, at a caller-chosen round factor.**

Residual: the init program (`Poly`, tape-free, normalised, with `fvR = 0`, `stT = p.2`,
`epsOf = Rq/40000` — all of them in `Check_initdq_m1` for `InitDq.init0`), the round factor's two
fuel facts and its domination of `budgetRounds`, and brick 4's `RunParts` at `paramsShallowKf Kf hK`.
The size ledger (m3 through m8's `LedgerGT`) and `htop` are discharged here. -/
theorem endgame_final_at_roundGT_gen
    (Kf : QuantumMaxCutEnergy.Input → ℕ) (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hinit : Automatic.Poly init)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hnorm : ∀ p : QMCLeafB.FuelWire.Pkg,
      (QMCLeafB.RoundProgram.stX (init p)).length
        = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hstT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (hpos : ∀ G : QuantumMaxCutEnergy.Input,
      1 ≤ Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  obtain ⟨C₀, kr, hcap⟩ := QMCLeafB.ConformanceM8.ledgerGT_MszG.2.2.2.2
  exact QMCLeafB.UnionShallow.solution_union_shallow_gen Kf k hKf hseed hK init
    QMCLeafB.ConformanceM8.roundGT QMCLeafB.RoundProgram.verdict
    hinit QMCLeafB.ConformanceM8.poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    QMCLeafB.CapGuard.MszG C₀ 6 (kr + 1) (by omega)
    (QMCLeafB.ConformanceM8.ledgerGT_of_ledgerGT
      QMCLeafB.ConformanceM8.ledgerGT_MszG).1
    (QMCLeafB.ConformanceM8.ledgerGT_of_ledgerGT
      QMCLeafB.ConformanceM8.ledgerGT_MszG).2
    (fun s => le_trans (hcap s) (Nat.mul_le_mul_left C₀
      (Nat.pow_le_pow_right (by omega : 1 ≤ (enc s).length + 1) (by omega : kr ≤ kr + 1))))
    hinitTape
    (fun G t _ hlo hhi => htop_roundGT_of_init init hnorm hfv hstT heps
      (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))
      (fun G' _ => hpos G') G t hlo hhi)
    hd

/-- **The final glue at the campaign round factor `Kbc2`** (this file's own count proof). -/
theorem endgame_final_at_roundGT
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hinit : Automatic.Poly init)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hnorm : ∀ p : QMCLeafB.FuelWire.Pkg,
      (QMCLeafB.RoundProgram.stX (init p)).length
        = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hstT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (k : ℕ) (hk : 20 ≤ 2 ^ k) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_final_at_roundGT_gen (fun G => QMCLeafB.UnionShallow.Kbc2
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G) k
    QMCLeafB.UnionShallow.poly_Kbc2_mHalve_mul
    (QMCLeafB.UnionShallow.Kbc2_mHalve_le_seed k hk)
    (fun G => QMCLeafB.UnionShallow.shallowKbound_Kbc2 G)
    init hinit hinitTape hnorm hfv hstT heps
    (fun G => QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hd

/-- **The final glue at m2's already-proved `4·Kbc` factor** — the same statement with the count
side taken from `LoopClose.Kbc4` instead of this file's `Kbc2`. -/
theorem endgame_final_at_roundGT_kbc4
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt)
    (hinit : Automatic.Poly init)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hnorm : ∀ p : QMCLeafB.FuelWire.Pkg,
      (QMCLeafB.RoundProgram.stX (init p)).length
        = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hstT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundProgram.stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.LoopClose.Kbc4
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf
          (fun G => QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
          (fun G => QMCLeafB.LoopClose.budgetRounds_le_Kbc4_dqShallow G _) G))
    (k : ℕ) (hk : 20 ≤ 2 ^ k) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_final_at_roundGT_gen (fun G => QMCLeafB.LoopClose.Kbc4
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G) k
    QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul
    (QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k (pow21_le hk))
    (fun G => QMCLeafB.LoopClose.budgetRounds_le_Kbc4_dqShallow G _)
    init hinit hinitTape hnorm hfv hstT heps
    (fun G => one_le_Kbc4_mul G) hd

/-! ## Smoke test: instantiated at the shelf's `RStInit.init0` the init-agnostic `htop` gives exactly
m7's `RoundT.htop_roundT_all`, so the lemma above is the same theorem, only freed of the init. -/

theorem htop_roundT_all_reproved (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
        QMCLeafB.RoundProgram.verdict T0 G t = true :=
  htop_roundT_of_init QMCLeafB.RStInit.init0
    (fun G t => QMCLeafB.HtopInit.fvR_init0 G t)
    (fun G t => QMCLeafB.RStInit.stT_init0 _)
    (fun G t => QMCLeafB.HtopFinish.epsOf_init0 _) T0 hpos


end QMCLeafB.UnionAtGT

/-! ## Axiom audit -/

#print axioms QMCLeafB.UnionAtGT.htop_roundT_of_init
#print axioms QMCLeafB.UnionAtGT.htop_roundGT_of_init
#print axioms QMCLeafB.UnionAtGT.endgame_final_at_roundGT
#print axioms QMCLeafB.UnionAtGT.htop_roundT_all_reproved
#print axioms QMCLeafB.UnionAtGT.endgame_final_at_roundGT_gen
#print axioms QMCLeafB.UnionAtGT.endgame_final_at_roundGT_kbc4
#print axioms QMCLeafB.UnionAtGT.one_le_Kbc4_mul


