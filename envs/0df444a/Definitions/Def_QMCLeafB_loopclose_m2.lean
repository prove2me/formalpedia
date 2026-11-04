-- Prove2me | Definitions.Def_QMCLeafB_loopclose_m2
-- name    : QMCLeafB_loopclose_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:54:44.665429+00:00
-- url     : https://prove2.me/theorems/c1904c8a-a75f-4406-a7e9-34cd09bfcf52
-- title:
--   QMCLeafB loopclose_m2
-- statement:
--   # leaf B phase 16 — `loopclose` (swarm `smw1ez4a9`, member m2, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_roundT_m7
import Definitions.Def_QMCLeafB_fuelwire_m4
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_round_program_m3
import Definitions.Def_QMCLeafB_dqbudget_m2
import Definitions.Def_QMCLeafB_integration_m6
import Definitions.Def_QMCLeafB_initdq_m1
/-
# leaf B phase 16 — `loopclose` (swarm `smw1ez4a9`, member m2, direction d6)

**The second closing stroke, and the `htop` slot absorbed into it.**

`QMCLeafB.LoopRestate.solution_of_loop_bounded` is the orbit-indexed stroke; the widest form of the
fuel wire on top of it is `FuelWire.solution_of_runParts_interior_monoF`, which asks for

    hK      : budgetRounds G (dqf G) (mHalve (n·n)) ≤ Kmono C e G      -- the round-count estimate
    horbit  : the per-initial-state size envelope along the `round`-orbit   -- the ledger
    hd      : one `RunParts` per interior `(G, t)` at `paramsMonoF dqf …`    -- the run brick

and nothing else.  This file removes the fourth slot, `htop`, by evaluating it: it proves

* `massV_init0` — the ℓ¹ mass of the initial weight code is `Rq G` (`∑_{i,j} |wMatrix G i j|`),
  the index arithmetic behind `epsOf (init0 p) = Rq G / 40000`;
* `htop_roundT` — the top-slice verdict at m7's `roundT`, for any tape-free round count `≥ 1`:
  on `[-Rq G/40000, 0]` the first round already reports `ok` (`fvR (init0) = 0` plus the slack),
  and the `ok` flag is never dropped;
* `endgame_loopclose` — `SolutionStatement` from `(hK, horbit, hd)` alone, at the guarded-round
  family `paramsMonoF dqf …` with `round := RoundT.roundT`.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.LoopClose

open QuantumMaxCutEnergy
open QMCNumericRuntime
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

local instance instRequestCodingLoopClose : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  ℓ¹ mass of a row-major code -/

/-- **The ℓ¹ mass of a row-major code is the ℓ¹ sum of its entries.** -/
theorem abs_sum_mk (n : ℕ) (f : ℕ → ℕ → ℚ) :
    ((MatQ.mk n f).map absq).sum = ∑ i : Fin n, ∑ j : Fin n, |f i j| := by
  have hm : (MatQ.mk n f).map absq
      = (List.range n).flatMap (fun i => (List.range n).map (fun j => absq (f i j))) := by
    rw [MatQ.mk, List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
  rw [hm, MatQ.sum_flatMap_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MatQ.list_sum_range]
  exact Finset.sum_congr rfl fun j _ => absq_eq (f i j)

/-! ## 2.  The initial state's mass is `Rq G` -/

/-- The weight code of the initial state is the row-major code of `wMatQ G`. -/
theorem stA_init0_eq_mk (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    stA (QMCLeafB.RStInit.init0 ((G, coins), t))
      = MatQ.mk G.n (QMCLeafB.RStInit.wVal
          (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))) := by
  show QMCLeafB.RStInit.wProg (QuantumMaxCutEnergy.encodeRequest (G, coins),
      parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins))) = _
  rw [QMCLeafB.RStInit.wProg_eq, QMCNumericRuntime.inputWidth_request]

/-- **The ℓ¹ mass at the initial state is `Rq G`.**  This is what `epsOf` reads, and hence the
numeric input of the top-slice verdict. -/
theorem massV_init0 (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 ((G, coins), t))
      = QMCLeafB.EngineRuntime.Rq G := by
  have hA := stA_init0_eq_mk G coins t
  have hval : ∀ i j : Fin G.n,
      QMCLeafB.RStInit.wVal (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))
          (i : ℕ) (j : ℕ) = QMCLeafB.RStInit.wMatQ G i j := by
    intro i j
    have h1 : MatQ.entry G.n (stA (QMCLeafB.RStInit.init0 ((G, coins), t))) i j
        = QMCLeafB.RStInit.wMatQ G i j :=
      (QMCLeafB.RStInit.stA_correct G coins t).2 i j
    have h2 : MatQ.entry G.n (stA (QMCLeafB.RStInit.init0 ((G, coins), t))) i j
        = QMCLeafB.RStInit.wVal (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))
            (i : ℕ) (j : ℕ) := by
      rw [hA]
      exact MatQ.entry_mk G.n _ i.isLt j.isLt
    rw [← h1, h2]
  calc QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 ((G, coins), t))
      = ((stA (QMCLeafB.RStInit.init0 ((G, coins), t))).map absq).sum := rfl
    _ = ((MatQ.mk G.n (QMCLeafB.RStInit.wVal
          (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins))))).map absq).sum := by
        rw [hA]
    _ = ∑ i : Fin G.n, ∑ j : Fin G.n,
          |QMCLeafB.RStInit.wVal (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))
            (i : ℕ) (j : ℕ)| := abs_sum_mk G.n _
    _ = ∑ i : Fin G.n, ∑ j : Fin G.n, |QMCLeafB.RStInit.wMatQ G i j| := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hval i j]
    _ = QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RStInit.abs_sum_wMatQ G

/-- The campaign slack at the initial state, read off the state. -/
theorem epsOf_init0 (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.RStInit.init0 ((G, coins), t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_init0 G coins t]
  ring

/-! ## 3.  The top-slice verdict at `roundT` -/

/-- **`htop` at `roundT`, for any tape-free round count `≥ 1`.**  On the top slice the initial point is
infeasible by exactly `-t`, so the slack test `fvR s ≤ stT s + epsOf s` fires at the first round
(`fvR (init0) = 0`, `epsOf (init0) = Rq G/40000`), and the recorded `ok` flag is never dropped
(`stOks_prefix_iterateT`). -/
theorem htop_roundT (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
      QMCLeafB.RoundProgram.verdict T0 G t = true := by
  rw [QMCLeafB.FinalStroke.loopBit_apply]
  refine QMCLeafB.RoundT.htop_roundT G t (hT G t) ?_
  have heps : QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := epsOf_init0 G [] t
  rw [heps]
  have hcast : ((0 : ℚ) : ℝ) ≤ ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
    push_cast
    push_cast at hlo
    linarith
  exact_mod_cast hcast

/-! ## 4.  The round factor is at least one -/

theorem one_le_Kmono_mul (C e : ℕ) (G : QuantumMaxCutEnergy.Input) :
    1 ≤ QMCLeafB.FuelWire.Kmono C e G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  have h1 : 1 ≤ QMCLeafB.FuelWire.Kmono C e G := by
    unfold QMCLeafB.FuelWire.Kmono
    omega
  have h2 : 1 ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) := QMCLeafB.HalvePerG.one_le_mHalve _
  calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
    _ ≤ QMCLeafB.FuelWire.Kmono C e G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) :=
        Nat.mul_le_mul h1 h2

/-! ## 5.  The closing stroke -/

/-- **`SolutionStatement` from three slots.**  Everything else is discharged: the four programs
(`RStInit.poly_init0`, `RoundT.poly_roundT`, `RoundProgram.poly_verdict`), the fuel and its exact
length (`FuelWire.poly_fuelOfProd`/`fuelOfProd_length`), the tape-freeness (`RStInit.init0_tape`),
`hspec` (`FinalStroke.hspec_of_tape_free`), the interior bracket split and `htop` (above).  What is
left is the round-count estimate `hK`, the orbit size ledger `horbit`, and the run brick `hd`. -/
theorem endgame_loopclose
    (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (C e c k : ℕ) (hC1 : 1 ≤ C) (hCc : C ≤ 8 ^ c) (hk : c + e + 8 ≤ 2 ^ k)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ QMCLeafB.FuelWire.Kmono C e G)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G').K
            * (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G').m)) G t
        (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_monoF dqf hdqf C e c k hC1 hCc hk hK
    QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_verdict
    sizes horbit QMCLeafB.RStInit.init0_tape
    (fun G t =>
      htop_roundT
        (fun G' _ => (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G').K
          * (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G').m)
        (fun G' _ => by
          show 1 ≤ (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G').K
            * (QMCLeafB.FuelWire.paramsMonoF dqf hdqf C e hC1 hK G').m
          rw [QMCLeafB.FuelWire.paramsMonoF_K, QMCLeafB.FuelWire.paramsMonoF_m]
          exact one_le_Kmono_mul C e G')
        G t)
    hd

/-! ## 6.  A round factor that carries the bit cost of `Rq`

`paramsMonoF`'s factor is `Kmono C e G = C·(n+1)^e + 1` — a monomial in `n` alone.  But
`budgetRounds G dq m = Nat.clog 2 ⌈2Φ₀/r^{n²}⌉₊ · m` with `r = dq/(8(Rq+1))`, so at any `dq ≤ 1` the
logarithm is at least `n²·log₂(8(Rq+1))`, i.e. it grows with the **bit length** of `Rq G`, which no
fixed-exponent monomial in `n` can dominate.  The family below carries that factor: it is m4's `Kbc`
(the factor whose bound is `RoundCountEstimate.budgetRounds_le_bitCost` at `dq = 1`), kept general in
`dq`.  Its fuel facts are already on the shelf (`poly_Kbc_mHalve_mul`, `Kbc_mHalve_le_seed`), so only
the budget inequality at the caller's `dq` is left. -/

/-- **The bit-cost-carrying parameter family**: tolerance `dqf G`, halving time `mHalve (n·n)`, round
factor `Kbc (mHalve (n·n)) G = mHalve·((n+1)²·(bitCost (Rq G) + n + 10))`. -/
noncomputable def paramsKbcF (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (G : QuantumMaxCutEnergy.Input) : QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOfK G (dqf G) (hdqf G)
    (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n))
    (QMCLeafB.HalvePerG.rmaxOf_nonneg (G.n * G.n))
    (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) (QMCLeafB.HalvePerG.one_le_mHalve _)
    (QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G) (hK G)
    (QMCLeafB.HalvePerG.hhalve_perG (G.n * G.n))

@[simp] theorem paramsKbcF_K (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (G : QuantumMaxCutEnergy.Input) :
    (paramsKbcF dqf hdqf hK G).K
      = QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := rfl

@[simp] theorem paramsKbcF_m (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (G : QuantumMaxCutEnergy.Input) :
    (paramsKbcF dqf hdqf hK G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-- `Kbc m G · m ≥ 1`, so the top-slice test can use any round count `≥ 1`. -/
theorem one_le_Kbc_mul (G : QuantumMaxCutEnergy.Input) :
    1 ≤ QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
        * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  rw [QMCLeafB.FuelWire.Kbc_eq]
  have h1 : 1 ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) := QMCLeafB.HalvePerG.one_le_mHalve _
  have h3 : 1 ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10 := by omega
  have h2 : 1 ≤ (G.n + 1) ^ 2
      * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10) := by
    calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
      _ ≤ (G.n + 1) ^ 2 * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10) :=
          Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) h3
  calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
    _ ≤ (QMCLeafB.HalvePerG.mHalve (G.n * G.n)
          * ((G.n + 1) ^ 2
            * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10)))
          * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h1

/-- **The closing stroke at the bit-cost family.**  `SolutionStatement` from the budget inequality at
the caller's own `dq` (brick 1's numeric half), the orbit size ledger (brick 2) and one `RunParts` per
interior `(G, t)` (brick 4) — the `htop` slot is discharged here. -/
theorem endgame_loopclose_kbc
    (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsKbcF dqf hdqf hK G').K * (paramsKbcF dqf hdqf hK G').m)) G t
        (paramsKbcF dqf hdqf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_of_params (paramsKbcF dqf hdqf hK) k
    QMCLeafB.FuelWire.poly_Kbc_mHalve_mul (QMCLeafB.FuelWire.Kbc_mHalve_le_seed k hk)
    QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_verdict
    sizes horbit QMCLeafB.RStInit.init0_tape
    (fun G t =>
      htop_roundT
        (fun G' _ => (paramsKbcF dqf hdqf hK G').K * (paramsKbcF dqf hdqf hK G').m)
        (fun G' _ => by
          show 1 ≤ (paramsKbcF dqf hdqf hK G').K * (paramsKbcF dqf hdqf hK G').m
          rw [paramsKbcF_K, paramsKbcF_m]
          exact one_le_Kbc_mul G')
        G t)
    hd

/-! ## 7.  The drip-free family: `K = 4·Kbc` at `dqShallow`, no numeric hypothesis

`DqBudget.budgetRounds_le_Kbc4` bounds the round count at the campaign's tolerance by `4·Kbc`; the
two fuel facts for that factor are proved here (the extra `4` costs one exponent of the seed, which
`Kbc_mul_seed_of_bound` has to spare).  The result is a parameter family whose every field is
discharged, so the closing stroke below needs only the orbit ledger and the run brick. -/

/-- **The round factor at the campaign's tolerance**: four copies of m4's `Kbc`. -/
def Kbc4 (m : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ := 4 * QMCLeafB.FuelWire.Kbc m G

/-- **`hK` at `dqShallow`, unconditionally.**  (`Rq G = 0` is the `dqShallow = 1` branch, where m4's
`dq = 1` bound applies.) -/
theorem budgetRounds_le_Kbc4_dqShallow (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G) m
      ≤ Kbc4 m G := by
  rcases lt_or_eq_of_le (QMCLeafB.EngineRuntime.Rq_nonneg G) with hlt | heq
  · exact QMCLeafB.DqBudget.budgetRounds_le_Kbc4 G hlt m
  · have hdq1 : QMCLeafB.RundataParams.dqShallow G = 1 := by
      unfold QMCLeafB.RundataParams.dqShallow
      rw [if_pos heq.symm]
    rw [hdq1]
    refine le_trans (QMCLeafB.FuelWire.budgetRounds_le_Kbc m G) ?_
    unfold Kbc4
    omega

/-- **The round count times the halving time is a program** at the campaign's family. -/
theorem poly_Kbc4_mHalve_mul :
    Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kbc4 (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) := by
  have h := QMCLeafB.FuelWire.poly_Kbc_mHalve_mul
  have h4 : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      (4 : ℕ) * (QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n))) :=
    QMCLeafB.FuelWire.poly_nat_mul (Automatic.Poly.const (β := ℕ) 4) h
  have heq : (fun p : QMCLeafB.FuelWire.Pkg =>
      Kbc4 (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n))
      = (fun p : QMCLeafB.FuelWire.Pkg =>
      (4 : ℕ) * (QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n))) := by
    funext p
    unfold Kbc4
    ring
  rw [heq]
  exact h4

/-- **The seed bound** for the `4·Kbc` factor: one more exponent than `Kbc`'s, which `2^k ≥ 21`
absorbs. -/
theorem Kbc4_mHalve_le_seed (k : ℕ) (hk : 21 ≤ 2 ^ k) (p : QMCLeafB.FuelWire.Pkg) :
    Kbc4 (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
      ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k) := by
  have hS8 : 8 ≤ QMCLeafB.FuelWire.seedLen p := QMCLeafB.FuelWire.seedLen_ge_eight p
  have hS1 : 1 ≤ QMCLeafB.FuelWire.seedLen p := by omega
  have hn : p.1.1.n + 1 ≤ QMCLeafB.FuelWire.seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : QMCLeafB.FuelWire.seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.FuelWire.seedLen_eq p
    omega
  have hA : (p.1.1.n + 1) ^ 2 ≤ QMCLeafB.FuelWire.seedLen p ^ 2 := Nat.pow_le_pow_left hn 2
  have hB : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10
      ≤ QMCLeafB.FuelWire.seedLen p ^ 4 := QMCLeafB.FuelWire.bitCost_add_le_seed_pow p
  have hAB : (p.1.1.n + 1) ^ 2
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10)
      ≤ QMCLeafB.FuelWire.seedLen p ^ 6 := QMCLeafB.FuelWire.mul_le_pow hA hB
  have h4 : (4 : ℕ) ≤ QMCLeafB.FuelWire.seedLen p ^ 1 := by
    rw [pow_one]
    omega
  have hAB4 : (4 : ℕ) * ((p.1.1.n + 1) ^ 2
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10))
      ≤ QMCLeafB.FuelWire.seedLen p ^ 7 := QMCLeafB.FuelWire.mul_le_pow h4 hAB
  have hm : QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n) ≤ QMCLeafB.FuelWire.seedLen p ^ 7 :=
    QMCLeafB.FuelWire.mHalve_le_seed p
  have hmm : QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
      * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
      ≤ QMCLeafB.FuelWire.seedLen p ^ (2 * 7) := by
    have h := Nat.mul_le_mul hm hm
    rw [← pow_add] at h
    simpa [two_mul] using h
  have hEq : Kbc4 (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
      = ((4 : ℕ) * ((p.1.1.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10)))
        * (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
            * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) := by
    unfold Kbc4 QMCLeafB.FuelWire.Kbc
    ring
  rw [hEq]
  calc ((4 : ℕ) * ((p.1.1.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10)))
        * (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
            * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n))
      ≤ QMCLeafB.FuelWire.seedLen p ^ 7 * QMCLeafB.FuelWire.seedLen p ^ (2 * 7) :=
        Nat.mul_le_mul hAB4 hmm
    _ = QMCLeafB.FuelWire.seedLen p ^ (7 + 2 * 7) := (pow_add _ _ _).symm
    _ ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k) := Nat.pow_le_pow_right hS1 (by omega)

/-- `Kbc4 · mHalve ≥ 1`, so the top-slice test applies at this family. -/
theorem one_le_Kbc4_mul (G : QuantumMaxCutEnergy.Input) :
    1 ≤ Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
        * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  have hm : 1 ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) := QMCLeafB.HalvePerG.one_le_mHalve _
  have hc : 1 ≤ (G.n + 1) ^ 2
      * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + (G.n + 9)) := by
    have h2 : 1 ≤ (G.n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + (G.n + 9) := by omega
    calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
      _ ≤ (G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + (G.n + 9)) :=
          Nat.mul_le_mul h2 h3
  have h1 : 1 ≤ Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := by
    unfold Kbc4 QMCLeafB.FuelWire.Kbc
    calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
      _ ≤ 4 * (QMCLeafB.HalvePerG.mHalve (G.n * G.n)
            * ((G.n + 1) ^ 2
              * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + (G.n + 9)))) := by
          refine Nat.mul_le_mul (by norm_num) ?_
          calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
            _ ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) * _ := Nat.mul_le_mul hm hc
  calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
    _ ≤ Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
          * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := Nat.mul_le_mul h1 hm

/-- **The campaign family**: tolerance `dqShallow G`, halving time `mHalve (n·n)`, round factor
`4·Kbc (mHalve (n·n)) G`, shallow ceiling `rmaxOf (n·n)`.  Every field is a theorem. -/
noncomputable def paramsShallow (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOfK G (QMCLeafB.RundataParams.dqShallow G)
    (QMCLeafB.RundataParams.dqShallow_pos G)
    (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n))
    (QMCLeafB.HalvePerG.rmaxOf_nonneg (G.n * G.n))
    (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) (QMCLeafB.HalvePerG.one_le_mHalve _)
    (Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (budgetRounds_le_Kbc4_dqShallow G (QMCLeafB.HalvePerG.mHalve (G.n * G.n)))
    (QMCLeafB.HalvePerG.hhalve_perG (G.n * G.n))

@[simp] theorem paramsShallow_K (G : QuantumMaxCutEnergy.Input) :
    (paramsShallow G).K = Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := rfl

@[simp] theorem paramsShallow_m (G : QuantumMaxCutEnergy.Input) :
    (paramsShallow G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

@[simp] theorem paramsShallow_dq (G : QuantumMaxCutEnergy.Input) :
    (paramsShallow G).dq = QMCLeafB.RundataParams.dqShallow G := rfl

/-- `K · m ≥ 1` at the campaign family. -/
theorem one_le_paramsShallow (G : QuantumMaxCutEnergy.Input) :
    1 ≤ (paramsShallow G).K * (paramsShallow G).m := by
  rw [paramsShallow_K, paramsShallow_m]
  exact one_le_Kbc4_mul G

/-- **The closing stroke with only two slots left.**  `SolutionStatement` from the orbit size ledger
at `roundT` (brick 2) and one `RunParts` per interior `(G, t)` at the campaign family (brick 4).
Everything else — the four programs, the fuel and its exact length, `hspec`, the bracket split,
`htop`, the round-count estimate and the parameter family itself — is discharged here. -/
theorem endgame_loopclose_shallow
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)) G t
        (paramsShallow G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_of_params paramsShallow k
    poly_Kbc4_mHalve_mul (Kbc4_mHalve_le_seed k hk)
    QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_verdict
    sizes horbit QMCLeafB.RStInit.init0_tape
    (fun G t =>
      htop_roundT (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)
        (fun G' _ => one_le_paramsShallow G') G t)
    hd

/-! ## 8.  The ledger slot from a one-step charge -/

/-- **`horbit` at `roundT` from the three ledger slots.**  A thin wrapper over
`IntegrateM6.orbit_envelope` at the round the closing stroke actually runs (`RoundT.roundT`), so that
brick 2 may deliver `(M, C₀, c, k, hMinv, hstep, hM)` instead of the envelope itself. -/
theorem horbit_roundT_of_ledger (M : QMCLeafB.RoundProgram.RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hMinv : ∀ s, M (QMCLeafB.RoundT.roundT s) ≤ M s + c)
    (hstep : ∀ s, (enc (QMCLeafB.RoundT.roundT s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k) :
    ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) k).eval
            (QMCLeafB.SimPoly.encSt a).length :=
  QMCLeafB.IntegrateM6.orbit_envelope QMCLeafB.RoundT.roundT M C₀ c k hk hMinv hstep hM

/-- **The same closing stroke with the ledger supplied by its three slots.** -/
theorem endgame_loopclose_ledger
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (M : QMCLeafB.RoundProgram.RSt → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (QMCLeafB.RoundT.roundT s) ≤ M s + c)
    (hstep : ∀ s, (enc (QMCLeafB.RoundT.roundT s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)) G t
        (paramsShallow G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_loopclose_shallow k hk (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) kr)
    (horbit_roundT_of_ledger M C₀ c kr hkr hMinv hstep hM) hd

/-! ## 8b.  Field lemmas for the campaign family (for brick 4) -/

@[simp] theorem paramsShallow_rmax (G : QuantumMaxCutEnergy.Input) :
    (paramsShallow G).rmax = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

@[simp] theorem paramsShallow_cAq (G : QuantumMaxCutEnergy.Input) :
    (paramsShallow G).cAq = QMCLeafB.EngineRuntime.Rq G := rfl

/-- The clip box `2n² + 2·dq²` at the campaign family is m6's `MOfS` — the parameter `init0`'s
`stX` must be packed at. -/
theorem paramsShallow_box (G : QuantumMaxCutEnergy.Input) :
    2 * (G.n : ℚ) ^ 2 + 2 * (paramsShallow G).dq ^ 2
      = QMCLeafB.NumCert.MOfS G := by
  rw [paramsShallow_dq]
  exact (QMCLeafB.NumCert.MOfS_eq G).symm

/-- The round count in the shape a run brick reads it. -/
theorem paramsShallow_count (G : QuantumMaxCutEnergy.Input) :
    (paramsShallow G).K * (paramsShallow G).m
      = 4 * (QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
          * QMCLeafB.HalvePerG.mHalve (G.n * G.n)) := by
  rw [paramsShallow_K, paramsShallow_m]
  unfold Kbc4
  ring

/-! ## 9.  The leaf's sentence, verbatim -/

/-- **`d9f601e5`, verbatim, from the two remaining slots.**  The type is the leaf's own sentence
(`SolutionStatement`'s body, which `solutionStatement_iff_wMatrix` identifies with the `wMatrix`
form); the proof is the closing stroke above. -/
theorem solution_of_leaf
    (k : ℕ) (hk : 21 ≤ 2 ^ k) (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)) G t
        (paramsShallow G)) :
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
  endgame_loopclose_shallow k hk sizes horbit hd

/-! ## 10.  The campaign initial state (`InitDq.init0`, box `2n² + 2·dqShallow²`)

§1–§9 run at `RStInit.init0`, whose box is `2n² + 2·1²`.  The run brick needs the box to be
`2n² + 2·P.dq²` at `P.dq = dqShallow` (its `hwit`/`hcut` name `initShapeOf (n·n) (2n²+2·P.dq²)`), so
the closing stroke must start from m1's `InitDq.init0`.  Everything below is §§1–9 at that state:
its weight code is the same (`InitDq` reuses `RStInit.wProg`), so the ℓ¹ mass is again `Rq G`. -/

/-- The weight code of `InitDq.init0` is the row-major code of `wMatQ G`. -/
theorem stA_init0D_eq_mk (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    stA (QMCLeafB.InitDq.init0 ((G, coins), t))
      = MatQ.mk G.n (QMCLeafB.RStInit.wVal
          (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))) := by
  show QMCLeafB.RStInit.wProg (QuantumMaxCutEnergy.encodeRequest (G, coins),
      parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins))) = _
  rw [QMCLeafB.RStInit.wProg_eq, QMCNumericRuntime.inputWidth_request]

/-- **The ℓ¹ mass at the campaign initial state is `Rq G`.** -/
theorem massV_init0D (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 ((G, coins), t))
      = QMCLeafB.EngineRuntime.Rq G := by
  have hA := stA_init0D_eq_mk G coins t
  have hval : ∀ i j : Fin G.n,
      QMCLeafB.RStInit.wVal (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))
          (i : ℕ) (j : ℕ) = QMCLeafB.RStInit.wMatQ G i j := by
    intro i j
    have h1 : MatQ.entry G.n (stA (QMCLeafB.InitDq.init0 ((G, coins), t))) i j
        = QMCLeafB.RStInit.wMatQ G i j :=
      (QMCLeafB.InitDq.stA_correct G coins t).2 i j
    have h2 : MatQ.entry G.n (stA (QMCLeafB.InitDq.init0 ((G, coins), t))) i j
        = QMCLeafB.RStInit.wVal (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))
            (i : ℕ) (j : ℕ) := by
      rw [hA]
      exact MatQ.entry_mk G.n _ i.isLt j.isLt
    rw [← h1, h2]
  calc QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 ((G, coins), t))
      = ((stA (QMCLeafB.InitDq.init0 ((G, coins), t))).map absq).sum := rfl
    _ = ((MatQ.mk G.n (QMCLeafB.RStInit.wVal
          (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins))))).map absq).sum := by
        rw [hA]
    _ = ∑ i : Fin G.n, ∑ j : Fin G.n,
          |QMCLeafB.RStInit.wVal (parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))
            (i : ℕ) (j : ℕ)| := abs_sum_mk G.n _
    _ = ∑ i : Fin G.n, ∑ j : Fin G.n, |QMCLeafB.RStInit.wMatQ G i j| := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hval i j]
    _ = QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RStInit.abs_sum_wMatQ G

/-- The campaign slack at `InitDq.init0`. -/
theorem epsOf_init0D (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 ((G, coins), t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_init0D G coins t]
  ring

/-- **`htop` at `roundT` from the campaign initial state.** -/
theorem htop_roundT_D (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT
      QMCLeafB.RoundProgram.verdict T0 G t = true := by
  rw [QMCLeafB.FinalStroke.loopBit_apply]
  set s := QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t) with hs
  have hfv : QMCLeafB.RoundProgram.fvR s = 0 := QMCLeafB.InitDq.fvR_init0 G t
  have ht : stT s = t := QMCLeafB.InitDq.stT_init0 _
  have heps : QMCLeafB.RoundT.epsOf s = QMCLeafB.EngineRuntime.Rq G / 40000 :=
    epsOf_init0D G [] t
  have hslack : 0 ≤ t + QMCLeafB.RoundT.epsOf s := by
    rw [heps]
    have hcast : ((0 : ℚ) : ℝ) ≤ ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
      push_cast
      push_cast at hlo
      linarith
    exact_mod_cast hcast
  have hbranch : QMCLeafB.RoundProgram.fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s := by
    rw [hfv, ht]
    exact hslack
  have hok : QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT s)
      = QMCLeafB.RoundProgram.stOks s ++ [true] := by
    rw [QMCLeafB.RoundT.roundT, if_pos hbranch]
    rfl
  have hmem : true ∈ QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[1] s) := by
    rw [Function.iterate_one, hok]
    exact List.mem_append_right _ (List.mem_singleton_self true)
  have hle : (1 : ℕ) ≤ T0 G t := hT G t
  have hpre : QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[1] s)
      <+: QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundT.roundT^[T0 G t] s) :=
    QMCLeafB.RoundT.stOks_prefix_iterateT s hle
  exact QMCLeafB.Htop.verdict_of_mem (hpre.mem hmem)

/-- **The closing stroke at the campaign initial state.**  Two slots: the orbit ledger at `roundT`
(brick 2) and `RunParts` at `paramsShallow` (brick 4).  The box of `InitDq.init0` is
`2n² + 2·dqShallow²` (`paramsShallow_box`), which is exactly the matrix `RunParts.hwit`/`hcut` name. -/
theorem endgame_loopclose_campaign
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)) G t
        (paramsShallow G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_of_params paramsShallow k
    poly_Kbc4_mHalve_mul (Kbc4_mHalve_le_seed k hk)
    QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT QMCLeafB.RoundProgram.verdict
    QMCLeafB.InitDq.poly_init0 QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_verdict
    sizes horbit QMCLeafB.InitDq.init0_tape
    (fun G t =>
      htop_roundT_D (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)
        (fun G' _ => one_le_paramsShallow G') G t)
    hd

/-- **`d9f601e5`, verbatim, at the campaign initial state.** -/
theorem solution_of_leaf_campaign
    (k : ℕ) (hk : 21 ≤ 2 ^ k) (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)) G t
        (paramsShallow G)) :
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
  endgame_loopclose_campaign k hk sizes horbit hd

/-! ## 11.  The stroke at an arbitrary round factor (so brick 4 may pick `K`) -/

/-- **The campaign family at a caller-chosen round factor** `Kf` (any `Kf` above `budgetRounds` at
`dqShallow`). -/
noncomputable def paramsFamilyK (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) : QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOfK G (QMCLeafB.RundataParams.dqShallow G)
    (QMCLeafB.RundataParams.dqShallow_pos G)
    (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n))
    (QMCLeafB.HalvePerG.rmaxOf_nonneg (G.n * G.n))
    (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) (QMCLeafB.HalvePerG.one_le_mHalve _)
    (Kf G) (hK G) (QMCLeafB.HalvePerG.hhalve_perG (G.n * G.n))

@[simp] theorem paramsFamilyK_K (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G) (G : QuantumMaxCutEnergy.Input) :
    (paramsFamilyK Kf hK G).K = Kf G := rfl

@[simp] theorem paramsFamilyK_m (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G) (G : QuantumMaxCutEnergy.Input) :
    (paramsFamilyK Kf hK G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

@[simp] theorem paramsFamilyK_dq (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G) (G : QuantumMaxCutEnergy.Input) :
    (paramsFamilyK Kf hK G).dq = QMCLeafB.RundataParams.dqShallow G := rfl

/-- **The closing stroke at any round factor.**  The caller supplies the round factor `Kf`, its
budget inequality at `dqShallow`, and the two fuel facts about `Kf · mHalve`; the stroke supplies
everything else.  `paramsShallow` is the case `Kf = Kbc4 (mHalve (n·n))`, whose three facts are in
§7. -/
theorem endgame_loopclose_family
    (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hpoly : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hone : ∀ G : QuantumMaxCutEnergy.Input,
      1 ≤ Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsFamilyK Kf hK G').K * (paramsFamilyK Kf hK G').m)) G t
        (paramsFamilyK Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_of_params (paramsFamilyK Kf hK) k
    (by simpa using hpoly) (by simpa using hseed)
    QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT QMCLeafB.RoundProgram.verdict
    QMCLeafB.InitDq.poly_init0 QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_verdict
    sizes horbit QMCLeafB.InitDq.init0_tape
    (fun G t =>
      htop_roundT_D (fun G' _ => (paramsFamilyK Kf hK G').K * (paramsFamilyK Kf hK G').m)
        (fun G' _ => by simpa using hone G') G t)
    hd

/-! ## 12.  The ledger at `roundT` is the ledger at `round` (plus the frozen branch)

`RoundProgram.round` is `if (oracleR s).1 then roundCut s else roundOk s` and
`RoundT.roundT` is `if fvR s ≤ stT s + epsOf s then roundOk s else round s`.  Both only ever do
`roundCut` or `roundOk`, so **every per-step estimate that covers `round` and `roundOk` covers
`roundT`**: brick 2's ledger for `round` transfers to the round the closing stroke runs. -/

theorem roundT_eq_round_or_roundOk (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundT.roundT s = QMCLeafB.RoundProgram.round s
      ∨ QMCLeafB.RoundT.roundT s = QMCLeafB.RoundProgram.roundOk s := by
  by_cases h : QMCLeafB.RoundProgram.fvR s
      ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · exact Or.inr (by rw [QMCLeafB.RoundT.roundT, if_pos h])
  · exact Or.inl (by rw [QMCLeafB.RoundT.roundT, if_neg h])

/-- **`horbit` at `roundT` from the two branches.**  The hypotheses are exactly what a `round`
ledger proves (`hMinvR`, `hstepR`) plus the frozen branch `roundOk`, whose charge is a single flag. -/
theorem horbit_roundT_of_both (M : QMCLeafB.RoundProgram.RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hMinvR : ∀ s, M (QMCLeafB.RoundProgram.round s) ≤ M s + c)
    (hMinvOk : ∀ s, M (QMCLeafB.RoundProgram.roundOk s) ≤ M s + c)
    (hstepR : ∀ s, (enc (QMCLeafB.RoundProgram.round s)).length
      ≤ max ((enc s).length + c) (M s))
    (hstepOk : ∀ s, (enc (QMCLeafB.RoundProgram.roundOk s)).length
      ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k) :
    ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundT.roundT^[j] a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) k).eval
            (QMCLeafB.SimPoly.encSt a).length := by
  refine horbit_roundT_of_ledger M C₀ c k hk ?_ ?_ hM
  · intro s
    rcases roundT_eq_round_or_roundOk s with h | h
    · rw [h]; exact hMinvR s
    · rw [h]; exact hMinvOk s
  · intro s
    rcases roundT_eq_round_or_roundOk s with h | h
    · rw [h]; exact hstepR s
    · rw [h]; exact hstepOk s

/-- **The closing stroke with brick 2's `round` ledger as the only size input.** -/
theorem endgame_loopclose_of_round_ledger
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (M : QMCLeafB.RoundProgram.RSt → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinvR : ∀ s, M (QMCLeafB.RoundProgram.round s) ≤ M s + c)
    (hMinvOk : ∀ s, M (QMCLeafB.RoundProgram.roundOk s) ≤ M s + c)
    (hstepR : ∀ s, (enc (QMCLeafB.RoundProgram.round s)).length
      ≤ max ((enc s).length + c) (M s))
    (hstepOk : ∀ s, (enc (QMCLeafB.RoundProgram.roundOk s)).length
      ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (paramsShallow G').K * (paramsShallow G').m)) G t
        (paramsShallow G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_loopclose_campaign k hk (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) kr)
    (horbit_roundT_of_both M C₀ c kr hkr hMinvR hMinvOk hstepR hstepOk hM) hd

end QMCLeafB.LoopClose

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.LoopClose.abs_sum_mk
#print axioms QMCLeafB.LoopClose.stA_init0_eq_mk
#print axioms QMCLeafB.LoopClose.massV_init0
#print axioms QMCLeafB.LoopClose.epsOf_init0
#print axioms QMCLeafB.LoopClose.htop_roundT
#print axioms QMCLeafB.LoopClose.one_le_Kmono_mul
#print axioms QMCLeafB.LoopClose.endgame_loopclose
#print axioms QMCLeafB.LoopClose.paramsKbcF_K
#print axioms QMCLeafB.LoopClose.one_le_Kbc_mul
#print axioms QMCLeafB.LoopClose.endgame_loopclose_kbc
#print axioms QMCLeafB.LoopClose.budgetRounds_le_Kbc4_dqShallow
#print axioms QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul
#print axioms QMCLeafB.LoopClose.Kbc4_mHalve_le_seed
#print axioms QMCLeafB.LoopClose.one_le_Kbc4_mul
#print axioms QMCLeafB.LoopClose.one_le_paramsShallow
#print axioms QMCLeafB.LoopClose.endgame_loopclose_shallow
#print axioms QMCLeafB.LoopClose.horbit_roundT_of_ledger
#print axioms QMCLeafB.LoopClose.endgame_loopclose_ledger
#print axioms QMCLeafB.LoopClose.paramsShallow_box
#print axioms QMCLeafB.LoopClose.paramsShallow_count
#print axioms QMCLeafB.LoopClose.solution_of_leaf
#print axioms QMCLeafB.LoopClose.massV_init0D
#print axioms QMCLeafB.LoopClose.epsOf_init0D
#print axioms QMCLeafB.LoopClose.htop_roundT_D
#print axioms QMCLeafB.LoopClose.endgame_loopclose_campaign
#print axioms QMCLeafB.LoopClose.solution_of_leaf_campaign
#print axioms QMCLeafB.LoopClose.endgame_loopclose_family
#print axioms QMCLeafB.LoopClose.roundT_eq_round_or_roundOk
#print axioms QMCLeafB.LoopClose.horbit_roundT_of_both
#print axioms QMCLeafB.LoopClose.endgame_loopclose_of_round_ledger


