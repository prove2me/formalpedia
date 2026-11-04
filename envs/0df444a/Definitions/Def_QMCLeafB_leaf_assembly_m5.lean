-- Prove2me | Definitions.Def_QMCLeafB_leaf_assembly_m5
-- name    : QMCLeafB_leaf_assembly_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:28:41.946346+00:00
-- url     : https://prove2.me/theorems/90f2142a-50f2-4c45-97a0-093314ce3f49
-- title:
--   QMCLeafB leaf_assembly_m5
-- statement:
--   # leaf B phase 16 — brick 5 `leaf-assembly` (swarm `smw1ez4a9`, member m5, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_initdq_m1
import Definitions.Def_QMCLeafB_union_roundgt_m5
/-
# leaf B phase 16 — brick 5 `leaf-assembly` (swarm `smw1ez4a9`, member m5, direction d8)

The last glue step: instantiate `UnionAtGT.endgame_final_at_roundGT` (which already discharges the
numeric half, the size ledger and `htop`) at **m1's init** `QMCLeafB.InitDq.init0` — the init packed
at the campaign tolerance `2n² + 2·dqShallow²`, which is the cap `RunParts.hwit`/`hcut` name.

What this file adds is exactly one bridge: `epsOf (InitDq.init0 p) = Rq p.1.1 / 40000` (the ℓ¹ mass
of the weight code is the total weight), together with the trivial re-statements of m1's facts in the
`noTape` form the glue asks for.  After this file the leaf has **one** hypothesis left: brick 4's
`RunParts` at `UnionShallow.paramsKbc2` (or at m2's `Kbc4` family, second version below).

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audits at the end.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.LeafAssembly

open QuantumMaxCutEnergy
open QMCNumericRuntime
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

local instance instRequestCodingLeafAssembly : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The weight code and its ℓ¹ mass at `InitDq.init0` -/

/-- **The code of m1's `init0` is `MatQ.mk G.n (wVal …)`.** -/
theorem stA_InitDq_eq_mk (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    QMCLeafB.RoundProgram.stA (QMCLeafB.InitDq.init0 ((G, coins), t))
      = MatQ.mk G.n (QMCLeafB.RStInit.wVal (inputEdges G)) := by
  have h1 : QMCLeafB.RoundProgram.stA (QMCLeafB.InitDq.init0 ((G, coins), t))
      = QMCLeafB.RStInit.wProg (QuantumMaxCutEnergy.encodeRequest (G, coins),
          QMCNumericRuntime.parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins))) := rfl
  rw [h1, QMCLeafB.RStInit.wProg_eq, QMCNumericRuntime.inputWidth_request,
    QMCNumericRuntime.parseEdges_request]

/-- The entries of the code are `wMatQ G`. -/
theorem wVal_InitDq_eq_wMatQ (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ)
    (i j : Fin G.n) :
    QMCLeafB.RStInit.wVal (inputEdges G) (i : ℕ) (j : ℕ) = QMCLeafB.RStInit.wMatQ G i j := by
  have h := QMCLeafB.InitDq.stA_correct_noTape G t
  have h2 : MatQ.entry G.n (QMCLeafB.RoundProgram.stA
      (QMCLeafB.InitDq.init0 ((G, []), t))) i j = QMCLeafB.RStInit.wMatQ G i j := h.2 i j
  rw [stA_InitDq_eq_mk, MatQ.entry_mk G.n _ i.isLt j.isLt] at h2
  exact h2

/-- **The ℓ¹ mass of m1's initial weight code is `Rq G`.** -/
theorem massV_InitDq (p : QMCLeafB.FuelWire.Pkg) :
    QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 := by
  obtain ⟨⟨G, coins⟩, t⟩ := p
  unfold QMCLeafB.RoundT.massV
  rw [stA_InitDq_eq_mk, QMCLeafB.HtopFinish.sum_map_mk,
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
    rw [QMCLeafB.RoundProgram.absq_eq, wVal_InitDq_eq_wMatQ G coins t i j]

/-- **`epsOf (InitDq.init0 p) = Rq p.1.1 / 40000`** — the bridge `htop` needs. -/
theorem epsOf_InitDq (p : QMCLeafB.FuelWire.Pkg) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_InitDq]
  ring

/-! ## 2.  The leaf at m1's init: one hypothesis left -/

/-- **`SolutionStatement` from brick 4 alone**, at the campaign family `paramsKbc2`, on m1's init,
at the guarded slack round. -/
theorem endgame_at_InitDq
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (k : ℕ) (hk : 20 ≤ 2 ^ k) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionAtGT.endgame_final_at_roundGT QMCLeafB.InitDq.init0
    QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init0_tape QMCLeafB.InitDq.init_normalised
    QMCLeafB.InitDq.fvR_init0
    (fun G t => QMCLeafB.InitDq.stT_init0 _)
    (fun G t => epsOf_InitDq _) hd k hk

/-- The same at m2's already-proved `4·Kbc` round factor. -/
theorem endgame_at_InitDq_kbc4
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.LoopClose.Kbc4
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf
          (fun G => QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
          (fun G => QMCLeafB.LoopClose.budgetRounds_le_Kbc4_dqShallow G _) G))
    (k : ℕ) (hk : 20 ≤ 2 ^ k) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionAtGT.endgame_final_at_roundGT_kbc4 QMCLeafB.InitDq.init0
    QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init0_tape QMCLeafB.InitDq.init_normalised
    QMCLeafB.InitDq.fvR_init0
    (fun G t => QMCLeafB.InitDq.stT_init0 _)
    (fun G t => epsOf_InitDq _) hd k hk


/-! ## 3.  The verbatim `d9f601e5` statement, one hypothesis away -/

/-- **`d9f601e5` from brick 4 alone**, in the leaf's verbatim form (`statement_lock_of_solutionStatement`
is definitional, so this is the repackage itself). -/
theorem solution_of_brick4
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (k : ℕ) (hk : 20 ≤ 2 ^ k) :
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
  QMCLeafB.ConformanceM8.statement_lock_of_solutionStatement
    (endgame_at_InitDq hd k hk)


/-- **`d9f601e5` from brick 4 at m2's `paramsShallow` family** (`K = 4·Kbc`), verbatim.  This is the
form the two `solution_of_leaf`-level endpoints agree on. -/
theorem solution_of_brick4_kbc4
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.ConformanceM8.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.LoopClose.Kbc4
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.LoopClose.paramsShallow G))
    (k : ℕ) (hk : 20 ≤ 2 ^ k) :
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
  QMCLeafB.ConformanceM8.statement_lock_of_solutionStatement
    (endgame_at_InitDq_kbc4 hd k hk)

end QMCLeafB.LeafAssembly

/-! ## Axiom audit -/

#print axioms QMCLeafB.LeafAssembly.stA_InitDq_eq_mk
#print axioms QMCLeafB.LeafAssembly.massV_InitDq
#print axioms QMCLeafB.LeafAssembly.epsOf_InitDq
#print axioms QMCLeafB.LeafAssembly.endgame_at_InitDq
#print axioms QMCLeafB.LeafAssembly.endgame_at_InitDq_kbc4
#print axioms QMCLeafB.LeafAssembly.solution_of_brick4
#print axioms QMCLeafB.LeafAssembly.solution_of_brick4_kbc4


