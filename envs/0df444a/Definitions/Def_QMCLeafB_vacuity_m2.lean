-- Prove2me | Definitions.Def_QMCLeafB_vacuity_m2
-- name    : QMCLeafB_vacuity_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:08:48.344893+00:00
-- url     : https://prove2.me/theorems/0659f164-f245-4439-933a-b2122411cc72
-- title:
--   QMCLeafB vacuity_m2
-- statement:
--   # leaf B phase 17 — brick `non-vacuity / family gluing` (swarm `smw1gfajf`, member m2, direction d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_solution_lock_m7
import Definitions.Def_QMCLeafB_runparts_stream_m4
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_conformance_m8
/-
# leaf B phase 17 — brick `non-vacuity / family gluing` (swarm `smw1gfajf`, member m2, direction d7)

The endgame is one hypothesis away: `Check_htop_solution_lock_m7.solution_of_hd` concludes the
verbatim `d9f601e5` sentence from

    hd : ∀ G t, 2 ≤ G.n → -Rq G ≤ t → (t : ℝ) < -(Rq G / 40000) → RunParts (loopBit …) G t (paramsKbc2 G)

plus the `InitDq.init0` facts.  This file does not attempt any residual slot of `hd`; it audits the
*target instantiation* itself, which no other direction holds:

1. **Non-vacuity of the interior branch.**  `hd`'s guard is satisfiable exactly when `Rq G > 0`, and
   concretely at `t = -Rq G`.  So `hd` is a substantive demand at every graph with a positive weight,
   and it is vacuously satisfied exactly at `Rq G = 0` (the zero-edge branch).  In particular the
   final stroke is never applied to an empty hypothesis set without our knowing it.
2. **Family gluing at the exact target.**  `UnionShallow.paramsKbc2 G` **is**
   `UnionShallow.paramsShallowKf Kf4 hK4 G` (an `abbrev`, so `rfl`), and that family **is**
   `HalvePerG.paramsK G (dqShallow G) (dqShallow_pos G) (Kf4 G) (hK4 G)` — the family m4's
   `RunPartsStream.paramsK_side_conditions` is stated at.  Hence the three scalars of the stream
   conduit are discharged at the family `hd` names, with no instantiation left implicit.
3. **The conduit lands at `hd`'s conclusion.**  `runParts_paramsKbc2_of_stream_data` is
   `RunPartsStream.runParts_of_stream_data` at `P := paramsKbc2 G` with the scalar hypotheses
   (ceiling positivity/boundedness, ok-branch rounding budget) already discharged, so its conclusion
   is *verbatim* the body of `hd` and its hypotheses are exactly the stream bundle of brick 4.
4. **`hstated` is forced, not free** (§4, machine-checked reduction): with `hqSurr` in force, the
   direction-side state budget is the trace inequality
   `∑_{j<k} μ_j · (flat ones ⪝ p_j) ≤ ∑_i (cX k) i i`; the shortcut "take `qSurr := flat ∘ cX`" is not
   available, since `qSurr` is pinned by `hqSurr`.  §4 is the bookkeeping the slot owners need.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open Matrix
open QuantumMaxCutEnergy

noncomputable section

namespace QMCLeafB.NonVacuity

/-! ## 1.  The interior bracket is inhabited iff `Rq` is positive

`hd` is demanded on `-Rq G ≤ t` and `(t : ℝ) < -(Rq G / 40000)`.  The width of that half-open
interval is `Rq G · (1 − 1/40000)`, so it is inhabited exactly at positive total weight.  This is the
non-vacuity statement for the interior branch of the leaf. -/

/-- **The guards of `hd` force positive total weight.**  (Hence `hd` is never asked at `Rq = 0`.) -/
theorem Rq_pos_of_bracket (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    0 < QMCLeafB.EngineRuntime.Rq G := by
  have h1 : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hlo
  have h2 : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ)
      < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := lt_of_le_of_lt h1 hhi
  have h3 : (0 : ℝ) < (QMCLeafB.EngineRuntime.Rq G : ℝ) := by
    have e1 : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ)
        = -(QMCLeafB.EngineRuntime.Rq G : ℝ) := by push_cast; ring
    have e2 : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        = -((QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000) := by push_cast; ring
    rw [e1, e2] at h2
    nlinarith
  exact_mod_cast h3

/-- **At positive total weight the interior bracket is inhabited**, at the left endpoint `t = -Rq G`
(the worst admissible threshold of the leaf). -/
theorem bracket_inhabited_of_Rq_pos (G : QuantumMaxCutEnergy.Input)
    (h : 0 < QMCLeafB.EngineRuntime.Rq G) :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  refine ⟨-QMCLeafB.EngineRuntime.Rq G, le_rfl, ?_⟩
  have hR : (0 : ℝ) < (QMCLeafB.EngineRuntime.Rq G : ℝ) := by exact_mod_cast h
  have e1 : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ)
      = -(QMCLeafB.EngineRuntime.Rq G : ℝ) := by push_cast; ring
  have e2 : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      = -((QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000) := by push_cast; ring
  rw [e1, e2]
  nlinarith

/-- **Non-vacuity, in one line**: the interior foot of `hd` is asked at `G` iff `G` carries weight. -/
theorem bracket_inhabited_iff (G : QuantumMaxCutEnergy.Input) :
    (∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
        (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      ↔ 0 < QMCLeafB.EngineRuntime.Rq G := by
  constructor
  · rintro ⟨t, hlo, hhi⟩
    exact Rq_pos_of_bracket G t hlo hhi
  · exact bracket_inhabited_of_Rq_pos G

/-- **A positive edge forces the interior branch to be exercised.**  `Rq G = 2 ∑ₑ wₑ`, so a single
nonneg-rational weight strictly above zero makes `Rq G > 0` and hence the bracket of `hd` inhabited. -/
theorem Rq_pos_of_weight_pos (G : QuantumMaxCutEnergy.Input)
    (e : QuantumMaxCutEnergy.Edge G.n) (h : 0 < G.weights e) :
    0 < QMCLeafB.EngineRuntime.Rq G := by
  unfold QMCLeafB.EngineRuntime.Rq
  have hsingle := Finset.single_le_sum
    (f := fun e' : QuantumMaxCutEnergy.Edge G.n => ((G.weights e' : ℚ≥0) : ℚ))
    (fun i _ => by positivity) (Finset.mem_univ e)
  have hpos : (0 : ℚ) < ((G.weights e : ℚ≥0) : ℚ) := by
    simpa using h
  linarith

/-- The zero-weight case: the interior branch is empty, so `hd` costs nothing there (this is the
`ZeroEdge` corner of the campaign; the statement is m5's, restated in the form used above). -/
theorem bracket_empty_of_Rq_nonpos (G : QuantumMaxCutEnergy.Input)
    (h : QMCLeafB.EngineRuntime.Rq G ≤ 0) :
    ¬ ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  rintro ⟨t, hlo, hhi⟩
  have hpos := Rq_pos_of_bracket G t hlo hhi
  linarith

/-! ## 2.  Family gluing: `paramsKbc2` is the stream conduit's family at the campaign constants -/

/-- **The target family is the `paramsShallowKf` family** at the `Kbc2` round factor (both are
`abbrev`s over `HalvePerG.paramsK`, so this is definitional). -/
theorem paramsKbc2_eq_paramsShallowKf (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.UnionShallow.paramsKbc2 G
      = QMCLeafB.UnionShallow.paramsShallowKf
          (fun G => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
          (fun G => QMCLeafB.UnionShallow.shallowKbound_Kbc2 G) G := rfl

/-- **`paramsShallowKf` is `HalvePerG.paramsK` at `dqShallow`** — the family m4's stream conduit is
stated at.  (The prose claim of `Check_runparts_stream_m4` §8, machine-checked.) -/
theorem paramsShallowKf_eq_paramsK (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.UnionShallow.paramsShallowKf Kf hK G
      = QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
          (QMCLeafB.RundataParams.dqShallow_pos G) (Kf G) (hK G) := rfl

/-- **The fields of `paramsKbc2`, spelled out** (the data `RunParts`'s records are indexed by). -/
theorem paramsKbc2_fields (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).K
        = QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n)
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G).dq = QMCLeafB.RundataParams.dqShallow G
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G).rmax
          = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The tolerance of the target family is strictly positive — so `hdiagc`'s `1 − dq/4` slab and the
halving ceiling are non-degenerate. -/
theorem paramsKbc2_dq_pos (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).dq :=
  QMCLeafB.RundataParams.dqShallow_pos G

/-- **The three scalar hypotheses of the stream conduit, at `paramsKbc2`, with no side conditions
beyond `2 ≤ G.n` and positive weight** (the latter is forced by `hd`'s own guards, §1). -/
theorem paramsKbc2_side_conditions (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).rmax
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G).rmax ≤ 1
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G).dq = QMCLeafB.RundataParams.dqShallow G
      ∧ (QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
            (3 * (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
          + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2
          - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G) :=
  QMCLeafB.RunPartsStream.paramsK_side_conditions G hn hRq
    (QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (QMCLeafB.UnionShallow.shallowKbound_Kbc2 G)

/-! ## 3.  The conduit at the exact target family

`RunPartsStream.runParts_of_stream_data` is *generic* in the parameter family `P`, so it lands at
`paramsKbc2` — the family `hd` names — as soon as its three scalar hypotheses are discharged, which
§2 does.  The conclusion below is **verbatim** the body of `hd`
(`Check_htop_solution_lock_m7.solution_of_hd`), so `hd` follows from the stream bundle alone:
`fun G t hn hlo hhi => runParts_paramsKbc2_of_stream_data (loopBit …) G t hn (Rq_pos_of_bracket …) …`. -/

/-- **Brick 4's conclusion at the campaign's family**: `RunParts o G t (paramsKbc2 G)` from the
program's per-round stream data, with `0 < rmax`, `rmax ≤ 1` and the ok-branch rounding budget no
longer hypotheses (they are `paramsKbc2_side_conditions`, given `2 ≤ G.n` and `0 < Rq G`). -/
noncomputable def runParts_paramsKbc2_of_stream_data
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
(ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (mu delta : ℕ → ℝ) (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G)
              hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne)
      j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne)
      j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m))    :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  QMCLeafB.RunPartsStream.runParts_of_stream_data o G t
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (paramsKbc2_side_conditions G hn hRq).1
    (paramsKbc2_side_conditions G hn hRq).2.1
    (paramsKbc2_side_conditions G hn hRq).2.2.2
    ok marg cX lam c cn mu delta dvec hdvec C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2
    hdiagc qSurr hqSurr hmu_up hmu_lo hlam3 hstatec hstated hverdict

#print axioms QMCLeafB.NonVacuity.runParts_paramsKbc2_of_stream_data

/-! ## 4.  `hstated` is forced, not free: the direction-side state budget is a trace inequality

`hstated` reads `dvec ⬝ᵥ (qSurr k − flat (castMat (cX k))) ≤ 0` at `dvec = flat ones`.  `qSurr` is
**not** a free parameter of the stream conduit: `hqSurr` pins it to the accumulated surrogate
`∑_{j<k} μ_j • p_j`.  Consequently the hypothesis is *equivalent* to

    ∑_{j<k} μ_j · (flat ones ⬝ᵥ p_j)  ≤  ∑_i (cX k) i i ,

a genuine budget against the program state's trace — not an artefact of the state mismatch, and not
removable by "taking `qSurr := flat ∘ cX`" as `Check_runparts_stream_m4`'s §5 docstring suggests:
that choice is not available, since `hqSurr` would then *force* `∑_{j<k} μ_j • p_j = flat (cX k)`
(`surrogate_pinned` below).

Two consequences for the slot owners:

* `stated_of_trace` — a bound on the surrogate trace alone yields `hstated`;
* `trace_le_of_diagc` — `hdiagc` bounds the right-hand side by `n·(1 − dq/4)`, so `hstated` follows
  from `∑_{j<k} μ_j (flat ones ⬝ᵥ p_j) ≤ n (1 − dq/4)`: this is where the surplus of the diagonal
  cap is spent, which is the one place in the residual set where the two slots couple.
  Sign of the traffic, for whoever closes it: `hlam3` forces `flat ones ⬝ᵥ p_j ≥ 0` and `hmu_up`
  gives `μ_j ≥ λ_j`.  With `p_j = A_j⁻¹(c_j + λ_j·flat ones)` (`witAt` at the recorded normal
  `cn j = c_j + λ_j·flat ones`) the summand is `μ_j·(d ⬝ A_j⁻¹c_j) + μ_j·λ_j·(d ⬝ A_j⁻¹d)`, and
  `d ⬝ A_j⁻¹d > 0` (`RunPartsStream.dir_wit_pos`), so its `λ`-part is at least
  `λ_j²·(d ⬝ A_j⁻¹d)`: the left-hand side grows **quadratically** in the dilation parameters, while
  `hlam2`/`hlam3` only ask for `λ` to be bounded *below*.  `hstated` is the one slot in the residual
  set where a large `λ` *costs* rather than buys, and §4.3 is the form in which to spend the cap. -/

/-- **The pairing of `flat ones` with a finite sum of scalar multiples.** -/
theorem dot_sum_smul {N : ℕ} (v : Fin N → ℝ) (s : Finset ℕ) (mu : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ) :
    v ⬝ᵥ (∑ j ∈ s, mu j • p j) = ∑ j ∈ s, mu j * (v ⬝ᵥ p j) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- **`flat ones ⬝ᵥ flat (castMat X)` is the trace of `X`.**  (The row-major flattening is a
reindexing, so the same symbol computes the identity pairing here as in `frob_one_eq_trace`.) -/
theorem dot_flat_one {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) :
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)
      = ∑ i, ((X i i : ℚ) : ℝ) := by
  have hL : ∀ i, QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X) i
      = ((QMCLeafB.RelaxOracle.flatQ X i : ℚ) : ℝ) := fun i => rfl
  have hstep : (∑ i : Fin (n * n),
        ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ)
          * ((QMCLeafB.RelaxOracle.flatQ X i : ℚ) : ℝ))
      = ∑ p : Fin n × Fin n,
          (((1 : Matrix (Fin n) (Fin n) ℚ) p.1 p.2 : ℚ) : ℝ) * ((X p.1 p.2 : ℚ) : ℝ) := by
    rw [← Equiv.sum_comp (finProdFinEquiv (m := n) (n := n)).symm
      (g := fun p : Fin n × Fin n =>
        (((1 : Matrix (Fin n) (Fin n) ℚ) p.1 p.2 : ℚ) : ℝ) * ((X p.1 p.2 : ℚ) : ℝ))]
    rfl
  have hdiag : ∀ i : Fin n,
      (∑ j : Fin n, (((1 : Matrix (Fin n) (Fin n) ℚ) i j : ℚ) : ℝ) * ((X i j : ℚ) : ℝ))
        = ((X i i : ℚ) : ℝ) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Matrix.one_apply_ne (Ne.symm hj)]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [dotProduct, hL]
  rw [hstep, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hdiag i

/-- **The surrogate is pinned by `hqSurr`**: the "free choice `qSurr = flat ∘ cX`" is not a choice —
it is the equation `∑_{j<k} μ_j • p_j = flat (cX k)`. -/
theorem surrogate_pinned
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (mu : ℕ → ℝ) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
    (hfree : ∀ k, qSurr k = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
    (k : ℕ) :
    (∑ j ∈ Finset.range k, mu j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)) := by
  rw [← hqSurr k, hfree k]

/-- **`hstated`, reduced to the trace budget on the accumulated surrogate.** -/
theorem stated_reduction
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (mu : ℕ → ℝ) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
    (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (k : ℕ) :
    dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      = ∑ j ∈ Finset.range k, mu j *
          (dvec ⬝ᵥ QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
        - ∑ i, ((cX k i i : ℚ) : ℝ) := by
  have h1 : dvec ⬝ᵥ qSurr k
      = ∑ j ∈ Finset.range k, mu j *
          (dvec ⬝ᵥ QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j) := by
    rw [hqSurr k]
    exact dot_sum_smul dvec (Finset.range k) mu _
  have h2 : dvec ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
      = ∑ i, ((cX k i i : ℚ) : ℝ) := by
    rw [hdvec]
    exact dot_flat_one (cX k)
  have hsub : dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      = dvec ⬝ᵥ qSurr k
        - dvec ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)) := by
    simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hsub, h1, h2]

/-- **A surrogate-trace bound gives `hstated`** — the usable form of the reduction. -/
theorem stated_of_trace
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (mu : ℕ → ℝ) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
    (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (k : ℕ)
    (htrace : ∑ j ∈ Finset.range k, mu j *
        (dvec ⬝ᵥ QMCLeafB.EngineIterates.cutPR
          (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
      ≤ ∑ i, ((cX k i i : ℚ) : ℝ)) :
    dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0 := by
  rw [stated_reduction G hn lam c cn hcne mu cX qSurr hqSurr dvec hdvec k]
  linarith

/-- **`hstated` is *equivalent* to the trace budget** — the reduction read in the direction the slot
owners need (the hypothesis holds iff the surrogate trace fits under the state trace). -/
theorem stated_iff_trace
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (mu : ℕ → ℝ) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
    (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (k : ℕ) :
    (dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
      ↔ (∑ j ∈ Finset.range k, mu j *
          (dvec ⬝ᵥ QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
        ≤ ∑ i, ((cX k i i : ℚ) : ℝ)) := by
  rw [stated_reduction G hn lam c cn hcne mu cX qSurr hqSurr dvec hdvec k]
  constructor <;> intro h <;> linarith

#print axioms QMCLeafB.NonVacuity.stated_iff_trace

/-- **`hdiagc` caps the state trace at `n·(1 − dq/4)`** — the right-hand side of `hstated`'s trace
budget, i.e. exactly how much surrogate trace the diagonal cap affords. -/
theorem trace_le_of_diagc (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (k : ℕ) :
    ∑ i, ((cX k i i : ℚ) : ℝ)
      ≤ (G.n : ℝ) * (1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4) := by
  have h : ∀ i : Fin G.n, ((cX k i i : ℚ) : ℝ)
      ≤ 1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4 := by
    intro i
    have h2 : (((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4 : ℚ)) : ℝ)
        = 1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4 := by
      push_cast
      ring
    calc ((cX k i i : ℚ) : ℝ)
        ≤ ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4 : ℚ) : ℝ) := by
          exact_mod_cast hdiagc k i
      _ = 1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4 := h2
  calc ∑ i, ((cX k i i : ℚ) : ℝ)
      ≤ ∑ _i : Fin G.n, (1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4) :=
        Finset.sum_le_sum fun i _ => h i
    _ = (G.n : ℝ) * (1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

#print axioms QMCLeafB.NonVacuity.dot_sum_smul
#print axioms QMCLeafB.NonVacuity.dot_flat_one
#print axioms QMCLeafB.NonVacuity.surrogate_pinned
#print axioms QMCLeafB.NonVacuity.stated_reduction
#print axioms QMCLeafB.NonVacuity.stated_of_trace
#print axioms QMCLeafB.NonVacuity.trace_le_of_diagc

/-! ## 5.  The residual as one object: `StreamData`

The lock `solution_of_hd` needs `hd : ∀ G t, 2 ≤ G.n → -Rq G ≤ t → (t : ℝ) < -(Rq G/40000) →
RunParts (loopBit …) G t (paramsKbc2 G)`.  §3 already produces the `RunParts`, so the whole content of
`hd` is the family of per-(G,t) stream records.  `StreamData` names that family in one place: its
fields are *verbatim* the hypotheses of `runParts_paramsKbc2_of_stream_data`, and `hd_of_streams`
turns any such family into the `hd` of the lock, with the guard's `0 < Rq G` supplied by §1.  So the
open content of the leaf is exactly `StreamData o G t hn` for every interior `(G, t)` at
`o := loopBit init round verdict (fun G' _ => Kbc2 (mHalve (G'.n*G'.n)) G' * mHalve (G'.n*G'.n))`.
-/

structure StreamData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) where
  ok : ℕ → Bool
  marg : ℕ → ℚ
  cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  lam : ℕ → ℚ
  c : ℕ → Fin (G.n * G.n) → ℚ
  cn : ℕ → Fin (G.n * G.n) → ℚ
  mu : ℕ → ℝ
  delta : ℕ → ℝ
  dvec : Fin (G.n * G.n) → ℝ
  hdvec : dvec = fun i =>
    ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ)
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
    (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq)
  hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin
  hmem : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
    * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
    (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq)
  hCsym : ∀ k, (cX k)ᵀ = cX k
  hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, ok k = false → 1 ≤ lam k
  hlam2 : ∀ k, ok k = false →
    |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
    + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
    QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    cn hcne (c k) k|
    + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c k) k|
    + 9 * marg k ^ 2
    / (4 * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
    QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4
  qSurr : ℕ → Fin (G.n * G.n) → ℝ
  hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
    QMCLeafB.EngineIterates.cutPR
    (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G)
    hn cn hcne) j
  hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
    (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne)
    j ≤ mu j
  hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
    (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne)
    j
  hlam3 : ∀ j,
    |(fun i => (((QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
    ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c j) j i : ℚ) : ℝ))|
    ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
    ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne
    (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)))
  hstatec : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
    ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
    + ∑ j ∈ Finset.range k, delta j * max 0
    (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
    (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j))
    ≤ ((marg k : ℚ) : ℝ) / 2
  hstated : ∀ k, ok k = false →
    dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
    ((QMCLeafB.UnionShallow.paramsKbc2 G).K
    * (QMCLeafB.UnionShallow.paramsKbc2 G).m)

/-- **The conduit, as a function of one record bundle.** -/
noncomputable def StreamData.toRunParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (S : StreamData o G t hn) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  runParts_paramsKbc2_of_stream_data o G t hn hRq S.ok S.marg S.cX S.lam S.c S.cn S.mu S.delta
    S.dvec S.hdvec S.C S.hmarg S.hmem S.hCsym S.hcEq S.hcn S.hcne S.hlam0 S.hlam1 S.hlam2
    S.hdiagc S.qSurr S.hqSurr S.hmu_up S.hmu_lo S.hlam3 S.hstatec S.hstated S.hverdict

/-- **`hd` of the lock, from a stream-record family.**  The statement is *verbatim* the `hd`
hypothesis of `QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round` /
`Check_htop_solution_lock_m7.solution_of_hd` at `o = loopBit …`, so the closing is one application. -/
noncomputable def hd_of_streams
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (S : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → StreamData o G t hn) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  fun G t hn hlo hhi => (S G t hn hlo hhi).toRunParts (Rq_pos_of_bracket G t hlo hhi)

#print axioms QMCLeafB.NonVacuity.StreamData.toRunParts
#print axioms QMCLeafB.NonVacuity.hd_of_streams

/-! ## 6.  The leaf from a stream-record family alone

`ConformanceM8.solution_final` already concludes the verbatim `d9f601e5` sentence from `hd` at
`InitDq.init0` and `paramsKbc2`.  Composing it with §5 closes the leaf's *interface*: every remaining
obligation of the campaign is now a `StreamData` family at that one `o` — nothing else.  The
statement below is the exact d9f601e5 type, so the shape of the open work is a single name.

This is a boundary-condition statement, not a discharge: the `StreamData` family is a hypothesis, and
the file proves nothing about its existence.  It is the sharpest form in which the residual can be
handed to the slot owners (d1: `hdiagc`/`hstatec`/positivity; d3: `C`/`hmarg`/`hmem`/`hCsym`/`hcEq`;
d5: `hmu_*`/`hpos`; and `hstated` in the trace form of §4). -/

/-- **The leaf from one `StreamData` family** — the verbatim `d9f601e5` sentence. -/
theorem solution_of_stream_data_family (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (S : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      StreamData
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t hn) :
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
  QMCLeafB.ConformanceM8.solution_final k hk (hd_of_streams _ S)

#print axioms QMCLeafB.NonVacuity.solution_of_stream_data_family

/-- **Statement lock.**  §6's conclusion *is* `QMCLeafB.FinishLine.SolutionStatement` (the `exact`
is a definitional check, not a rewrite), so a `StreamData` family is a complete supply for the leaf's
last node. -/
theorem solutionStatement_of_stream_data_family (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (S : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      StreamData
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t hn) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_stream_data_family k hk S

#print axioms QMCLeafB.NonVacuity.solutionStatement_of_stream_data_family

/-! ## 7.  The drift slot is removable: the exact-surrogate conduit

`mu`/`delta` are **proof data** of the `RunParts` interface (`ℕ → ℝ`), not records of the program: no
`Poly` requirement touches them, and `drift_bound_upper` only asks `mu j - delta j ≤ CentreTrack.lam
… j ≤ mu j`.  So one may take `mu := CentreTrack.lam …` and `delta := 0` *exactly*, i.e. the
surrogate is the engine's own centre (`CentreTrack.Cat_eq_sum`: `Cat k = ∑_{j<k} λ_j • p_j`, with
`λ_j = γ_j/√σ_j` the engine increment).  Two consequences at the §5 interface:

* the charging sum `∑_j δ_j · max 0 (−(c_k ⬝ p_j))` in `hstatec` **vanishes identically** (`δ = 0`),
  and `hdriftc`/`hdriftd` lose their drift terms, because `Cat k − qSurr k = 0` — the bracket choice
  (`invSqrtGe` vs `invSqrtLe`, m4's f57) does not arise at all in this formulation;
* `hmu_up`/`hmu_lo` become `le_rfl`/`simp`, so `Check_runparts_stream_m4` §6's `muUp`/`deltaUp`
  dyadic apparatus is not needed to *discharge* them (it is needed only if one insists on dyadic
  *values*, which the interface does not).

What survives is exactly the **state mismatch at the exact engine centre**:

    hstatec : c_k ⬝ (Cat k − flat (cX k)) ≤ marg_k/2
    hstated : flat ones ⬝ (Cat k − flat (cX k)) ≤ 0

— the two conditions d1/d5 must prove, in their sharpest form (no surrogate slack to spend).  By §4,
`hstated` is *equivalent* to `flat ones ⬝ Cat k ≤ tr (cX k)` under `hqSurr`, so the trace budget of §4
is the same obligation in different clothes. -/

/-- **The drift is identically zero at the exact surrogate.** -/
theorem exact_surrogate_drift (N : ℕ)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (k : ℕ) :
    QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
        - ∑ j ∈ Finset.range k, QMCLeafB.CentreTrack.lam N cd j •
            QMCLeafB.EngineIterates.cutPR cd j = 0 := by
  rw [QMCLeafB.CentreTrack.Cat_eq_sum]
  exact sub_self _

/-- **The conduit at `paramsKbc2` with the exact surrogate**: the residual's state-side content, with
no `mu`/`delta` and no charging sum. -/
noncomputable def runParts_paramsKbc2_of_exact_surrogate
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
      + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
      QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      cn hcne (c k) k|
      + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c k) k|
      + 9 * marg k ^ 2
      / (4 * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
      QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
      ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c j) j i : ℚ) : ℝ))|
      ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
      ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne
      (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) k
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  refine runParts_paramsKbc2_of_stream_data o G t hn hRq ok marg cX lam c cn
    (fun j => QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)
    (fun _ => 0) dvec hdvec C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 hdiagc
    (fun k => QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) k)
    (fun k => QMCLeafB.CentreTrack.Cat_eq_sum (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) k)
    (fun j => le_rfl) (fun j => by simp) hlam3 ?_ hstated hverdict
  intro k hok
  have hzero : ∀ j ∈ Finset.range k, (0 : ℝ) * max 0
      (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j)) = 0 := by
    intro j _; ring
  rw [Finset.sum_eq_zero hzero, add_zero]
  exact hstatec k hok

#print axioms QMCLeafB.NonVacuity.exact_surrogate_drift
#print axioms QMCLeafB.NonVacuity.runParts_paramsKbc2_of_exact_surrogate

/-! ## 8.  Five of the residual's slots are definitional choices, not obligations

m4's residual list (`Check_runparts_stream_m4` §5) names `hmarg`, `hcEq`, `hcn`, `hqSurr`,
`hmu_up`/`hmu_lo` as hypotheses.  They are *not* analytic content: every one of them is satisfiable
by a definition, because the objects they constrain (`marg`, `c`, `cn`, `mu`, `delta`, `qSurr`) are
parameters of the stream bundle, not records of the program.  The three lemmas below are that
statement, machine-checked (they are the only choices available, so nothing is lost):

* `marg k := (C k _).margin` reads the oracle's own margin — `hmarg` holds by `dif_pos`;
* `c k := flatQ (C k _).normal` is the oracle's own violated direction, and `cn k := c k + λ k • flat
  ones` is the recorded normal — `hcEq`/`hcn` hold by construction (this is *why* the pair
  `(c, cn)` is in the interface: the normal is `c` shifted by the dilation);
* `mu := CentreTrack.lam …`, `delta := 0` — §7;
* `qSurr := Cat …` — §7.

So the residual of `hd` at `paramsKbc2` is, after this file: the oracle records `C`/`hmem`/`hCsym`,
the dilation side `hlam0`–`hlam3`/`hcne`, the verdict read-out `hverdict`, and the three *analytic*
conditions `hdiagc`, `hstatec`, `hstated` at the exact engine centre.  Nothing else. -/

/-- **`marg` is read off the oracle.** -/
theorem exists_marg {N : ℕ} (ok : ℕ → Bool)
    (F : ∀ k, ok k = false → ℚ) :
    ∃ marg : ℕ → ℚ, ∀ k (hok : ok k = false), marg k = F k hok :=
  ⟨fun k => if h : ok k = false then F k h else 0, fun k hok => by simp only [dif_pos hok]⟩

/-- **`(c, cn)` are the oracle's violated direction and its dilation shift.** -/
theorem exists_c_cn {N : ℕ} (ok : ℕ → Bool)
    (F : ∀ k, ok k = false → Fin N → ℚ) (lam : ℕ → ℚ) (v : Fin N → ℚ) :
    ∃ (c cn : ℕ → Fin N → ℚ),
      (∀ k (hok : ok k = false), c k = F k hok)
      ∧ (∀ k, cn k = c k + lam k • v) := by
  refine ⟨fun k => if h : ok k = false then F k h else 0,
    fun k => (if h : ok k = false then F k h else 0) + lam k • v, ?_, fun k => rfl⟩
  intro k hok
  simp only [dif_pos hok]

/-- **The exact surrogate is admissible**: `mu := CentreTrack.lam`, `delta := 0` meet both interval
conditions of `drift_bound_upper`. -/
theorem exists_mu_delta {N : ℕ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData N) :
    ∃ (mu delta : ℕ → ℝ),
      (∀ j, QMCLeafB.CentreTrack.lam N cd j ≤ mu j)
      ∧ (∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam N cd j) :=
  ⟨fun j => QMCLeafB.CentreTrack.lam N cd j, fun _ => 0, fun j => le_rfl, fun j => by simp⟩

/-- **`qSurr` is the engine's centre** (`CentreTrack.Cat_eq_sum`). -/
theorem exists_qSurr {N : ℕ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData N) :
    ∃ qSurr : ℕ → Fin N → ℝ,
      ∀ k, qSurr k = ∑ j ∈ Finset.range k, QMCLeafB.CentreTrack.lam N cd j •
        QMCLeafB.EngineIterates.cutPR cd j :=
  ⟨fun k => QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k,
    fun k => QMCLeafB.CentreTrack.Cat_eq_sum N cd k⟩

#print axioms QMCLeafB.NonVacuity.exists_marg
#print axioms QMCLeafB.NonVacuity.exists_c_cn
#print axioms QMCLeafB.NonVacuity.exists_mu_delta
#print axioms QMCLeafB.NonVacuity.exists_qSurr

#print axioms QMCLeafB.NonVacuity.Rq_pos_of_bracket
#print axioms QMCLeafB.NonVacuity.bracket_inhabited_of_Rq_pos
#print axioms QMCLeafB.NonVacuity.bracket_inhabited_iff
#print axioms QMCLeafB.NonVacuity.Rq_pos_of_weight_pos
#print axioms QMCLeafB.NonVacuity.bracket_empty_of_Rq_nonpos
#print axioms QMCLeafB.NonVacuity.paramsKbc2_eq_paramsShallowKf
#print axioms QMCLeafB.NonVacuity.paramsShallowKf_eq_paramsK
#print axioms QMCLeafB.NonVacuity.paramsKbc2_fields
#print axioms QMCLeafB.NonVacuity.paramsKbc2_dq_pos
#print axioms QMCLeafB.NonVacuity.paramsKbc2_side_conditions

/-! ## 9.  Cone record for the shelf strokes this audit leans on

Printed here so that the coordinator's mirror can quote one file: every stroke of the endgame chain
that this audit consumes has the standard cone. -/

#print axioms QMCLeafB.ConformanceM8.solution_final
#print axioms QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round
#print axioms QMCLeafB.RunPartsStream.runParts_shallow_dyadic
#print axioms QMCLeafB.UnionShallow.solution_union_shallow
#print axioms QMCLeafB.InitDq.poly_init0
#print axioms QMCLeafB.InitDq.init_normalised
#print axioms QMCLeafB.InitDq.fvR_init0
#print axioms QMCLeafB.InitDq.stT_init0
#print axioms QMCLeafB.InitDq.init0_tape

end QMCLeafB.NonVacuity


