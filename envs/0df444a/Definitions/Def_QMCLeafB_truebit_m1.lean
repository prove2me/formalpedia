-- Prove2me | Definitions.Def_QMCLeafB_truebit_m1
-- name    : QMCLeafB_truebit_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:11:51.90546+00:00
-- url     : https://prove2.me/theorems/41ec3960-227e-4204-b4c9-7c801784ca23
-- title:
--   QMCLeafB truebit_m1
-- statement:
--   # m1 — the TRUE-BIT stratum of `ResidParts` is free
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_parts_m2
/-
# m1 — the TRUE-BIT stratum of `ResidParts` is free

`FinalStroke.RunParts` records `ok cd del` as **data** and constrains them only through
`hverdict : o G t = anyOk ok (K·m)`; every geometric field (`hwit hrho hcne hdel0 hcheck hle hcut`)
is conditioned on `ok k = false`.  So at an interior point whose bit is **true** one may record the
all-`ok` stream: no round is a cut round, all eight geometric slots become vacuous, and the only
surviving obligation is `hcert` — one unit-diagonal PSD real point with
`tr (wMatrix G · X) ≤ t + Rq/40000`, the *same* witness at every round (it does not depend on `k`).

Consequences (both machine-checked here):

* `runParts_of_trueBit` — `RunParts o G t P` from `o G t = true`, `0 < K·m`, and one primal point.
  No engine facts, no cut data, no depth ledger, no dilation;
* `residParts_of_falseStratum` — the accepted residual `PartsM2.ResidParts` follows from
  **(i)** `RunParts` on the bit-`false` stratum (the sliver class, unchanged) and
  **(ii)** one primal point at each bit-`true` interior point.

So the residual's true-bit half carries no content beyond a feasible point.  Ingredient (ii) is
supplied by banked work: `QMCLeafB.RundataCert.hcert_of_relaxMem` (Check_brick_hd_cert_m5) turns
the campaign's ok-round `RelaxMem` into exactly that witness, and `OkProdM6.anyOk_const_true` is the
verdict computation reproduced below.  NOTE the mismatch to watch when wiring (ii): that brick is
stated at `RundataCert.dq G = eps G/(9·cAq G + 1)`, while `paramsKbc2.dq = dqShallow G`, which
differs from it only at `Rq G = 0` (the `dqShallow` fallback to `1`), so the wiring needs
`Rq G ≠ 0`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TrueBitM1

open QuantumMaxCutEnergy

/-! ## 1.  The verdict of the all-`ok` stream -/

/-- `anyOk` of the all-`true` stream at a positive count (`OkProdM6.anyOk_const_true`, reproved
here so this module depends only on the residual's own interface). -/
theorem anyOk_true_stream : ∀ N : ℕ, 0 < N →
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) N = true
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | (k + 1), _ => by
      rw [QMCLeafB.SimLoop.anyOk_succ]
      simp

/-! ## 2.  `RunParts` at a true bit, from one primal point -/

/-- **THE TRUE-BIT PRODUCTION.**  With the bit true, record the all-`ok` stream: the eight cut-slot
fields are vacuous, and `hcert` is the single supplied primal point. -/
def runParts_of_trueBit {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : FinalStroke.RunParams G}
    (hbit : o G t = true) (hKm : 0 < P.K * P.m)
    (hcert : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      AnswerProducer.IsUnitDiagPSD X ∧
        (wMatrix G * X).trace
          ≤ (t : ℝ) + ((((EngineRuntime.Rq G / 40000 : ℚ)) : ℚ) : ℝ)) :
    FinalStroke.RunParts o G t P where
  ok := fun _ => true
  cd := fun _ => ⟨0, 0, 0⟩
  del := fun _ => 0
  hcert := fun _ _ _ => hcert
  hwit := by intro k _ h; exact absurd h (by simp)
  hrho := by intro k _ h; exact absurd h (by simp)
  hcne := by intro k _ h; exact absurd h (by simp)
  hdel0 := by intro k _ h; exact absurd h (by simp)
  hcheck := by intro k _ h; exact absurd h (by simp)
  hle := by intro k _ h; exact absurd h (by simp)
  hcut := by intro k _ h; exact absurd h (by simp)
  hverdict := by rw [hbit, anyOk_true_stream _ hKm]

/-! ## 3.  The residual reduces to its bit-`false` stratum -/

/-- **`ResidParts` needs only the bit-`false` stratum.**  Bit-`true` interior points are discharged
by `runParts_of_trueBit`; the surviving obligation is the bit-`false` stratum (the sliver class),
where the cut contract is genuine. -/
def residParts_of_falseStratum {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G}
    (hpos : ∀ G : QuantumMaxCutEnergy.Input, 0 < (Pfam G).K * (Pfam G).m)
    (htrue : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      o G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        AnswerProducer.IsUnitDiagPSD X ∧
          (wMatrix G * X).trace
            ≤ (t : ℝ) + ((((EngineRuntime.Rq G / 40000 : ℚ)) : ℚ) : ℝ))
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      o G t = false → FinalStroke.RunParts o G t (Pfam G)) :
    PartsM2.ResidParts o Pfam := by
  intro G t hn hlo hhi hbody
  by_cases h : o G t = true
  · exact runParts_of_trueBit h (hpos G) (htrue G t hn h)
  · have hf : o G t = false := by
      cases hb : o G t
      · rfl
      · exact absurd hb h
    exact hfalse G t hn hf


/-! ## 4.  The campaign stroke with the true-bit stratum deleted -/

/-- **`AssemblyM5.HdProp` from a bit-`false`-only residual.**  `PartsM2.hdProp_of_campaign_parts`
with the accepted residual `ResidParts` replaced by

`hsliver : 2 ≤ G.n → campaignBit G t = false → RunParts campaignBit G t (paramsKbc2 G)`,

the bit-`false` stratum alone (the sliver class; the empty-body points inside it are already handled
by `RefutedM3.runParts_of_emptyBody` inside `hdProp_of_parts`).  The bit-`true` stratum is deleted by
`runParts_of_trueBit`.  `hpos` is `UnionShallow.one_le_Kbc2_mul` at `paramsKbc2`; `htrue` is the
campaign's ok-round `RelaxMem` routed through `RundataCert.hcert_of_relaxMem`. -/
def hdProp_of_campaign_sliver (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ →
      Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      Audit2M5.campaignBit G t = SimLoop.anyOk (rb G t)
        ((UnionShallow.paramsKbc2 G).K * (UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      RelaxOracle.RelaxMem (Finalization.wMatrixQ G) (cXp G t k)
        (t - RundataCert.eps G) (UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ BallFloor.relaxBodyLE (wMatrix G)
          ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ RelaxOracle.RelaxMem (Finalization.wMatrixQ G) Q
          (t - RundataCert.eps G) (UnionShallow.paramsKbc2 G).dq)
    (hpos : ∀ G : QuantumMaxCutEnergy.Input,
      0 < (UnionShallow.paramsKbc2 G).K * (UnionShallow.paramsKbc2 G).m)
    (htrue : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      Audit2M5.campaignBit G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        AnswerProducer.IsUnitDiagPSD X ∧
          (wMatrix G * X).trace
            ≤ (t : ℝ) + ((((EngineRuntime.Rq G / 40000 : ℚ)) : ℚ) : ℝ))
    (hsliver : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      Audit2M5.campaignBit G t = false →
      FinalStroke.RunParts Audit2M5.campaignBit G t (UnionShallow.paramsKbc2 G)) :
    AssemblyM5.HdProp :=
  PartsM2.hdProp_of_campaign_parts rb cXp hbit hok hemptyR
    (residParts_of_falseStratum hpos htrue hsliver)

#print axioms QMCLeafB.TrueBitM1.hdProp_of_campaign_sliver


/-- `K·m > 0` at the campaign parameters (banked `UnionShallow.one_le_Kbc2_mul`). -/
theorem campaign_K_pos (G : QuantumMaxCutEnergy.Input) :
    0 < (UnionShallow.paramsKbc2 G).K * (UnionShallow.paramsKbc2 G).m :=
  lt_of_lt_of_le Nat.zero_lt_one (UnionShallow.one_le_Kbc2_mul G)

#print axioms QMCLeafB.TrueBitM1.campaign_K_pos

/-- `hdProp_of_campaign_sliver` with `hpos` discharged. -/
def hdProp_of_campaign_sliver' (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ →
      Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      Audit2M5.campaignBit G t = SimLoop.anyOk (rb G t)
        ((UnionShallow.paramsKbc2 G).K * (UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      RelaxOracle.RelaxMem (Finalization.wMatrixQ G) (cXp G t k)
        (t - RundataCert.eps G) (UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ BallFloor.relaxBodyLE (wMatrix G)
          ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ RelaxOracle.RelaxMem (Finalization.wMatrixQ G) Q
          (t - RundataCert.eps G) (UnionShallow.paramsKbc2 G).dq)
    (htrue : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      Audit2M5.campaignBit G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        AnswerProducer.IsUnitDiagPSD X ∧
          (wMatrix G * X).trace
            ≤ (t : ℝ) + ((((EngineRuntime.Rq G / 40000 : ℚ)) : ℚ) : ℝ))
    (hsliver : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      Audit2M5.campaignBit G t = false →
      FinalStroke.RunParts Audit2M5.campaignBit G t (UnionShallow.paramsKbc2 G)) :
    AssemblyM5.HdProp :=
  hdProp_of_campaign_sliver rb cXp hbit hok hemptyR campaign_K_pos htrue hsliver

#print axioms QMCLeafB.TrueBitM1.hdProp_of_campaign_sliver'


/-! ## 5.  No `RunParts` anywhere: the leaf from "nonempty body => bit true" -/

/-- **`ResidParts` with the `RunParts` demand gone.**  If every interior point with a nonempty relaxed
body reads bit `true`, then `ResidParts` follows from `hpos` and the primal points at bit-`true`
points alone: the bit-`false` stratum carries no nonempty body, so it is vacuous. -/
def residParts_of_nonempty_true {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G}
    (hpos : ∀ G : QuantumMaxCutEnergy.Input, 0 < (Pfam G).K * (Pfam G).m)
    (htrue : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        AnswerProducer.IsUnitDiagPSD X ∧
          (wMatrix G * X).trace
            ≤ (t : ℝ) + ((((EngineRuntime.Rq G / 40000 : ℚ)) : ℚ) : ℝ))
    (hvisible : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        BallFloor.relaxBodyLE (wMatrix G)
          ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((Pfam G).dq : ℚ) : ℝ) X) → o G t = true) :
    PartsM2.ResidParts o Pfam := by
  intro G t hn _hlo _hhi hbody
  exact runParts_of_trueBit (hvisible G t hn hbody) (hpos G) (htrue G t hn (hvisible G t hn hbody))

#print axioms QMCLeafB.TrueBitM1.residParts_of_nonempty_true

/-- **THE LEAF WITH NO `RunParts` SLOT.**  `AssemblyM5.HdProp` from the campaign's read-out data,
the primal point at bit-`true` points, and ONE design property of the round program:
`hvisible : 2 ≤ G.n → (∃ body member) → campaignBit G t = true`.  `K·m > 0` is discharged by
`campaign_K_pos`.  The empty-body points of the bit-`false` side are handled inside
`PartsM2.hdProp_of_parts` by `RefutedM3.runParts_of_emptyBody`; the nonempty bit-`false` side is
killed by `hvisible`. -/
def hdProp_of_campaign_closed (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ →
      Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      Audit2M5.campaignBit G t = SimLoop.anyOk (rb G t)
        ((UnionShallow.paramsKbc2 G).K * (UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      RelaxOracle.RelaxMem (Finalization.wMatrixQ G) (cXp G t k)
        (t - RundataCert.eps G) (UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ BallFloor.relaxBodyLE (wMatrix G)
          ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ RelaxOracle.RelaxMem (Finalization.wMatrixQ G) Q
          (t - RundataCert.eps G) (UnionShallow.paramsKbc2 G).dq)
    (htrue : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      Audit2M5.campaignBit G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        AnswerProducer.IsUnitDiagPSD X ∧
          (wMatrix G * X).trace
            ≤ (t : ℝ) + ((((EngineRuntime.Rq G / 40000 : ℚ)) : ℚ) : ℝ))
    (hvisible : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        BallFloor.relaxBodyLE (wMatrix G)
          ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      Audit2M5.campaignBit G t = true) :
    AssemblyM5.HdProp :=
  PartsM2.hdProp_of_campaign_parts rb cXp hbit hok hemptyR
    (residParts_of_nonempty_true (Pfam := UnionShallow.paramsKbc2) campaign_K_pos
      htrue hvisible)

#print axioms QMCLeafB.TrueBitM1.hdProp_of_campaign_closed

#print axioms QMCLeafB.TrueBitM1.anyOk_true_stream
#print axioms QMCLeafB.TrueBitM1.runParts_of_trueBit
#print axioms QMCLeafB.TrueBitM1.residParts_of_falseStratum

end QMCLeafB.TrueBitM1


