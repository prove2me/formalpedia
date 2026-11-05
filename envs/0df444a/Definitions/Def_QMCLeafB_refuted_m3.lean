-- Prove2me | Definitions.Def_QMCLeafB_refuted_m3
-- name    : QMCLeafB_refuted_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:13:44.550145+00:00
-- url     : https://prove2.me/theorems/09879727-0ef7-4c17-8c0c-8b0c5cb4d013
-- title:
--   QMCLeafB refuted_m3
-- statement:
--   `Check_refuted_m3` — phase 21, member m3, direction `d6` (`anchors-and-audit`):
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_runparts_m5
import Definitions.Def_QMCLeafB_record_m2
/-
  `Check_refuted_m3` — phase 21, member m3, direction `d6` (`anchors-and-audit`):
  **the refuted-point anchor, at the analytic boundary.**

  Phase 20's residual `CoreDataF` is uninhabitable at an interior point whose relaxed body is empty
  (d1's machine-checked refutation: `hcutfin` demands a member beyond the horizon).  This module
  shows that the refutation does **not** propagate to the shape the leaf is actually closed with.
  At an empty body the *analytic* shape `RunParts` — hence `RunData`, hence
  `VerdictSound.solution_of_loop_via_runData` — is inhabited by the all-`cut` stream with zero
  recorded margins:

  * `hcert` is vacuous (no `ok` round);
  * `hwit` is `runCut`'s own witness relation `Aat k *ᵥ p k = c k`, for *any* nonzero rational
    normal stream (no geometry at all);
  * `hcheck` is `σ = c ⬝ p > 0`, from the engine's positivity of the iterates;
  * `hdel0` is `0 ≤ 0`, `hle` is `rmax ≤ rmax`, `hrho` is `RunParams.hrmax`, `hcne` is the
    nonzero normal;
  * `hcut` is *vacuous*: the ball it must separate is empty, since the relaxed body is;
  * `hverdict` is the bit equation at the all-`false` stream
    (`RecordM2.anyOk_false_stream`).

  So no cut budget, no dilation multiplier, no pinch and no drift appears on the empty side: the
  whole lamstream/pinch machinery is confined to *nonempty* bodies.  §3 instantiates the anchor at
  d1's point `(G₀, −99999/100000)`, where the body emptiness is the two-test-vector estimate
  `⟪A,X⟫ ≥ −(1 + 3δ/4) > u + δ/2` of `Check_emptybody_m5`, redone over ℝ (the ball is a set of real
  matrices; `RelaxMem` is rational).

  Discipline: `set_option autoImplicit false`, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
  `#print axioms` on every declaration.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RefutedM3

open QuantumMaxCutEnergy

/-! ## 1.  An empty body empties the ball

`Boundary.relaxBall A u δ M` is the relaxed body, flattened, cut down by the norm bound.  So an
empty body makes every separation contract vacuous. -/

/-- No point of the ball lies in an empty relaxed body. -/
theorem not_relaxBall_of_emptyBody {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ M : ℝ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ, ¬ QMCLeafB.BallFloor.relaxBodyLE A u δ X)
    (z : Fin (n * n) → ℝ) : z ∉ QMCLeafB.Boundary.relaxBall A u δ M :=
  fun hz => hempty _ hz.1

#print axioms QMCLeafB.RefutedM3.not_relaxBall_of_emptyBody

/-! ## 2.  The all-`cut` run at an empty body

The recorded stream is `runCut` at the constant nonzero normal `e₀`, the margins are `0`, and the
depth ceiling is `RunParams.rmax`.  Every slot of `RunParts` is then immediate. -/

/-- The constant normal stream `e₀` used by the anchor. -/
def e₀ (N : ℕ) [NeZero N] : Fin N → ℚ := fun i => if i = 0 then 1 else 0

theorem e₀_ne (N : ℕ) [NeZero N] : e₀ N ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e₀] at this

/-- **The empty-body branch of `hd`.**  At an interior point whose relaxed body is empty, the
analytic run record exists for the all-`cut` stream — for every parameter family `P` and every bit
`o` that reads `false` there. -/
noncomputable def runParts_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hbit : o G t = false)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  have hN : 2 ≤ G.n * G.n := by have := hn; nlinarith
  haveI : NeZero (G.n * G.n) := ⟨by omega⟩
  set c : ℕ → Fin (G.n * G.n) → ℚ := fun _ => e₀ (G.n * G.n) with hc
  have hcne : ∀ k : ℕ, c k ≠ 0 := fun _ => e₀_ne (G.n * G.n)
  set cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
    QMCLeafB.RunPartsDilate.runCut G P hn c hcne with hcd
  have hrunwit : ∀ k,
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c :=
    fun k => QMCLeafB.RunPartsDilate.runCut_wit G P hn c hcne k
  have hpos : ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p :=
    QMCLeafB.RunPartsShallow.sigmaQ_pos_of_wit hN
      (QMCLeafB.RunPartsDilate.A0P_posDef G P) hrunwit (fun _ => P.hrmax) (fun k => hcne k)
  exact
    { ok := fun _ => false
      cd := cd
      del := fun _ => 0
      hcert := by intro k _ hok; exact absurd hok (by simp)
      hwit := fun k _ _ => hrunwit k
      hrho := by intro k _ _; exact P.hrmax
      hcne := by intro k _ _; exact hcne k
      hdel0 := by intro k _ _; exact le_refl 0
      hcheck := by
        intro k _ _
        have h := hpos k
        have hrho : (cd k).rho = P.rmax := rfl
        have h2 : (0 : ℚ) ≤ (cd k).rho ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p := by
          rw [hrho]
          exact mul_nonneg (sq_nonneg _) (le_of_lt h)
        simpa using h2
      hle := by intro k _ _; exact le_refl P.rmax
      hcut := by
        intro k _ _ z hz
        exact absurd hz (not_relaxBall_of_emptyBody hempty z)
      hverdict := by
        rw [hbit, QMCLeafB.RecordM2.anyOk_false_stream] }

#print axioms QMCLeafB.RefutedM3.runParts_of_emptyBody

/-- **The same at the leaf's own analytic shape**: the empty-body branch of `hd` as `RunData`. -/
noncomputable def runData_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hbit : o G t = false)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X) :
    QMCLeafB.VerdictSound.RunData o G t :=
  QMCLeafB.FinalStroke.RunParts.toRunData (runParts_of_emptyBody G t P hn hbit hempty)

#print axioms QMCLeafB.RefutedM3.runData_of_emptyBody

/-! ## 3.  The anchor at `(G₀, −99999/100000)`

`G₀` is d1's two-vertex one-edge instance (`Rq = 1`, `wMatrixQ = !![0, 1/2; 1/2, 0]`) and `t₀` the
interior point where the relaxed body is empty.  §3.1 redoes the body estimate over **ℝ** — the ball
lives in real matrices, while `RelaxMem` is rational, so the rational statement of
`Check_emptybody_m5` does not transfer — and §3.2 is the anchor itself. -/

/-- The four entries of the real weight matrix of `G₀`. -/
theorem wMatrix_G₀_00 :
    QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀ (0 : Fin 2) (0 : Fin 2) = 0 :=
  QMCLeafB.wMatrix_apply_of_eq

theorem wMatrix_G₀_11 :
    QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀ (1 : Fin 2) (1 : Fin 2) = 0 :=
  QMCLeafB.wMatrix_apply_of_eq

theorem wMatrix_G₀_01 :
    QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀ (0 : Fin 2) (1 : Fin 2) = 1 / 2 := by
  rw [QMCLeafB.wMatrix_apply]
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrix_G₀_10 :
    QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀ (1 : Fin 2) (0 : Fin 2) = 1 / 2 := by
  rw [QMCLeafB.wMatrix_apply]
  norm_num [QMCLeafB.ResidRefute.G₀]

/-- **The real relaxed body at `(G₀, t₀)` is empty.**  The same two test vectors as the rational
estimate: `diag_near` bounds the diagonal above, the PSD slot at `x = (1,1)` bounds the off-diagonal
sum below, and `⟪A,X⟫` is half that sum, which `trace_le` puts above a strictly larger number. -/
theorem body_empty_G₀ (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀)
      ((QMCLeafB.EmptyBodyM5.t₀ : ℝ) -
        (((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ))
      (((QMCLeafB.EmptyBodyM5.dq₀ : ℚ)) : ℝ) X := by
  intro h
  obtain ⟨hpsd, hdiag, htrace⟩ := h
  have hdqv : (((QMCLeafB.EmptyBodyM5.dq₀ : ℚ)) : ℝ) = 1 / 400000 := by
    rw [QMCLeafB.EmptyBodyM5.dq₀_eq]; norm_num
  have huv : (QMCLeafB.EmptyBodyM5.t₀ : ℝ) -
      (((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ)
      = -(99999 / 100000) - 1 / 40000 := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]
    unfold QMCLeafB.EmptyBodyM5.t₀
    norm_num
  have h00 : X 0 0 ≤ 1 + (((QMCLeafB.EmptyBodyM5.dq₀ : ℚ)) : ℝ) / 4 := by
    have h := (abs_le.mp (hdiag 0)).2
    linarith
  have h11 : X 1 1 ≤ 1 + (((QMCLeafB.EmptyBodyM5.dq₀ : ℚ)) : ℝ) / 4 := by
    have h := (abs_le.mp (hdiag 1)).2
    linarith
  have hpsd1 := hpsd (fun _ : Fin 2 => (1 : ℝ))
  have hsq : (∑ i : Fin 2, ((1 : ℝ)) ^ 2) = 2 := by norm_num
  have hq : QMCLeafB.BallFloor.qfR X (fun _ : Fin 2 => (1 : ℝ))
      = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  rw [hsq, hq] at hpsd1
  have hfrob : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀) X
      = 1 / 2 * X 0 1 + 1 / 2 * X 1 0 := by
    simp only [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, QMCLeafB.wMatrix_apply]
    norm_num [QMCLeafB.ResidRefute.G₀]
  rw [hfrob] at htrace
  rw [hdqv] at h00 h11 hpsd1
  rw [huv] at htrace
  linarith

#print axioms QMCLeafB.RefutedM3.body_empty_G₀

/-- **The anchor**: the analytic run record at `(G₀, t₀)`, for every bit that reads `false` there.
This is the run `hd` needs at the refuted point of the campaign — the point where phase 20's
`CoreDataF` is uninhabitable (d1). -/
noncomputable def runParts_G₀_of_bitFalse (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hbit : o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false) :
    QMCLeafB.FinalStroke.RunParts o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  runParts_of_emptyBody _ _ _ QMCLeafB.ResidKill.hnG₀ hbit body_empty_G₀

#print axioms QMCLeafB.RefutedM3.runParts_G₀_of_bitFalse

/-- The same at `RunData` — the shape `VerdictSound.solution_of_loop_via_runData` consumes as `hd`. -/
noncomputable def runData_G₀_of_bitFalse (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hbit : o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false) :
    QMCLeafB.VerdictSound.RunData o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ :=
  runData_of_emptyBody _ _ _ QMCLeafB.ResidKill.hnG₀ hbit body_empty_G₀

#print axioms QMCLeafB.RefutedM3.runData_G₀_of_bitFalse

/-! ## 4.  What this settles, and the one hypothesis it leaves

*Settled.*  The phase-21 refutation of `CoreDataF` does **not** reach the analytic boundary: at an
empty body `RunParts`/`RunData` exist for the all-`cut` stream with zero margins, with no cut budget,
no multiplier, no pinch and no drift.  Consequently the endgame's `hd` splits cleanly in two:

* **empty body** — this module (the bit equation and body emptiness are the only inputs);
* **nonempty body** — where the member certificate, the cut records and the two drift budgets live
  (d2/d3/d4's lanes).  The refutation says nothing about that side; `hcutfin` is satisfiable there
  because a member exists.

*Left open.*  The hypothesis `hbit : o G₀ t₀ = false`.  It is **not** obtainable from phase 20's
`hverdict_eq_false_G₀` as stated: that lemma is conditioned on a `CoreDataF`, which does not exist at
the empty point, so it is vacuous there.  The honest routes to the bit are (a) the program bridge
`hon` (d2: a program `ok` round implies a member, hence none at an empty body) composed with the
all-`false` read-out, or (b) taking the bit equation as a slot of whatever residual is closed with.
This module takes the second route and keeps `hbit` explicit, so that either supplier plugs in
without touching the construction.
-/


/-! ## 5.  The bit at an empty body, from the program's own `ok` test

The anchor above takes `o G t = false` as a hypothesis.  It does not have to stay one: the program's
`ok` bit is a *sufficient* condition for membership (`hon`, d2's bridge), so at an empty body every
round of the program's own flag stream is `false` and its verdict bit — read out by `anyOk` at the
horizon — is `false`.  Both the read-out and the implication are taken as the two premises they are,
so the lemma is independent of how the program's stream is named. -/

/-- **An empty body forces the loop's bit to `false`**, given (i) the read-out equation at the
program's own flag stream and (ii) the `ok ⇒ member` implication at that stream's centres. -/
theorem bit_false_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq) :
    o G t = false := by
  have hall : ∀ k, k < P.K * P.m → rb k = false := by
    intro k _
    cases h : rb k with
    | false => rfl
    | true => exact absurd (hok k h) (hempty (cX k))
  rw [hbit, QMCLeafB.ResidRefute.anyOk_all_false rb (P.K * P.m) hall]

#print axioms QMCLeafB.RefutedM3.bit_false_of_emptyBody

/-- **The empty branch with the bit discharged**: empty body + the read-out + `ok ⇒ member` give the
run record outright. -/
noncomputable def runParts_of_emptyBody' {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hemptyQ : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  runParts_of_emptyBody G t P hn
    (bit_false_of_emptyBody hbit hok hemptyQ) hempty

#print axioms QMCLeafB.RefutedM3.runParts_of_emptyBody'

/-! ## 6.  The `hd` split

The closing stroke `VerdictSound.solution_of_loop_via_runData` asks for
`hd : ∀ G t, 2 ≤ G.n → −Rq G ≤ t → t ≤ 0 → RunData o G t`.  The two branches are *exhaustive* and
this section performs the split: an empty body is discharged here, a nonempty body is the other
lane's.  Nothing about the nonempty case is assumed beyond its own producer. -/

/-- **`hd` from the nonempty branch.**  Given (i) the read-out + `ok ⇒ member` premises that make the
bit `false` at an empty body, and (ii) a producer for the nonempty-body points, the leaf's whole
`hd` obligation follows. -/
noncomputable def hd_of_nonemptyBranch {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cX : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o G t = QMCLeafB.SimLoop.anyOk (rb G t) ((Pfam G).K * (Pfam G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX G t k)
        (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((Pfam G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq)
    (hne : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((Pfam G).dq : ℚ) : ℝ) X) →
      QMCLeafB.VerdictSound.RunData o G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → -QMCLeafB.EngineRuntime.Rq G ≤ t →
      t ≤ 0 → QMCLeafB.VerdictSound.RunData o G t := by
  intro G t hn _ _
  by_cases hbody : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((Pfam G).dq : ℚ) : ℝ) X
  · exact hne G t hn hbody
  · rw [not_exists] at hbody
    exact runData_of_emptyBody G t (Pfam G) hn
      (bit_false_of_emptyBody (hbit G t) (hok G t) (hemptyR G t hbody)) hbody

#print axioms QMCLeafB.RefutedM3.hd_of_nonemptyBranch

end QMCLeafB.RefutedM3


