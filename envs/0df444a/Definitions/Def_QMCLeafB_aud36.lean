-- Prove2me | Definitions.Def_QMCLeafB_aud36
-- name    : QMCLeafB_aud36
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:36:15.584227+00:00
-- url     : https://prove2.me/theorems/b9c50459-10d1-469b-8f84-6ac1da213064
-- title:
--   QMCLeafB aud36
-- statement:
--   # `Check_aud36_m6` — phase 36, m6, direction d6 (`audit36`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_dc35
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_bh35
import Definitions.Def_QMCLeafB_hokupper34
/-
# `Check_aud36_m6` — phase 36, m6, direction d6 (`audit36`)

Independent re-audit of the four load-bearing phase-35 files plus the statement lock, on the
PUBLISHED cone only (`Definitions.Def_QMCLeafB_*`; no `Solutions.*` import).

## §1  Coordinator step 2 repaired: the ball obstruction is radius-free for the RUN's own data

Step 2 reads m1's `DC35M1.not_shallowCut_of_ball_horizon` as "a ball-bearing body admits NO record".
It does not say that: it refutes `ThinRec34M4.ShallowCut`, which is stated at the CANONICAL ceiling
stream `NormalCut (fun k => c k)` with `rho ≡ rmax`.  A `RunParts` record carries its OWN stream `cd`
with only `0 ≤ rho ≤ rmax` (`hrho`, `hle`), and `hwit` pins `p` through the run's own shapes
`Aat … cd k`.  So `BodyRec → ShallowCut` needs `cd = NormalCut (·.c)`, which is not a field and is
not derivable: two streams with the same normals and different `rho` give different `Aat`, hence
different `p`, hence different `σ`.

The repair costs nothing: `BallM2.no_runParts_of_ball` uses the campaign radius in exactly two
places — as `hr : 0 < r` and as `P.hbudget : volPot A₀·(1/2)^K < r^(n·n)`.  Parameterizing by `r`
gives the radius-free refutation of `BodyRec` from the run's OWN data.

## §2  What that does and does not give

`bit_true_of_ball_gen` is the honest form of "so the bit is TRUE": given a record family, the bit is
`true` at every ball-bearing point.  That is a NECESSARY condition on any correct fill, not a proof
of `CompleteSlot`.

Discipline: `set_option autoImplicit false`; no proof holes, no extra principles, no native
computation; `#print axioms` after every declaration (all `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Aud36M6

open QuantumMaxCutEnergy
open QMCLeafB.BallM2 (runBall)

/-! ## 1.  Radius-free ball obstruction, from the run's own transcript -/

theorem no_runParts_of_ball_gen
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ runBall G t P)
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n))
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t = true := by
  classical
  by_contra hcon
  have hfalse : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  have hall : ∀ k, k < P.K * P.m → B.ok k = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).mp
      (by rw [← B.hverdict]; exact hfalse)
  have hNm : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by nlinarith [P.hdq]
  have hn' : 2 ≤ G.n * G.n := by nlinarith
  have hA0 : (QMCLeafB.EngineIterates.castM
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
    QMCLeafB.Boundary.initShapeOf_cast_posDef hNm
  have hwit : ∀ k, k < P.K * P.m →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd k *ᵥ (B.cd k).p = (B.cd k).c :=
    fun k hk => B.hwit k hk (hall k hk)
  have hρ : ∀ k, k < P.K * P.m → 0 ≤ (B.cd k).rho :=
    fun k hk => B.hrho k hk (hall k hk)
  have hcne : ∀ k, k < P.K * P.m → (B.cd k).c ≠ 0 :=
    fun k hk => B.hcne k hk (hall k hk)
  have hcover : ∀ z, runBall G t P z →
      QMCLeafB.EngineIterates.Ell (QMCLeafB.EngineIterates.castM
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))) 0 z :=
    fun z hz => QMCLeafB.Boundary.ell_initShapeOf hNm (QMCLeafB.Boundary.relaxBall_norm hz)
  have hδ0 : ∀ k, k < P.K * P.m → 0 ≤ B.del k :=
    fun k hk => B.hdel0 k hk (hall k hk)
  have hcheck : ∀ k, k < P.K * P.m →
      (B.del k) ^ 2 ≤ ((B.cd k).rho) ^ 2 *
        QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p :=
    fun k hk => B.hcheck k hk (hall k hk)
  have hcutδ : ∀ k, k < P.K * P.m → ∀ z, runBall G t P z →
      -(((B.del k : ℚ)) : ℝ) ≤ QMCLeafB.EngineIterates.cutCR B.cd k
        ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) :=
    fun k hk z hz => B.hcut k hk (hall k hk) z hz
  have hle : ∀ k, k < P.K * P.m → (B.cd k).rho ≤ P.rmax :=
    fun k hk => B.hle k hk (hall k hk)
  obtain ⟨hcont, hvol⟩ := QMCLeafB.SimLoop.Prefix.body_containment_at_halving_margin_prefix
    (n := G.n * G.n) hn' (A0 := QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (cd := B.cd) (T := P.K * P.m)
    hA0 hwit hρ hcne (0 : Fin (G.n * G.n) → ℝ) (runBall G t P) hcover hδ0 hcheck hcutδ
    P.hrmax hle P.hhalve (le_rfl : QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K ≤
      QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K) le_rfl
  have hKpd : (QMCLeafB.BallFloor.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))).PosDef :=
    QMCLeafB.SimLoop.Aat_cast_posDef_prefix hn' hA0 hwit hρ hcne (P.K * P.m) le_rfl
  refine QMCLeafB.BallFloor.no_run_of_ball (A := QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))
    hKpd (a := QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (P.K * P.m))
    (a₀ := QMCLeafB.AnswerProducer.flat X₀) (body := runBall G t P) (ε :=
      QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K) hr ?_ ?_ hvol hR
  · intro y hy
    apply hball
    have : ∑ k, ((y + QMCLeafB.AnswerProducer.flat X₀) k
        - QMCLeafB.AnswerProducer.flat X₀ k) ^ 2 = ∑ k, y k ^ 2 := by
      simp
    rw [QMCLeafB.Boundary.eucBallF, Set.mem_ofPred_eq, this]
    exact hy
  · intro z hz
    exact hcont z hz

#print axioms QMCLeafB.Aud36M6.no_runParts_of_ball_gen

/-- **Monotone side of the horizon condition.**  `P.hbudget` (the campaign radius) implies the
radius-free condition at every `r` at least as large.  For `r` BELOW the campaign radius the
condition is strictly stronger than `hbudget` and has to be discharged by arithmetic (see the
report: at `paramsKbc2`/`G₁` every `r ≳ 10^{-6761}` works). -/
theorem horizon_of_ge_campaign
    {G : QuantumMaxCutEnergy.Input} {P : QMCLeafB.FinalStroke.RunParams G}
    {r : ℝ} (hrr : (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) ≤ r) :
    QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n) := by
  have hr0 : (0 : ℝ) < (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) := by
    have h1 : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
    have h2 : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
    positivity
  exact lt_of_lt_of_le P.hbudget (pow_le_pow_left₀ hr0.le hrr _)

#print axioms QMCLeafB.Aud36M6.horizon_of_ge_campaign

/-- **Radius-free `no_runParts_of_ball`, campaign side**: a ball at least as large as the campaign's
already forbids the record. -/
theorem no_runParts_of_ball_le
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hrr : (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) ≤ r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ runBall G t P)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t = true :=
  no_runParts_of_ball_gen hn hr hball (horizon_of_ge_campaign hrr) B

#print axioms QMCLeafB.Aud36M6.no_runParts_of_ball_le

theorem not_bodyRec_of_ball_gen
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ runBall G t P)
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n)) :
    ¬ QMCLeafB.ThinRec34M4.BodyRec G t P := by
  rintro ⟨B⟩
  have h := no_runParts_of_ball_gen hn hr hball hR B
  exact Bool.false_ne_true h

#print axioms QMCLeafB.Aud36M6.not_bodyRec_of_ball_gen

/-! ## 2.  The honest form of "so the bit is TRUE" -/

theorem bit_true_of_ball_gen
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ runBall G t P)
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n))
    (hrec : o G t = false → Nonempty (QMCLeafB.FinalStroke.RunParts o G t P)) :
    o G t = true := by
  cases ho : o G t with
  | false =>
      obtain ⟨B⟩ := hrec ho
      rw [no_runParts_of_ball_gen hn hr hball hR B] at ho
      exact Bool.noConfusion ho
  | true => rfl

#print axioms QMCLeafB.Aud36M6.bit_true_of_ball_gen

theorem not_shallowSlot_of_ball
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ runBall G t P)
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n))
    (hslot : o G t = false → QMCLeafB.ThinRec34M4.ShallowCut G t P hn) :
    o G t = true :=
  bit_true_of_ball_gen hn hr hball hR
    (fun hf => (QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec (o := o) hf).2
      (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (hslot hf)))

#print axioms QMCLeafB.Aud36M6.not_shallowSlot_of_ball

/-! ## 3.  The statement lock

The live platform statement, fetched from `GET /theorems/d9f601e5-8c68-4369-a27d-701e73e686b8`
(status `Open`, `mathlib_rev 0df444a360eaa60ab8c11dca51a86af692955474`, identical to `lakefile.lean`'s
pin), pasted verbatim and proved DEFINITIONALLY EQUAL to the campaign's `FinishLine.SolutionStatement`
by `rfl`.  `rfl` on `Prop`s is definitional equality, so a single token of drift would fail the
`def`-equality; the whitespace-insensitive textual diff (checked separately, 507 characters after
normalisation on both sides) agrees.
-/

/-- The live `formal_statement`'s conclusion, verbatim. -/
def liveStatement : Prop :=
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
      S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000

/-- **THE LOCK.**  The live statement and the campaign's sentence are the SAME proposition,
definitionally. -/
theorem lock_live_eq_solutionStatement :
    liveStatement = QMCLeafB.FinishLine.SolutionStatement := rfl

#print axioms QMCLeafB.Aud36M6.lock_live_eq_solutionStatement

/-- The same lock in `Iff` form, which is the shape every closing stroke consumes. -/
theorem lock_live_iff : liveStatement ↔ QMCLeafB.FinishLine.SolutionStatement := Iff.rfl

#print axioms QMCLeafB.Aud36M6.lock_live_iff

/-! ## 4.  The four files' own prints, completed

Each of `Check_by35_m6`, `Check_dc35_m1`, `Check_hokupper34_m8`, `Check_bh35_m5` prints axioms for
almost all of its declarations; these are the six that carry no print (m1's is the only load-bearing
one — the initial shape's positive definiteness, used by every determinant argument). -/

#print axioms QMCLeafB.Bypass35M6.traceStream_ne_zero
#print axioms QMCLeafB.Bypass35M6.trF_add
#print axioms QMCLeafB.Bypass35M6.trF_smul
#print axioms QMCLeafB.DC35M1.initShape_posDef
#print axioms HokUpper34M8.list_sum_nonneg
#print axioms HokUpper34M8.le_list_sum

/-! ## 5.  Cross-checks of the four headline statements against what the assembler assumes -/

#print axioms QMCLeafB.DC35M1.not_shallowCut_of_ball_horizon
#print axioms QMCLeafB.DC35M1.containment_of_shallow
#print axioms QMCLeafB.Bypass35M6.shallowCut_of_separating
#print axioms QMCLeafB.Bypass35M6.sigmaQ_normalCut_pos
#print axioms QMCLeafB.BH35M5.topGate_iff_mem
#print axioms QMCLeafB.BH35M5.dreg_bit_complete_fails
#print axioms QMCLeafB.BH35M5.dreg_reachTop_const
#print axioms HokUpper34M8.hok_of_releasedGate
#print axioms QMCLeafB.ThinRec34M4.encl_of_bodyRec
#print axioms QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut
#print axioms QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec
#print axioms QMCLeafB.BallM2.no_runParts_of_ball

end QMCLeafB.Aud36M6


