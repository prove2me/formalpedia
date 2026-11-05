-- Prove2me | Definitions.Def_QMCLeafB_ball_m2
-- name    : QMCLeafB_ball_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:11:11.953258+00:00
-- url     : https://prove2.me/theorems/d9c46900-ccfb-43ca-9fae-457e1f2b9961
-- title:
--   QMCLeafB ball_m2
-- statement:
--   # Leaf B phase 24 — m2, direction `sliver-ball`: the sliver body carries the campaign's ball,
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_parts_m2
/-
# Leaf B phase 24 — m2, direction `sliver-ball`: the sliver body carries the campaign's ball,
# and therefore the sliver's bit is FORCED TRUE

## What this file proves

**(1) `no_runParts_of_ball` — a ball in the run's relaxation forbids an all-`false` stream.**
Give `FinalStroke.RunParts o G t P` and a Euclidean ball of radius `P.dq / (8·(P.cAq+1))` around
some point of the run's own relaxation `runBall G t P = relaxBall (wMatrix G) (t − Rq/40000) P.dq M`
(`M = 2n² + 2dq²`, exactly `RunParts.hcut`'s quantifier).  If `o G t = false`, then `hverdict` +
`anyOk_eq_false_iff` make every round `k < K·m` a cut round, so `hcut/hcheck/hrho/hcne/hdel0/hle`
plus the halving (`P.hhalve`, `hbudget`) give

  `relaxBall ⊆ Ell (Aat (K·m)) (Cat (K·m))`  and  `volPot (Aat (K·m)) ≤ volPot₀·(1/2)^K < r^(n·n)`,

while the contained ball gives `r^(n·n) ≤ volPot (Aat (K·m))` (the ball floor
`BallFloor.no_run_of_ball`).  Contradiction.  Hence **`o G t = true`**: a ball-bearing body forces a
true bit, at *every* `RunParams`, with no other hypothesis.

**(2) At the sliver the ball exists, at the campaign's own radius.**  `Xs = !![1,y;y,1]`,
`y = −(1 + 7·dq/16) = −(1 + 7/6080000)` is a point of the real relaxed body at `(G₁, t₁)`
(PSD slack `7dq/16`, level slack `3dq/8`), and the whole Frobenius ball of radius `dq/24` around it
lies in `relaxBall (wMatrix G₁) (t₁ − Rq/40000) (dq) (8 + 2dq²)`.  Since the campaign's `cAq` is
`Rq G` (definitionally, `runParamsOfK`), at `G₁` that is `dq/(8·3) = dq/24` — the sliver's ball is
*exactly* the campaign's ball.  `sliver_ball_sharp` shows `dq/16` is the largest radius any centre
admits, so `Xs` is the optimal centre and `dq/24` is within a factor `3/2` of sharp.

**(3) Consequences.**  `sliver_bit_true`: every `RunParts` at `(G₁,t₁)` has
`o G₁ t₁ = true`; `campaign_bit_true_at_sliver`: `ResidParts campaignBit paramsKbc2` **forces**
`campaignBit G₁ t₁ = true`.  So the `ok ≡ false` production route (`hcert` vacuous) that the phase-23
plan named for the sliver **cannot exist**, and any production there must report `ok` at least once.
That route is not vacuous: `sliver_hcert_witness` exhibits `!![1,-1;-1,1]` (unit diagonal, PSD,
objective `-2 < t₁ + Rq/40000`) as an `ok`-round certificate at the sliver.

This is the exact `dM = 1` volume obstruction, stated at the sliver: the `hbudget` inequality that
makes the engine refute a body is *also* a floor on any body that carries the campaign's ball.  Both
sides are machine-checked; nothing here is a heuristic.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom cone `[propext, Classical.choice, Quot.sound]` (audit at the end).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.BallM2

open QuantumMaxCutEnergy

/-- The run's relaxed body, in flat coordinates. -/
abbrev runBall (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Set (Fin (G.n * G.n) → ℝ) :=
  QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
    ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
    ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ)

theorem no_runParts_of_ball
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ runBall G t P)
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
  have hr : 0 < (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) := by
    have h1 : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
    have h2 : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
    positivity
  have hKpd : (QMCLeafB.BallFloor.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))).PosDef :=
    QMCLeafB.SimLoop.Aat_cast_posDef_prefix hn' hA0 hwit hρ hcne (P.K * P.m) le_rfl
  refine QMCLeafB.BallFloor.no_run_of_ball (A := QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))
    hKpd (a := QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (P.K * P.m))
    (a₀ := QMCLeafB.AnswerProducer.flat X₀) (body := runBall G t P) hr ?_ ?_ hvol ?_
  · intro y hy
    apply hball
    have : ∑ k, ((y + QMCLeafB.AnswerProducer.flat X₀) k
        - QMCLeafB.AnswerProducer.flat X₀ k) ^ 2 = ∑ k, y k ^ 2 := by
      simp
    rw [QMCLeafB.Boundary.eucBallF, Set.mem_setOf_eq, this]
    exact hy
  · intro z hz
    exact hcont z hz
  · exact P.hbudget

/-! ## 2.  Two general lemmas: margin-summed ball containment, and a Frobenius norm-doubling bound -/

/-- **A ball around a body point, from explicit slacks.**  If `X₀` satisfies the three ledger
inequalities with slacks `m₁ m₂ m₃` (PSD margin, diagonal distance, objective distance) then the
Frobenius ball of radius `r` around `X₀` lies in the body at tolerance `δ` as soon as the radius
plus each slack fits the tolerance. -/
theorem matBall_subset_relaxBodyLE {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ cA r m₁ m₂ m₃ : ℝ}
    (hr : 0 ≤ r) (hcA : 0 ≤ cA) (hAsum : ∑ i, ∑ j, |A i j| ≤ cA)
    {X₀ : Matrix (Fin n) (Fin n) ℝ}
    (hpsd : ∀ x : Fin n → ℝ, -m₁ * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR X₀ x)
    (hdiag : ∀ i, |X₀ i i - 1| ≤ m₂)
    (htr : QMCLeafB.BallFloor.frob A X₀ ≤ u + m₃)
    (h1 : r + m₁ ≤ δ / 2) (h2 : r + m₂ ≤ δ / 4) (h3 : r * cA + m₃ ≤ δ / 2) :
    QMCLeafB.BallFloor.matBall X₀ r ⊆ QMCLeafB.BallFloor.relaxBodyLE A u δ := by
  intro X hX
  obtain ⟨E, rfl⟩ : ∃ E, X = X₀ + E := ⟨X - X₀, (add_sub_cancel X₀ X).symm⟩
  have hEn : QMCLeafB.BallFloor.frobNormSq E ≤ r ^ 2 := by
    simpa [QMCLeafB.BallFloor.matBall] using hX
  have hdiagE : ∀ i, |E i i| ≤ r :=
    fun i => QMCLeafB.BallFloor.abs_apply_le_of_frobNormSq_le hr hEn i i
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hx2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2' : -(r * (∑ i, x i ^ 2)) ≤ QMCLeafB.BallFloor.qfR E x :=
      (abs_le.mp (QMCLeafB.BallFloor.abs_qfR_le_of_frobNormSq_le (E := E) (x := x) hr hEn)).1
    have h0 := hpsd x
    have h1' : (r + m₁) * (∑ i, x i ^ 2) ≤ (δ / 2) * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right h1 hx2
    rw [QMCLeafB.BallFloor.qfR_add]
    nlinarith
  · intro i
    have hsum : (X₀ + E) i i - 1 = (X₀ i i - 1) + E i i := by
      rw [Matrix.add_apply]; ring
    have h1' : |(X₀ + E) i i - 1| ≤ |X₀ i i - 1| + |E i i| := by
      rw [hsum]; exact abs_add_le _ _
    have h3' := hdiag i
    have h4' := hdiagE i
    linarith
  · have h1' : QMCLeafB.BallFloor.frob A (X₀ + E)
        = QMCLeafB.BallFloor.frob A X₀ + QMCLeafB.BallFloor.frob A E :=
      QMCLeafB.BallFloor.frob_add A X₀ E
    have h2' : QMCLeafB.BallFloor.frob A E ≤ r * (∑ i, ∑ j, |A i j|) :=
      (abs_le.mp (QMCLeafB.BallFloor.abs_frob_le (A := A) (E := E) hr hEn)).2
    have h5 : r * (∑ i, ∑ j, |A i j|) ≤ r * cA := mul_le_mul_of_nonneg_left hAsum hr
    rw [h1']
    nlinarith

/-- **A Frobenius norm bound for a sum**: `‖X + E‖² ≤ (3/2)‖X‖² + 3‖E‖²`, entrywise from
`2ab ≤ a²/2 + 2b²`. -/
theorem frobNormSq_add_le {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frobNormSq (X + E)
      ≤ 3 / 2 * QMCLeafB.BallFloor.frobNormSq X + 3 * QMCLeafB.BallFloor.frobNormSq E := by
  have hterm : ∀ i j, (X + E) i j ^ 2
      ≤ 3 / 2 * X i j ^ 2 + 3 * E i j ^ 2 := by
    intro i j
    have h : 2 * X i j * E i j ≤ X i j ^ 2 / 2 + 2 * E i j ^ 2 := by
      nlinarith [sq_nonneg (X i j - 2 * E i j)]
    rw [Matrix.add_apply]
    nlinarith
  have hl : ∀ i, ∑ j, (3 / 2 * X i j ^ 2 + 3 * E i j ^ 2)
      = 3 / 2 * (∑ j, X i j ^ 2) + 3 * (∑ j, E i j ^ 2) := by
    intro i
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hsum : (∑ i, ∑ j, (3 / 2 * X i j ^ 2 + 3 * E i j ^ 2))
      = ∑ i, (3 / 2 * (∑ j, X i j ^ 2) + 3 * (∑ j, E i j ^ 2)) :=
    Finset.sum_congr rfl fun i _ => hl i
  have h3 : (∑ i, (3 / 2 * (∑ j, X i j ^ 2) + 3 * (∑ j, E i j ^ 2)))
      = 3 / 2 * (∑ i, ∑ j, X i j ^ 2) + 3 * (∑ i, ∑ j, E i j ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
  simp only [QMCLeafB.BallFloor.frobNormSq]
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j) ?_
  rw [hsum, h3]

/-! ## 3.  The sliver: the relaxed body at `(G₁, t₁)` carries the campaign's ball -/

/-- The sliver ball centre: unit diagonal, off-diagonal `-(1 + 7·dq/16) = -(1 + 7/6080000)`.  Its
PSD slack is `7·dq/16` and its level slack is `dq/8`; the optimum of the two binding slacks is at
this `y`, and it gives radius `dq/16` (we use the safe `dq/24`). -/
def Xs : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 1 else -(1 + 7 / 6080000)

/-- The campaign's ball radius at the sliver: `dq/(8·(c_A+1))` at `dq = 1/380000`, `c_A = 2`,
i.e. `dq/24 = 1/9120000`. -/
def rSliver : ℝ := 1 / 9120000

theorem Xs_diag : ∀ i, Xs i i = 1 := by
  intro i; simp [Xs]

theorem Xs_qf (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xs x
      = x 0 ^ 2 + x 1 ^ 2 - 2 * (1 + 7 / 6080000) * (x 0 * x 1) := by
  simp [QMCLeafB.BallFloor.qfR, Xs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Xs_qf_lb (x : Fin 2 → ℝ) :
    -(7 / 6080000) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR Xs x := by
  rw [Xs_qf, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 - x 1)]

theorem Xs_frob :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁) Xs
      = -(2 + 7 / 3040000) := by
  rw [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
  simp [Xs]
  norm_num

theorem Xs_frobNormSq : QMCLeafB.BallFloor.frobNormSq Xs
    = 2 + 2 * (1 + 7 / 6080000) ^ 2 := by
  simp [QMCLeafB.BallFloor.frobNormSq, Xs, Fin.sum_univ_two]
  norm_num

theorem wMatrix_G₁_asum :
    (∑ i : Fin 2, ∑ j : Fin 2, |QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁ i j|) = 2 := by
  simp [Fin.sum_univ_two, QMCLeafB.AnchorFactsM2.wMatrix_G₁_00,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_11, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10]
  norm_num

/-- **The sliver's relaxed body contains the Frobenius ball of radius `dq/24`** around `Xs`, at
tolerance `dq = 1/380000`.  The three slacks are PSD `7dq/16`, diagonal `0`, level `3dq/8`; the
radius `dq/24` satisfies `dq/24 + 7dq/16 = 23dq/48 ≤ dq/2`, `dq/24 ≤ dq/4` and
`2·(dq/24) + 3dq/8 = 11dq/24 ≤ dq/2`. -/
theorem sliver_matBall :
    QMCLeafB.BallFloor.matBall Xs rSliver ⊆
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁)
        (((QMCLeafB.AnchorFactsM2.t₁ : ℚ) : ℝ)
          - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.AnchorFactsM2.P₁).dq : ℚ) : ℝ) := by
  have hrq : QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ = 2 :=
    QMCLeafB.EmptyBodyM5.Rq_G₁
  have hdq : (QMCLeafB.AnchorFactsM2.P₁).dq = 1 / 380000 :=
    QMCLeafB.EmptyBodyM5.dq₁_eq
  have hu : ((QMCLeafB.AnchorFactsM2.t₁ : ℚ) : ℝ)
      - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 5 / 1520000) := by
    rw [hrq]; unfold QMCLeafB.AnchorFactsM2.t₁; norm_num
  rw [hdq, hu]
  refine matBall_subset_relaxBodyLE (A := QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁)
    (u := -(2 + 5 / 1520000)) (δ := ((1 / 380000 : ℚ) : ℝ)) (cA := 2) (r := rSliver)
    (m₁ := 7 / 6080000) (m₂ := 0) (m₃ := 3 / 3040000) (by norm_num [rSliver]) (by norm_num)
    (by rw [wMatrix_G₁_asum]) (by simpa using Xs_qf_lb) ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [Xs_diag i]
    norm_num
  · rw [Xs_frob]; norm_num
  · norm_num [rSliver]
  · norm_num [rSliver]
  · norm_num [rSliver]

/-- **The ball is inside the run's relaxation** `relaxBall` (body *and* norm bound). -/
theorem sliver_ball :
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat Xs) rSliver
      ⊆ runBall QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
          QMCLeafB.AnchorFactsM2.P₁ := by
  have hrq : QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ = 2 :=
    QMCLeafB.EmptyBodyM5.Rq_G₁
  have hdq : (QMCLeafB.AnchorFactsM2.P₁).dq = 1 / 380000 :=
    QMCLeafB.EmptyBodyM5.dq₁_eq
  have hn1 : QMCLeafB.AnchorFactsM2.G₁.n = 2 := QMCLeafB.AnchorFactsM2.n₁
  intro z hz
  have hr0 : (0 : ℝ) ≤ rSliver := by norm_num [rSliver]
  -- (i) the slack transport from flat coordinates
  have hE : QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z - Xs) ≤ rSliver ^ 2 := by
    have hfn : QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z - Xs)
        = ∑ k : Fin (2 * 2), (QMCLeafB.AnswerProducer.flat
            (QMCLeafB.Boundary.unflat z - Xs)) k ^ 2 :=
      (QMCLeafB.Boundary.sum_sq_flat (QMCLeafB.Boundary.unflat z - Xs)).symm
    rw [hfn]
    refine le_trans (le_of_eq ?_) hz
    exact Finset.sum_congr rfl fun k _ => by
      simp [QMCLeafB.Boundary.flat_sub, QMCLeafB.Boundary.flat_unflat]
  refine ⟨?_, ?_⟩
  · exact sliver_matBall (show QMCLeafB.Boundary.unflat z
        ∈ QMCLeafB.BallFloor.matBall Xs rSliver from hE)
  · -- (ii) the norm bound `∑ zᵢ² ≤ M`
    have hnorm : (∑ k, z k ^ 2) = QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z) := by
      rw [show (∑ k, z k ^ 2)
          = ∑ k : Fin (2 * 2),
              (QMCLeafB.AnswerProducer.flat (QMCLeafB.Boundary.unflat z)) k ^ 2 from by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [QMCLeafB.Boundary.flat_unflat]]
      rw [QMCLeafB.Boundary.sum_sq_flat]
      rfl
    have hdec : QMCLeafB.Boundary.unflat z = Xs + (QMCLeafB.Boundary.unflat z - Xs) :=
      (add_sub_cancel Xs (QMCLeafB.Boundary.unflat z)).symm
    rw [hnorm, hdec]
    have hb := frobNormSq_add_le Xs (QMCLeafB.Boundary.unflat z - Xs)
    have h3 : (3 : ℝ) * QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z - Xs)
        ≤ 3 * rSliver ^ 2 := by linarith
    have hM : ((2 * (QMCLeafB.AnchorFactsM2.G₁.n : ℚ) ^ 2
        + 2 * (QMCLeafB.AnchorFactsM2.P₁).dq ^ 2 : ℚ) : ℝ)
        = 8 + 2 * (1 / 380000 : ℝ) ^ 2 := by
      rw [hn1, hdq]; push_cast; ring
    rw [hM]
    have h4 : (3 / 2 : ℝ) * QMCLeafB.BallFloor.frobNormSq Xs
        = 3 + 3 * (1 + 7 / 6080000) ^ 2 := by
      rw [Xs_frobNormSq]; ring
    rw [h4] at hb
    have hr2 : rSliver ^ 2 = (1 / 9120000 : ℝ) ^ 2 := by rw [rSliver]
    rw [hr2] at h3
    have hnum : (0 : ℝ) < (1 / 9120000) ^ 2 := by norm_num
    nlinarith [hb, h3, hnum]

/-! ## 4.  The campaign's own radius at the sliver, and the bit consequence -/

/-- The campaign's `c_A` is the total weight `Rq` (definitionally, `runParamsOfK`), so at `G₁` it is
`2` and the campaign's ball radius `dq/(8·(c_A+1))` is exactly `dq/24 = 1/9120000`. -/
theorem paramsKbc2_cAq (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).cAq = QMCLeafB.EngineRuntime.Rq G := rfl

theorem sliver_campaign_radius :
    (QMCLeafB.AnchorFactsM2.P₁.dq : ℝ)
        / (8 * ((QMCLeafB.AnchorFactsM2.P₁.cAq : ℝ) + 1)) = rSliver := by
  have hdq : (QMCLeafB.AnchorFactsM2.P₁).dq = 1 / 380000 :=
    QMCLeafB.EmptyBodyM5.dq₁_eq
  have hcA : (QMCLeafB.AnchorFactsM2.P₁).cAq = 2 := by
    rw [paramsKbc2_cAq, QMCLeafB.EmptyBodyM5.Rq_G₁]
  rw [hdq, hcA, rSliver]
  norm_num

/-- **The sliver's ball is at the campaign's own radius.** -/
theorem sliver_ball_campaign :
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat Xs)
        ((QMCLeafB.AnchorFactsM2.P₁.dq : ℝ) / (8 * ((QMCLeafB.AnchorFactsM2.P₁.cAq : ℝ) + 1)))
      ⊆ runBall QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
          QMCLeafB.AnchorFactsM2.P₁ := by
  rw [sliver_campaign_radius]
  exact sliver_ball

/-- **At the sliver, no all-false cut stream can satisfy `RunParts`**: the verdict bit is `true`. -/
theorem sliver_bit_true {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      QMCLeafB.AnchorFactsM2.P₁) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
  no_runParts_of_ball QMCLeafB.AnchorFactsM2.hn₁ sliver_ball_campaign B

/-- **THE RESIDUAL FORCES THE CAMPAIGN BIT TRUE AT THE SLIVER.**  `ResidParts` at the campaign bit
supplies `RunParts` at `(G₁, t₁)` (interior, nonempty body), and the ball argument turns any such
run into `campaignBit G₁ t₁ = true`.  Hence a production at the sliver with `ok ≡ false` (the
"`hcert` is vacuous" route) **cannot exist**. -/
theorem campaign_bit_true_at_sliver
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.Audit2M5.campaignBit QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
  sliver_bit_true (H QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
    QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1
    QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2 QMCLeafB.AnchorFactsM2.realBody_G₁)

/-! ## 5.  Sharpness: `dq/16` is the largest admissible radius at `Xs` -/

/-- **The radius `dq/24` is within a factor `3/2` of optimal.**  Any radius above `dq/16` fails:
the all-ones perturbation `-(r/2)·J` has Frobenius norm `r` and pushes the quadratic form at
`x = (1,1)` below the tolerance's floor.  (At `r = dq/16` the two binding slacks — PSD `7dq/16` and
level `dq/8·2 = dq/4` — are exactly spent; `Xs` is the optimal centre.) -/
theorem sliver_ball_sharp {r : ℝ} (hr : 1 / 6080000 < r) :
    ¬ QMCLeafB.BallFloor.matBall Xs r ⊆
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁)
        (-(2 + 5 / 1520000)) (((1 / 380000 : ℚ) : ℝ)) := by
  intro hsub
  set E : Matrix (Fin 2) (Fin 2) ℝ := fun i j => -(r / 2) with hEdef
  have hmem : Xs + E ∈ QMCLeafB.BallFloor.matBall Xs r := by
    have hsub0 : Xs + E - Xs = E := by rw [add_sub_cancel_left]
    show QMCLeafB.BallFloor.frobNormSq (Xs + E - Xs) ≤ r ^ 2
    rw [hsub0]
    have hEval : QMCLeafB.BallFloor.frobNormSq E = 4 * (r / 2) ^ 2 := by
      simp [QMCLeafB.BallFloor.frobNormSq, hEdef, Fin.sum_univ_two]
      ring
    rw [hEval]
    nlinarith
  have hbody := hsub hmem
  have hq := hbody.1 (fun _ : Fin 2 => (1 : ℝ))
  have h1 : QMCLeafB.BallFloor.qfR Xs (fun _ : Fin 2 => (1 : ℝ)) = -(7 / 3040000) := by
    simp [QMCLeafB.BallFloor.qfR, Xs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have h2 : QMCLeafB.BallFloor.qfR E (fun _ : Fin 2 => (1 : ℝ)) = -2 * r := by
    simp [QMCLeafB.BallFloor.qfR, hEdef, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hqf : QMCLeafB.BallFloor.qfR (Xs + E) (fun _ : Fin 2 => (1 : ℝ))
      = -(7 / 3040000) - 2 * r := by
    rw [QMCLeafB.BallFloor.qfR_add, h1, h2]
    ring
  rw [hqf] at hq
  simp [Fin.sum_univ_two] at hq
  linarith

/-! ## 6.  The surviving route is not vacuous: the `ok` certificate at the sliver -/

/-- The rank-one unit-diagonal PSD point `!![1,-1;-1,1]` certifies the `ok` branch at `(G₁, t₁)`:
its objective is `-2`, strictly below the program's level `t₁ + Rq/40000`.  Hence the ball
obstruction does **not** make `RunParts` uninhabited at the sliver — it only forces the run to report
`ok` at least once. -/
theorem sliver_hcert_witness :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁ * X).trace
          ≤ ((QMCLeafB.AnchorFactsM2.t₁ : ℚ) : ℝ)
            + (((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ) := by
  have hpsd : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0 - x 1)]
  refine ⟨!![1, -1; -1, 1], ⟨hpsd, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · have htr : (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁ * !![1, -1; -1, 1]).trace = -2 := by
      rw [Matrix.trace, Fin.sum_univ_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two, QMCLeafB.AnchorFactsM2.wMatrix_G₁_00,
        QMCLeafB.AnchorFactsM2.wMatrix_G₁_11, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
        QMCLeafB.AnchorFactsM2.wMatrix_G₁_10]
      norm_num
    rw [htr]
    have hRq : QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ = 2 :=
      QMCLeafB.EmptyBodyM5.Rq_G₁
    rw [hRq]
    unfold QMCLeafB.AnchorFactsM2.t₁
    norm_num

/-! ## 6b.  The reusable stratum form, and the refutation it yields against a false bit -/

/-- **Any interior point whose run-relaxation carries the campaign's ball has a true bit.**  This is
the stratum-level form of `no_runParts_of_ball` that a producer at any `(G,t)` can consume: it needs
only the ball inclusion into `runBall G t (Pfam G)` — which is a property of `(G,t)`, not of the run.
-/
theorem residParts_bit_true_of_ball
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.PartsM2.ResidParts o Pfam)
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hbody : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((Pfam G).dq : ℚ) : ℝ) X)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((Pfam G).dq / (8 * ((Pfam G).cAq + 1))) ⊆ runBall G t (Pfam G)) :
    o G t = true :=
  no_runParts_of_ball hn hball (H G t hn hlo hhi hbody)

/-- **If the campaign bit is `false` at the sliver, the residual is REFUTED.**  The phase-22/23
record places `(G₁,t₁)` in the `false`-bit (`RefutedSupply`) class; `campaign_bit_true_at_sliver`
says that is incompatible with `ResidParts`.  One of the two must go: either the program's bit is
`true` there (and the sliver is ok-branch work, as `sliver_hcert_witness` shows is possible), or
`ResidParts` at this `campaignBit` is unprovable. -/
theorem residParts_refuted_of_false_bit
    (hbit : QMCLeafB.Audit2M5.campaignBit QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      = false) :
    ¬ Nonempty (QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have h := campaign_bit_true_at_sliver H
  rw [h] at hbit
  exact Bool.noConfusion hbit


end QMCLeafB.BallM2


/-! ## 7.  Axiom audit -/


#print axioms QMCLeafB.BallM2.no_runParts_of_ball
#print axioms QMCLeafB.BallM2.matBall_subset_relaxBodyLE
#print axioms QMCLeafB.BallM2.frobNormSq_add_le
#print axioms QMCLeafB.BallM2.Xs_diag
#print axioms QMCLeafB.BallM2.Xs_qf
#print axioms QMCLeafB.BallM2.Xs_qf_lb
#print axioms QMCLeafB.BallM2.Xs_frob
#print axioms QMCLeafB.BallM2.Xs_frobNormSq
#print axioms QMCLeafB.BallM2.wMatrix_G₁_asum
#print axioms QMCLeafB.BallM2.sliver_matBall
#print axioms QMCLeafB.BallM2.sliver_ball
#print axioms QMCLeafB.BallM2.paramsKbc2_cAq
#print axioms QMCLeafB.BallM2.sliver_campaign_radius
#print axioms QMCLeafB.BallM2.sliver_ball_campaign
#print axioms QMCLeafB.BallM2.sliver_bit_true
#print axioms QMCLeafB.BallM2.campaign_bit_true_at_sliver
#print axioms QMCLeafB.BallM2.sliver_ball_sharp
#print axioms QMCLeafB.BallM2.sliver_hcert_witness
#print axioms QMCLeafB.BallM2.residParts_bit_true_of_ball
#print axioms QMCLeafB.BallM2.residParts_refuted_of_false_bit


