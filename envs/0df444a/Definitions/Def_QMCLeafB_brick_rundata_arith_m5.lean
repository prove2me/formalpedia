-- Prove2me | Definitions.Def_QMCLeafB_brick_rundata_arith_m5
-- name    : QMCLeafB_brick_rundata_arith_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:56:52.568768+00:00
-- url     : https://prove2.me/theorems/99d9cbc1-807b-40e8-8925-ec1f8c8159aa
-- title:
--   QMCLeafB brick_rundata_arith_m5
-- statement:
--   # leaf B phase 13 — brick `rundata-arith` (swarm `smw17fqzz`, member m5, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_ClosingBracket
/-
# leaf B phase 13 — brick `rundata-arith` (swarm `smw17fqzz`, member m5, direction d8)

The closing stroke of the leaf is

    QMCLeafB.VerdictSound.solution_of_loop_via_runData (init fuel round verdict … o hspec hd)

with `hd : ∀ G t, 2 ≤ G.n → -Rq G ≤ t → t ≤ 0 → RunData o G t`.  `RunData` has eight *scalar*
slots (`K m dq cAq rmax del` and the two budget/halving inequalities over them) and a fixed list of
*run* slots (`ok cd` and the per-round facts about them).  This brick removes the scalar half:

* §1 trace bounds — `|wMatrix G i j| ≤ Rq G` and `∑ᵢⱼ |wMatrix G i j| ≤ (n² · Rq G : ℚ)`, i.e. an
  explicit ledger constant `cAqOf G` for `RunData.hcAq`/`hAsum`.  Nothing analytic: `Rq G = 2 ∑ e, w e`
  and every entry of `wMatrix G` is a single weight.
* §2 the assembled run's scalars: `dqOf = 1`, `cAqOf G = (n·n) · Rq G`, `rmaxOf = 0`, `mOf G = 4 n²`
  and `K = runK G dq cAq m k0`, with the two close-form inequalities *proved*:
  `runK_budget` (from `ClosingBracket.runData_hbudget_close`, padded by `k0` extra rounds) and
  `halveOf` (from `ClosingBracket.runData_hhalve_close`).
* §3 `rundata_of_run` — the whole `RunData` record at those scalars from exactly the run:
  the cut sequence `cd`, the margins `del`, the `ok` bits, and four analytic facts
  (`hcert` the feasible round's witness, `hcut` the separation contract, plus the ledger facts).
  No scalar slot is left to the caller.
* §4 `rundata_allOk` — the special case in which **no cut round is needed**: if a feasible point at
  the threshold exists, the run can report `ok` at every round, and `RunData` is then a theorem with
  no further hypotheses (all cut-side fields are vacuous).  `soundAt_allOk` feeds it to
  `VerdictSound.soundAt_of_runData`.
* §5 `soundAt_of_witness_or_floor` — the shape the two assembled branches take: a `SoundAt` needs
  only "verdict `true` ⇒ a witness" and "verdict `false` ⇒ below the floor".
* §6 axiom audit.

No `sorry`, no `axiom`, no edits to existing files; `set_option autoImplicit false` throughout.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false

namespace QMCLeafB.RundataArith

open QuantumMaxCutEnergy

/-! ## 1.  The ledger constant `cAq` is free

`RunData` asks for a rational `cAq ≥ 0` with `∑ᵢⱼ |wMatrix G i j| ≤ cAq`.  `Rq G = 2 ∑ e, w e`, and
every entry of `wMatrix G` is one weight, so `n² · Rq G` is a valid explicit choice. -/

/-- `Rq` in terms of the weights, over `ℝ`. -/
theorem Rq_eq (G : Input) :
    ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) = 2 * ∑ e, (G.weights e : ℝ) := by
  rw [QMCLeafB.EngineRuntime.Rq]
  push_cast
  rfl

theorem Rq_nonneg (G : Input) : 0 ≤ QMCLeafB.EngineRuntime.Rq G := by
  have h : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) = 2 * ∑ e, (G.weights e : ℝ) := Rq_eq G
  have h2 : (0 : ℝ) ≤ 2 * ∑ e, (G.weights e : ℝ) := by
    have h3 : (0 : ℝ) ≤ ∑ e, (G.weights e : ℝ) :=
      Finset.sum_nonneg fun e _ => by positivity
    linarith
  have h4 : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by rw [h]; exact h2
  exact_mod_cast h4

/-- Every entry of the w-matrix is at most `Rq`. -/
theorem wMatrix_abs_le_Rq (G : Input) (i j : Fin G.n) :
    |QMCLeafB.wMatrix G i j| ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
  have hterm : ∀ e : Edge G.n,
      (G.weights e : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
    intro e
    have h1 : (G.weights e : ℝ) ≤ ∑ e', (G.weights e' : ℝ) :=
      Finset.single_le_sum (f := fun e => (G.weights e : ℝ))
        (fun e _ => by positivity) (Finset.mem_univ e)
    have h2 : (0 : ℝ) ≤ ∑ e', (G.weights e' : ℝ) :=
      Finset.sum_nonneg fun e _ => by positivity
    have h3 := Rq_eq G
    rw [h3]; linarith
  rw [QMCLeafB.wMatrix]
  simp only [Matrix.of_apply]
  split_ifs with h1 h2
  · rw [abs_of_nonneg (show (0 : ℝ) ≤ (G.weights ⟨(i, j), h1⟩ : ℝ) by positivity)]
    exact hterm _
  · rw [abs_of_nonneg (show (0 : ℝ) ≤ (G.weights ⟨(j, i), h2⟩ : ℝ) by positivity)]
    exact hterm _
  · rw [abs_zero]
    have := Rq_nonneg G
    exact_mod_cast this

/-- **The `hAsum` slot at an explicit constant.** -/
theorem sum_abs_wMatrix_le (G : Input) :
    ∑ i, ∑ j, |QMCLeafB.wMatrix G i j|
      ≤ ((((G.n * G.n : ℕ) : ℚ) * QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
  calc ∑ i, ∑ j, |QMCLeafB.wMatrix G i j|
      ≤ ∑ i : Fin G.n, ∑ _j : Fin G.n, ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => wMatrix_abs_le_Rq G i j
    _ = ((((G.n * G.n : ℕ) : ℚ) * QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, Nat.cast_mul, nsmul_eq_mul]
        ring

/-! ## 2.  The assembled run's scalars

`RunData` never fixes the numbers `dq cAq rmax m K`: any choice with the two close-form inequalities
works.  We take `dq = 1` (the smallest legal oracle tolerance), `cAq = n²·Rq G` (§1),
`rmax = 0` and `m = 4n²` — the constants `Check_ClosingBracket` closes the halving inequality at.
`K` is the shelf's own `simRounds`, padded by an arbitrary `k0` extra rounds so that the caller can
force `0 < K·m` (the `anyOk`-true case of §4 needs it).  Padded rounds never hurt: shrinking the
potential by more halvings only makes the budget inequality easier. -/

/-- the ledger constant of the assembled run -/
noncomputable def cAqOf (G : Input) : ℚ :=
  ((G.n * G.n : ℕ) : ℚ) * QMCLeafB.EngineRuntime.Rq G

theorem cAqOf_nonneg (G : Input) : 0 ≤ cAqOf G := by
  unfold cAqOf
  exact mul_nonneg (by positivity) (Rq_nonneg G)

/-- the relaxation cap fixed by `RunData`'s own shape -/
def capOf (G : Input) (dq : ℚ) : ℚ := 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2

theorem capOf_pos (G : Input) (dq : ℚ) (hdq : 0 < dq) : 0 < capOf G dq := by
  unfold capOf
  have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
  have h2 : (0 : ℚ) < dq ^ 2 := by positivity
  linarith

/-- the initial potential of the assembled run -/
noncomputable def volOf (G : Input) (dq : ℚ) : ℝ :=
  QMCLeafB.EngineIterates.volPot (G.n * G.n)
    (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (capOf G dq))

theorem volOf_nonneg (G : Input) (dq : ℚ) : 0 ≤ volOf G dq := by
  unfold volOf QMCLeafB.EngineIterates.volPot
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- the ledger slack of the assembled run -/
noncomputable def epsOf (dq cAq : ℚ) : ℝ := (dq : ℝ) / (8 * ((cAq : ℝ) + 1))

/-- the round count of the assembled run: the shelf's `simRounds`, plus `k0` spare rounds -/
noncomputable def runK (G : Input) (dq cAq : ℚ) (m k0 : ℕ) : ℕ :=
  QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m + k0

/-- **`hbudget` at the assembled scalars, for any number of spare rounds.** -/
theorem runK_budget (G : Input) (dq cAq : ℚ) (hdq : 0 < dq) (hcAq : 0 ≤ cAq)
    {m : ℕ} (hm1 : 1 ≤ m) (k0 : ℕ) :
    volOf G dq * (1 / 2) ^ runK G dq cAq m k0 < (epsOf dq cAq) ^ (G.n * G.n) := by
  have hbase := QMCLeafB.ClosingBracket.runData_hbudget_close G.n (capOf G dq)
    (capOf_pos G dq hdq) dq cAq hdq hcAq hm1
  have hΦ : (0 : ℝ) ≤ volOf G dq := volOf_nonneg G dq
  have hhalf : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m :=
    by positivity
  have hk : (1 / 2 : ℝ) ^ k0 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsplit : (1 / 2 : ℝ) ^ runK G dq cAq m k0
      = (1 / 2 : ℝ) ^ QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m
        * (1 / 2 : ℝ) ^ k0 := by
    rw [runK, pow_add]
  calc volOf G dq * (1 / 2) ^ runK G dq cAq m k0
      = volOf G dq * ((1 / 2 : ℝ) ^ QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m
          * (1 / 2 : ℝ) ^ k0) := by rw [hsplit]
    _ = (volOf G dq * (1 / 2 : ℝ) ^ QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m)
          * (1 / 2 : ℝ) ^ k0 := by ring
    _ ≤ (volOf G dq * (1 / 2 : ℝ) ^ QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m)
          * 1 := by
        exact mul_le_mul_of_nonneg_left hk (mul_nonneg hΦ hhalf)
    _ = volOf G dq * (1 / 2 : ℝ) ^ QMCLeafB.SimLoop.simRounds G.n (volOf G dq) (epsOf dq cAq) m := by
        ring
    _ < (epsOf dq cAq) ^ (G.n * G.n) := hbase

/-! ## 3.  The whole `RunData` at the assembled scalars

The caller supplies the run (`ok`, `cd`, `del`) and the facts about it; every scalar slot, the
`hAsum` ledger constant and both close-form inequalities are discharged here. -/

/-- **`RunData` from a run, at the assembled scalars.**  What is left as hypothesis is exactly the
run itself: the feasible round's witness (`hcert`), the separation contract on the cut rounds
(`hcut`), the ledger facts (`hwit hrho hcne hdel0 hcheck`), the shallow-regime ceiling, and the
verdict equation. -/
noncomputable def rundata_of_run
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ)
    (dq : ℚ) (hdq : 0 < dq) (cAq : ℚ) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |QMCLeafB.wMatrix G i j| ≤ (cAq : ℝ))
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (k0 : ℕ)
    (ok : ℕ → Bool) (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hcert : ∀ k, k < runK G dq cAq m k0 * m → ok k = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace
            ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
    (hwit : ∀ k, k < runK G dq cAq m k0 * m → ok k = false →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (capOf G dq)) cd k *ᵥ (cd k).p
        = (cd k).c)
    (hrho : ∀ k, k < runK G dq cAq m k0 * m → ok k = false → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < runK G dq cAq m k0 * m → ok k = false → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < runK G dq cAq m k0 * m → ok k = false → 0 ≤ del k)
    (hcheck : ∀ k, k < runK G dq cAq m k0 * m → ok k = false →
      (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hcut : ∀ k, k < runK G dq cAq m k0 * m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (dq : ℝ)
          ((capOf G dq : ℚ) : ℝ) →
        -(((del k : ℚ)) : ℝ)
          ≤ QMCLeafB.EngineIterates.cutCR cd k
              ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ) cd k))
    (hle : ∀ k, k < runK G dq cAq m k0 * m → ok k = false → (cd k).rho ≤ rmax)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (runK G dq cAq m k0 * m)) :
    QMCLeafB.VerdictSound.RunData o G t where
  K := runK G dq cAq m k0
  m := m
  ok := ok
  cd := cd
  dq := dq
  cAq := cAq
  rmax := rmax
  del := del
  hdq := hdq
  hcAq := hcAq
  hAsum := hAsum
  hcert := hcert
  hwit := hwit
  hrho := hrho
  hcne := hcne
  hdel0 := hdel0
  hcheck := hcheck
  hcut := hcut
  hrmax := hrmax
  hle := hle
  hhalve := hhalve
  hbudget := runK_budget G dq cAq hdq hcAq hm1 k0
  hverdict := hverdict

/-! ## 4.  A run with no cut rounds

If some unit-diagonal semidefinite `X` already meets the threshold, the loop can report `ok` at
every round: all the cut-side fields of `RunData` are vacuous, and the record becomes a theorem with
that witness as its only input.  This is the assembled shape on the part of the bracket where a
point at the threshold is known. -/

theorem mOf_ge_one (G : Input) (hn : 2 ≤ G.n) : 1 ≤ 4 * (G.n * G.n) := by
  have : 2 ≤ G.n * G.n := by nlinarith
  omega

theorem halveOf (G : Input) (hn : 2 ≤ G.n) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((0 : ℚ) : ℝ)))⁻¹ ^ (4 * (G.n * G.n))
      ≤ 1 / 2 := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  simpa using QMCLeafB.ClosingBracket.runData_hhalve_close (G.n * G.n) hN

/-- **`RunData` with no cut round.**  Inputs: a feasible point at the threshold, and the verdict bit
`true`.  Everything else — the oracle tolerance, the ledger constant, the cap, the round count, both
close-form inequalities — is discharged at explicit constants. -/
noncomputable def rundata_allOk (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hwitw : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
    (hbit : o G t = true) :
    QMCLeafB.VerdictSound.RunData o G t := by
  have hm1 : 1 ≤ 4 * (G.n * G.n) := mOf_ge_one G hn
  have hT : 0 < runK G (1 : ℚ) (cAqOf G) (4 * (G.n * G.n)) 1 * (4 * (G.n * G.n)) := by
    have hk : 1 ≤ runK G (1 : ℚ) (cAqOf G) (4 * (G.n * G.n)) 1 := by
      unfold runK
      omega
    exact Nat.mul_pos (by omega) (by omega)
  refine rundata_of_run o G t (1 : ℚ) (by norm_num) (cAqOf G) (cAqOf_nonneg G)
    (sum_abs_wMatrix_le G) 0 (le_refl 0) (4 * (G.n * G.n)) hm1 (halveOf G hn) 1
    (fun _ => true) (fun _ => ⟨(0 : Fin (G.n * G.n) → ℚ), 0, 0⟩) (fun _ => 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k _ _
    exact hwitw
  · intro k _ hk
    exact absurd hk (by simp)
  · intro k _ hk
    exact absurd hk (by simp)
  · intro k _ hk
    exact absurd hk (by simp)
  · intro k _ hk
    exact absurd hk (by simp)
  · intro k _ hk
    exact absurd hk (by simp)
  · intro k _ hk
    exact absurd hk (by simp)
  · intro k _ hk
    exact absurd hk (by simp)
  · -- the verdict equation: `anyOk (fun _ => true) T = true` for `T > 0`
    rw [hbit]
    exact ((QMCLeafB.SimLoop.anyOk_eq_true_iff (fun _ => true) _).mpr ⟨0, hT, rfl⟩).symm

/-- **A `SoundAt` with no cut round.**  `rundata_allOk` fed to the closing stroke's own soundness
step. -/
theorem soundAt_allOk (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hwitw : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
    (hbit : o G t = true) :
    QMCLeafB.VerdictSound.SoundAt o G t :=
  QMCLeafB.VerdictSound.soundAt_of_runData o G t hn (rundata_allOk o G t hn hwitw hbit)

/-! ## 5.  The two-clause shape of an assembled `SoundAt`

Whatever the run eventually looks like, the `SoundAt` it produces has exactly this form: on a
`true` verdict a witness at the threshold, on a `false` verdict the trivial floor.  Recording it here
fixes the obligation any `hd`-provider has to meet, split in the two branches. -/

/-- **A `SoundAt` from a witness-or-floor decision.** -/
theorem soundAt_of_witness_or_floor (o : Input → ℚ → Bool) (G : Input) (t : ℚ)
    (hwit : o G t = true → ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
    (hfloor : o G t = false →
      (t : ℝ) ≤ -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.VerdictSound.SoundAt o G t :=
  ⟨hwit, fun hf => QMCLeafB.VerdictSound.soundAt_false_of_le_floor o G t hf (hfloor hf)⟩

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.RundataArith.Rq_eq
#print axioms QMCLeafB.RundataArith.Rq_nonneg
#print axioms QMCLeafB.RundataArith.wMatrix_abs_le_Rq
#print axioms QMCLeafB.RundataArith.sum_abs_wMatrix_le
#print axioms QMCLeafB.RundataArith.cAqOf_nonneg
#print axioms QMCLeafB.RundataArith.capOf_pos
#print axioms QMCLeafB.RundataArith.volOf_nonneg
#print axioms QMCLeafB.RundataArith.runK_budget
#print axioms QMCLeafB.RundataArith.mOf_ge_one
#print axioms QMCLeafB.RundataArith.halveOf
#print axioms QMCLeafB.RundataArith.rundata_allOk
#print axioms QMCLeafB.RundataArith.soundAt_allOk
#print axioms QMCLeafB.RundataArith.soundAt_of_witness_or_floor

end QMCLeafB.RundataArith


