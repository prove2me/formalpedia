-- Prove2me | Definitions.Def_QMCLeafB_budgetarith
-- name    : QMCLeafB_budgetarith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:30:27.224145+00:00
-- url     : https://prove2.me/theorems/d2c655be-9219-4d95-b4a3-fc63c03596eb
-- title:
--   QMCLeafB budgetarith
-- statement:
--   # phase 23, member m8, direction d5 `budget-arithmetic oracle`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_crater
import Definitions.Def_QMCLeafB_btwins
/-
# phase 23, member m8, direction d5 `budget-arithmetic oracle`

Arithmetic at the **one open stratum's own anchor** `(G₁, t₁)` (two vertices, one edge of
weight `1`; `Rq = 2`, `dq = 1/380000`, `ε = 1/20000`, `t₁ = -2 + 71/1520000`), decided exactly
in `ℚ` / `ℝ` and checked by `norm_num` / `nlinarith`.

What is machine-checked here, and why each item is load-bearing:

* **§1 the campaign constants in closed form at the stratum** — `dq₁ = 1/380000`,
  `u₁ = t₁ - ε = -2 - 5/1520000`, the level `u₁ + dq₁/2 = -2 - 3/1520000`, the pinched ceiling
  `n(1 - dq/4) = 2 - 1/760000`, and `ceiling < 23/10`: the *universal* 20-round trace increment
  of `Check_crater_m2.per_round` (machine-checked `≥ 2.3`) strictly exceeds the pinched ceiling by
  more than `3/10` at the stratum's own constants.  So the empty-body escape of `Check_crater_m2`
  is not what kills the drift slot there — the arithmetic kills it at *every* `n = 2` point.

* **§2 the pinch deficit is EXACTLY `dq/4`** — the sharpest form of
  `Check_emptybody_m5.no_pinched_member_G₁`: every pinched matrix (`diag = 1 - dq/4`) that is
  PSD up to `dq/2` has `frob A Q ≥ -2 - dq/2 = (u₁ + dq/2) + dq/4`, i.e. it misses the level by
  precisely `dq/4 = 1/1520000`.  Not "no pinched member" but "short by exactly one `dq/4`": that
  is the width of the repair (level shift or un-pinched test), and it is `1/76` of the leaf slack
  `Rq/40000`, so the ok-side test has room to pay it.

* **§3 the stratum's body carries a trace-`2` point** — `X* = [[1,y],[y,1]]`,
  `y = -(1 + 7dq/16)`, is a genuine member of the REAL relaxed body (`relaxBodyLE`), with strict
  slacks (`psd` margin `dq/16`, level slack `dq/8`, diagonal exactly `1`), and `tr X* = 2`.

* **§4 the reversed (`dM = -1`) body slot is FALSE at every pinched centre** — by
  `Check_btwins_m1.frob_neg_one_sub` the reversed `hbody` asks `tr Q ≥ tr X` for every real body
  point `X`; with `X*` that is `tr Q ≥ 2`, while the pinch gives `tr Q = 2 - dq/2`.  So a
  `dM = -1` re-derivation cannot keep the pinched (queryable) centre: it must also pay for a
  centre whose trace sits *above* the whole body.

* **§5 the genuine separator at the stratum is the trace cut, margin exactly `dq/4`** — the
  oracle's trace branch at the pinched centre is a `RelaxCut` with normal `-A` and margin `dq/4`;
  the production of the cut stream at `(G₁, t₁)`-class points (`RunParts`-direct, no drift slots)
  can be fed by this witness.

House discipline: `set_option autoImplicit false`; a `#print axioms` audit after every
declaration; no proof-escape token of the library discipline; `⊊` is not used.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace QMCLeafB.BudgetArith_M8

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle (frob castMat castMat_apply frob_sub frob_neg_left frob_map)

/-! ## 1.  The campaign constants at the stratum's anchor, in closed form -/

/-- The stratum's input: two vertices, one edge of weight `1` (`Rq = 2`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The campaign parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁

/-- The stratum's interior threshold. -/
abbrev t₁ : ℚ := -(2 : ℚ) + 71 / 1520000

/-- The oracle tolerance at the stratum: `dqShallow G₁ = (Rq/40000)/(9·Rq + 1)`. -/
abbrev dq₁ : ℚ := 1 / 380000

/-- The body's threshold level `u = t₁ - ε`. -/
abbrev u₁ : ℚ := t₁ - 1 / 20000

theorem dq₁_param : P₁.dq = dq₁ := QMCLeafB.EmptyBodyM5.dq₁_eq

theorem eps₁_param : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁

theorem u₁_eq : u₁ = -(2 : ℚ) - 5 / 1520000 := by
  unfold u₁ t₁; norm_num

/-- **The level the body is taken at**: `u₁ + dq₁/2 = -2 - 3/1520000`. -/
theorem level₁ : u₁ + dq₁ / 2 = -(2 : ℚ) - 3 / 1520000 := by
  unfold u₁ t₁ dq₁; norm_num

/-- **The pinched ceiling at the stratum**: `n(1 - dq/4) = 2 - 1/760000`. -/
theorem ceiling₁ : (1 - dq₁ / 4) * (2 : ℚ) = 2 - 1 / 760000 := by
  unfold dq₁; norm_num

/-- **The ceiling is strictly below the universal 20-round increment bound `23/10`** (the bound
`Check_crater_m2.sum_lb` proves for every normal/margin stream at `n² = 4`, `rmax = 1/16`).  The
margin is `3/10`, independent of the body being empty. -/
theorem ceiling_lt_drift : ((1 - dq₁ / 4 : ℚ) : ℝ) * (G₁.n : ℝ) < 23 / 10 := by
  have hn : G₁.n = 2 := rfl
  have hd : ((dq₁ : ℚ) : ℝ) = 1 / 380000 := by unfold dq₁; norm_num
  rw [hn]
  push_cast
  nlinarith

/-! ## 2.  The pinch deficit is exactly `dq/4` -/

/-- **The pinched PSD floor**: a matrix whose diagonal is pinned to `1 - dq/4` and which is
PSD up to `dq/2` has `⟪A, Q⟫ ≥ -2 - dq/2` — the `x = (1,1)` test of the PSD margin, `A = wMatrixQ
G₁` having off-diagonal `1` and zero diagonal (`EmptyBodyM5.frob_ge_of_pinched` with the trace slot
dropped, since only `x = (1,1)` is used). -/
theorem pinch_floor (Q : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i, Q i i = 1 - dq₁ / 4)
    (hpsd : ∀ x : Fin 2 → ℚ, -(dq₁ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf Q x) :
    -(2 + dq₁ / 2) ≤ frob (QMCLeafB.Finalization.wMatrixQ G₁) Q := by
  have h1 := hpsd (fun _ : Fin 2 => (1 : ℚ))
  have hsq : (∑ i : Fin 2, ((1 : ℚ)) ^ 2) = 2 := by norm_num
  have hqf : QMCLeafB.SepOracle.qf Q (fun _ : Fin 2 => (1 : ℚ))
      = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  rw [hsq, hqf] at h1
  have hfrob : frob (QMCLeafB.Finalization.wMatrixQ G₁) Q = Q 0 1 + Q 1 0 := by
    simp [frob, Fin.sum_univ_two, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00,
      QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10,
      QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11]
  have hd0 := hdiag 0
  have hd1 := hdiag 1
  rw [hfrob]
  unfold dq₁ at hd0 hd1 ⊢
  nlinarith

/-- **The deficit is exactly `dq/4`**: the pinched floor `-2 - dq/2` sits `dq/4` *above* the
body's level `u₁ + dq₁/2`.  (Not merely "no pinched member": short by exactly one `dq/4`.) -/
theorem pinch_deficit : -(2 + dq₁ / 2) = (u₁ + dq₁ / 2) + dq₁ / 4 := by
  rw [level₁]; unfold dq₁; norm_num

/-- The deficit as a number: `dq/4 = 1/1520000`. -/
theorem pinch_deficit_value : dq₁ / 4 = 1 / 1520000 := by
  unfold dq₁; norm_num

/-- **The repair width against the leaf's slack**: `dq/4` is `1/76` of the slack
`Rq G₁/40000 = 1/20000`.  A level shift of `dq/4` on the ok side costs `1/76` of the slack. -/
theorem deficit_vs_slack : dq₁ / 4 = (1 / 20000) / 76 := by
  unfold dq₁; norm_num

/-! ## 3.  The stratum's body carries a trace-`2` point -/

/-- A genuine point of the stratum's relaxed body with unit diagonal: `[[1,y],[y,1]]`,
`y = -(1 + 7·dq/16)`.  Its PSD margin is `dq/16`, its level slack `dq/8`. -/
def Xstar : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 1 else -(1 + 7 / 6080000)

theorem Xstar_diag : ∀ i, Xstar i i = 1 := by
  intro i; simp [Xstar]

theorem Xstar_trace : ∑ i, Xstar i i = 2 := by
  rw [Fin.sum_univ_two]; norm_num [Xstar]

theorem Xstar_qf (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xstar x
      = x 0 ^ 2 + x 1 ^ 2 - 2 * (1 + 7 / 6080000) * (x 0 * x 1) := by
  simp [QMCLeafB.BallFloor.qfR, Xstar, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **`X*` is a member of the REAL relaxed body at `(G₁, t₁)`** (all three inequalities), with the
PSD slack `dq/16` and the level slack `dq/8` both strict. -/
theorem Xstar_mem :
    QMCLeafB.BallFloor.relaxBodyLE (castMat (QMCLeafB.Finalization.wMatrixQ G₁))
      ((u₁ : ℚ) : ℝ) ((dq₁ : ℚ) : ℝ) Xstar := by
  have hd : ((dq₁ : ℚ) : ℝ) = 1 / 380000 := by unfold dq₁; norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [Xstar_qf, hd, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 - x 1)]
  · intro i
    rw [Xstar_diag i, hd]
    norm_num
  · have hf : QMCLeafB.BallFloor.frob (castMat (QMCLeafB.Finalization.wMatrixQ G₁)) Xstar
        = 2 * (-(1 + 7 / 6080000)) := by
      simp [QMCLeafB.BallFloor.frob, QMCLeafB.SepOracle.castMat_apply, Xstar, Fin.sum_univ_two,
        QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
        QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11] <;> norm_num
    rw [hf, u₁_eq, hd]
    norm_num

/-! ## 4.  The reversed (`dM = -1`) body slot is FALSE at every pinched centre -/

/-- **`dM = -1` cannot live at a pinched centre.**  The reversed body slot
(`Check_btwins_m1.frob_neg_one_sub`) asks a centre `Q` to sit *above* the whole real body in
trace: `(∑ i, Q i i) - ∑ i, X i i ≥ 0` for every body point `X`.  At the stratum the body contains
`X*` with `tr X* = 2`, while every pinched centre has `tr Q = 2 - dq/2 < 2`: the reversed slot is
violated by exactly `dq/2`, at *every* pinched (hence every queryable) centre. -/
theorem not_reversed_hbody_pinch (Q : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i, Q i i = 1 - dq₁ / 4) :
    ¬ (∀ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (castMat (QMCLeafB.Finalization.wMatrixQ G₁))
          ((u₁ : ℚ) : ℝ) ((dq₁ : ℚ) : ℝ) X →
        0 ≤ QMCLeafB.SepOracle.frob (castMat (-1 : Matrix (Fin 2) (Fin 2) ℚ))
          (X - castMat Q)) := by
  intro h
  have hX := h Xstar Xstar_mem
  rw [QMCLeafB.BTwins_M1.frob_neg_one_sub] at hX
  have hQ : ∑ i, ((Q i i : ℚ) : ℝ) = 2 - ((dq₁ : ℚ) : ℝ) / 2 := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hXtr : ∑ i, Xstar i i = 2 := Xstar_trace
  rw [hQ, hXtr] at hX
  have hd : ((dq₁ : ℚ) : ℝ) = 1 / 380000 := by unfold dq₁; norm_num
  rw [hd] at hX
  norm_num at hX

/-! ## 5.  The genuine separator at the stratum: the trace cut, margin exactly `dq/4` -/

/-- **The trace cut at the pinched centre separates the whole real relaxed body** with margin
exactly `dq/4`: `⟪-A, X - Q⟫ ≥ dq/4` for every member `X`.  This is the stratum's genuine violated
direction (the oracle's `trace` branch), and it is what a `RunParts`-direct production of the cut
stream at `(G₁, t₁)`-class points can record. -/
def traceCut_pinched (Q : Matrix (Fin 2) (Fin 2) ℚ)    (hdiag : ∀ i, Q i i = 1 - dq₁ / 4)
    (hpsd : ∀ x : Fin 2 → ℚ, -(dq₁ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf Q x) :
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G₁) Q u₁ dq₁ where
  normal := -(QMCLeafB.Finalization.wMatrixQ G₁)
  margin := dq₁ / 4
  margin_pos := by unfold dq₁; norm_num
  separates := by
    intro X hX
    obtain ⟨-, -, hlev⟩ := hX
    have hfloor := pinch_floor Q hdiag hpsd
    have hcast : frob (castMat (QMCLeafB.Finalization.wMatrixQ G₁)) (castMat Q)
        = ((frob (QMCLeafB.Finalization.wMatrixQ G₁) Q : ℚ) : ℝ) := by
      simp [frob, QMCLeafB.SepOracle.castMat_apply, Fin.sum_univ_two] <;> push_cast <;> ring
    have hneg : castMat (-(QMCLeafB.Finalization.wMatrixQ G₁))
        = -(castMat (QMCLeafB.Finalization.wMatrixQ G₁)) := by
      ext a b
      simp [QMCLeafB.SepOracle.castMat_apply]
    have hf' : ((-(2 + dq₁ / 2) : ℚ) : ℝ)
        ≤ ((frob (QMCLeafB.Finalization.wMatrixQ G₁) Q : ℚ) : ℝ) := by
      exact_mod_cast hfloor
    rw [hneg, frob_neg_left, frob_sub, hcast]
    have hlev' : frob (castMat (QMCLeafB.Finalization.wMatrixQ G₁)) X
        ≤ ((u₁ : ℚ) : ℝ) + ((dq₁ : ℚ) : ℝ) / 2 := hlev
    push_cast at hlev' hf' ⊢
    linarith

#print axioms QMCLeafB.BudgetArith_M8.u₁_eq
#print axioms QMCLeafB.BudgetArith_M8.level₁
#print axioms QMCLeafB.BudgetArith_M8.ceiling₁
#print axioms QMCLeafB.BudgetArith_M8.ceiling_lt_drift
#print axioms QMCLeafB.BudgetArith_M8.pinch_floor
#print axioms QMCLeafB.BudgetArith_M8.pinch_deficit
#print axioms QMCLeafB.BudgetArith_M8.pinch_deficit_value
#print axioms QMCLeafB.BudgetArith_M8.deficit_vs_slack
#print axioms QMCLeafB.BudgetArith_M8.Xstar_diag
#print axioms QMCLeafB.BudgetArith_M8.Xstar_trace
#print axioms QMCLeafB.BudgetArith_M8.Xstar_qf
#print axioms QMCLeafB.BudgetArith_M8.Xstar_mem
#print axioms QMCLeafB.BudgetArith_M8.not_reversed_hbody_pinch
#print axioms QMCLeafB.BudgetArith_M8.traceCut_pinched

end QMCLeafB.BudgetArith_M8


