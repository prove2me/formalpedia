-- Prove2me | Definitions.Def_QMCLeafB_sliver2
-- name    : QMCLeafB_sliver2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:27:33.290206+00:00
-- url     : https://prove2.me/theorems/f4b51a3e-986c-4238-9a1c-820cb47ff6d5
-- title:
--   QMCLeafB sliver2
-- statement:
--   # leaf B phase 20 — brick `sliver, unconditional` (swarm `smw1kspvn`, member m8, direction d10)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sliver
/-
# leaf B phase 20 — brick `sliver, unconditional` (swarm `smw1kspvn`, member m8, direction d10)

`Check_sliver_m8.no_witness_at_bottom` proves that at the bottom of the bracket `t = -Rq G` the
witness slot of `VerdictOkM8.bundleH_of_verdict_true` is unsatisfiable, but takes the trivial bound
`-Rq G ≤ frob (wMatrixQ G) X` as a hypothesis.  This file discharges it:

* §1 `qf_two`: the quadratic form at a two-point vector, `a²Xᵢᵢ + ab Xᵢⱼ + ba Xⱼᵢ + b²Xⱼⱼ`;
* §2 `abs_entry_le_of_psd`: exact PSD + the diagonal band give `|Xᵢⱼ| ≤ 1 + dq/4`
  (from `qf X (eᵢ+eⱼ) ≥ 0` and `qf X (eᵢ-eⱼ) ≥ 0`, no 2x2 minor needed);
* §3 the weight matrix: entrywise nonnegative and `∑ᵢⱼ (wMatrixQ G)ᵢⱼ = Rq G`;
* §4 `frob_lower_bound`: `-(1 + dq/4)·Rq G ≤ frob (wMatrixQ G) X`;
* §5 the unconditional no-witness theorem at `t = -Rq G`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Sliver2M8

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle

/-! ## 1.  The quadratic form at a two-point vector -/

theorem qf_two {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) {i j : Fin n} (hij : i ≠ j) (a b : ℚ) :
    qf X (fun k => if k = i then a else if k = j then b else 0)
      = a ^ 2 * X i i + a * b * X i j + b * a * X j i + b ^ 2 * X j j := by
  set v : Fin n → ℚ := fun k => if k = i then a else if k = j then b else 0 with hv
  have hvi : v i = a := by simp [hv]
  have hvj : v j = b := by simp [hv, Ne.symm hij]
  have hv0 : ∀ k, k ≠ i → k ≠ j → v k = 0 := by
    intro k h1 h2
    simp only [hv]
    rw [if_neg h1, if_neg h2]
  have hinner : ∀ p : Fin n, (∑ q, v p * (X p q * v q))
      = v p * (X p i * v i) + v p * (X p j * v j) := by
    intro p
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun q => v p * (X p q * v q)) (Finset.mem_univ i)]
    rw [Finset.sum_eq_single j]
    · intro b hb hbj
      have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
      rw [hv0 b hbi hbj]
      ring
    · intro h
      exact absurd (by simp [Ne.symm hij]) h
  rw [qf_eq_sum]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
    (fun p => ∑ q, v p * (X p q * v q)) (Finset.mem_univ i)]
  rw [hinner i, Finset.sum_eq_single j]
  · rw [hinner j, hvi, hvj]
    ring
  · intro b hb hbj
    have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
    rw [hinner b, hv0 b hbi hbj]
    ring
  · intro h
    exact absurd (by simp [Ne.symm hij]) h

#print axioms QMCLeafB.Sliver2M8.qf_two

/-! ## 2.  The entry bound from exact PSD and the band -/

/-- **`|Xᵢⱼ| ≤ 1 + dq/4`.**  From `qf X (eᵢ+eⱼ) ≥ 0` and `qf X (eᵢ-eⱼ) ≥ 0`. -/
theorem abs_entry_le_of_psd {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} {DQ : ℚ}
    (hDQ4 : DQ ≤ 4) (hXsym : Xᵀ = X)
    (hXband : ∀ i, |X i i - 1| ≤ DQ / 4)
    (hXpsd : ∀ x : Fin n → ℚ, 0 ≤ qf X x) (i j : Fin n) :
    |X i j| ≤ 1 + DQ / 4 := by
  have hsym : ∀ a b : Fin n, X a b = X b a := fun a b => by
    have h := congrFun (congrFun hXsym b) a
    rwa [Matrix.transpose_apply] at h
  have hdiag : ∀ a : Fin n, X a a ≤ 1 + DQ / 4 := by
    intro a
    have h := abs_le.mp (hXband a)
    linarith [h.2]
  have hdiag' : ∀ a : Fin n, 1 - DQ / 4 ≤ X a a := by
    intro a
    have h := abs_le.mp (hXband a)
    linarith [h.1]
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg]
    · exact hdiag i
    · linarith [hdiag' i, hDQ4]
  · have h1 := hXpsd (fun k => if k = i then 1 else if k = j then 1 else 0)
    have h2 := hXpsd (fun k => if k = i then 1 else if k = j then -1 else 0)
    rw [qf_two X hij 1 1] at h1
    rw [qf_two X hij 1 (-1)] at h2
    have hsij : X j i = X i j := (hsym i j).symm
    rw [abs_le]
    constructor <;> nlinarith [h1, h2, hdiag i, hdiag j, hsij]

#print axioms QMCLeafB.Sliver2M8.abs_entry_le_of_psd

/-! ## 3.  The weight matrix: nonnegative entries, total `Rq` -/

/-- **`wMatrixQ G` is entrywise nonnegative.** -/
theorem wMatrixQ_nonneg (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    0 ≤ QMCLeafB.Finalization.wMatrixQ G i j := by
  rw [QMCLeafB.Finalization.wMatrixQ_apply]
  split_ifs with h1 h2
  · exact_mod_cast (G.weights ⟨(i, j), h1⟩).2
  · exact_mod_cast (G.weights ⟨(j, i), h2⟩).2
  · norm_num

#print axioms QMCLeafB.Sliver2M8.wMatrixQ_nonneg

/-- **The total mass of the weight matrix is `Rq`**: `∑ᵢⱼ (wMatrixQ G)ᵢⱼ = Rq G`. -/
theorem sum_wMatrixQ (G : QuantumMaxCutEnergy.Input) :
    ∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j
      = QMCLeafB.EngineRuntime.Rq G := by
  have hcast : ((∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j : ℚ) : ℝ)
      = ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
    push_cast
    rw [← QMCLeafB.EngineRuntime.Rq_cast]
    rw [show QMCLeafB.V (QMCLeafB.wMatrix G) = ∑ i, ∑ j, QMCLeafB.wMatrix G i j from rfl]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← QMCLeafB.CastBridge.castM_apply, ← QMCLeafB.Finalization.wMatrix_castM]
  exact_mod_cast hcast

#print axioms QMCLeafB.Sliver2M8.sum_wMatrixQ

/-! ## 4.  The trivial lower bound on the objective -/

/-- **`-(1 + dq/4)·Rq ≤ frob (wMatrixQ G) X`** at a band-PSD point. -/
theorem frob_lower_bound {G : QuantumMaxCutEnergy.Input}
    (X : Matrix (Fin G.n) (Fin G.n) ℚ) {DQ : ℚ}
    (hDQ4 : DQ ≤ 4) (hXsym : Xᵀ = X) (hXband : ∀ i, |X i i - 1| ≤ DQ / 4)
    (hXpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf X x) :
    (-(1 + DQ / 4)) * QMCLeafB.EngineRuntime.Rq G
      ≤ QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) X := by
  have hentry : ∀ i j : Fin G.n, -(1 + DQ / 4) ≤ X i j := by
    intro i j
    have h := abs_le.mp (abs_entry_le_of_psd hDQ4 hXsym hXband hXpsd i j)
    linarith [h.1]
  have hstep : (-(1 + DQ / 4)) * (∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j)
      ≤ ∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j * X i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ?_)
    have h1 : 0 ≤ QMCLeafB.Finalization.wMatrixQ G i j := wMatrixQ_nonneg G i j
    have h2 : -(1 + DQ / 4) ≤ X i j := hentry i j
    nlinarith
  rw [sum_wMatrixQ] at hstep
  simpa [QMCLeafB.SepOracle.frob] using hstep

#print axioms QMCLeafB.Sliver2M8.frob_lower_bound

/-! ## 5.  The unconditional sliver theorem -/

/-- **`dqShallow·(Rq/4 + 1/2) < eps`** — the slack the witness slot would need at `t = -Rq`,
strengthened from `Check_sliver_m8`'s `dqShallow/2 < eps` to the `(1 + dq/4)·Rq` bound. -/
theorem dqShallow_mul_lt_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.RundataParams.dqShallow G)
        * (QMCLeafB.EngineRuntime.Rq G / 4 + 1 / 2) < QMCLeafB.RundataCert.eps G := by
  have heps : 0 < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    linarith
  rw [QMCLeafB.RundataParams.dqShallow, if_neg (ne_of_gt hRq),
    QMCLeafB.RundataParams.dqShallowCore, div_mul_eq_mul_div,
    div_lt_iff₀ (by linarith : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1)]
  nlinarith [hRq, heps]

#print axioms QMCLeafB.Sliver2M8.dqShallow_mul_lt_eps

/-- **At `t = -Rq G` the witness slot is unsatisfiable — unconditionally.**  No band-PSD rational
point can be a centre of `bundleH_of_verdict_true` at the bracket's bottom, for any input with
`Rq G > 0`.  So the ok branch is empty there, `o G t = false` is forced, and the whole burden on the
sliver is the cut side (records, `hdriftc`, `hdriftd`) — the part bricks 1/2 own. -/
theorem no_witness_at_bottom_unconditional {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (h4 : (QMCLeafB.UnionShallow.paramsKbc2 G).dq ≤ 4)
    (X : Matrix (Fin G.n) (Fin G.n) ℚ) (hXsym : Xᵀ = X)
    (hXband : ∀ i, |X i i - 1| ≤ (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hXpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf X x) :
    ¬ (QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) X
        ≤ (-QMCLeafB.EngineRuntime.Rq G - QMCLeafB.RundataCert.eps G)
            + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2) := by
  have hlow := frob_lower_bound X h4 hXsym hXband hXpsd
  intro h
  have hdq : (QMCLeafB.UnionShallow.paramsKbc2 G).dq
      = QMCLeafB.RundataParams.dqShallow G := QMCLeafB.UnionShallow.paramsKbc2_dq G
  have harith := dqShallow_mul_lt_eps G hRq
  rw [hdq] at h hlow
  nlinarith [hlow, h, harith]

#print axioms QMCLeafB.Sliver2M8.no_witness_at_bottom_unconditional



/-! ## 6.  The same bound for the *margin* form, so it applies to `RelaxMem` itself

`RelaxMem` carries only `psd_margin : ∀ x, -(δ/2)·∑x² ≤ qf cX x`, not exact PSD, and it is not
required to be symmetric.  Both are harmless: the two quadratic-form evaluations at `eᵢ + eⱼ` give
`Xᵢⱼ + Xⱼᵢ ≥ -2 - (3/2)δ`, the antisymmetric part of `X` contributes nothing to `frob` against a
symmetric zero-diagonal `A`, and the pair bound is all the half-sum form of `frob` needs. -/

/-- **The pair bound from the margin form**: `Xᵢⱼ + Xⱼᵢ ≥ -2 - (3/2)·DQ` (no symmetry, no exact
PSD). -/
theorem pair_lower_bound {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} {DQ : ℚ}
    (hDQ0 : 0 ≤ DQ) (hXband : ∀ i, |X i i - 1| ≤ DQ / 4)
    (hmarg : ∀ x : Fin n → ℚ, -(DQ / 2) * (∑ i, x i ^ 2) ≤ qf X x) (i j : Fin n) :
    -2 - (3 / 2) * DQ ≤ X i j + X j i := by
  by_cases hij : i = j
  · subst hij
    have h := abs_le.mp (hXband i)
    linarith [h.1]
  · have hS : (∑ k, (if k = i then (1 : ℚ) else if k = j then 1 else 0) ^ 2) ≤ 2 := by
      have hpt : ∀ k : Fin n, (if k = i then (1 : ℚ) else if k = j then 1 else 0) ^ 2
          ≤ (if k = i then (1 : ℚ) else 0) + (if k = j then (1 : ℚ) else 0) := by
        intro k
        by_cases h1 : k = i
        · simp [h1, hij]
        · by_cases h2 : k = j
          · simp [h1, h2, Ne.symm hij]
          · simp [h1, h2]
      refine le_trans (Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)) ?_
      rw [Finset.sum_add_distrib]
      simp
      norm_num
    have h := hmarg (fun k => if k = i then (1 : ℚ) else if k = j then 1 else 0)
    have hq : -DQ ≤ qf X (fun k => if k = i then (1 : ℚ) else if k = j then 1 else 0) := by
      nlinarith [h, hS]
    rw [qf_two X hij 1 1] at hq
    have hi := abs_le.mp (hXband i)
    have hj := abs_le.mp (hXband j)
    linarith [hi.2, hj.2]

#print axioms QMCLeafB.Sliver2M8.pair_lower_bound

/-- **`frob` against a symmetric matrix is the half-sum of the pairs.** -/
theorem frob_eq_half_pairs {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j = A j i) :
    QMCLeafB.SepOracle.frob A X
      = (1 / 2) * ∑ i, ∑ j, A i j * (X i j + X j i) := by
  have hswap : (∑ i, ∑ j, A i j * X j i) = (∑ i, ∑ j, A i j * X i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => ?_))
    rw [hA b a]
  have hsplit : (∑ i, ∑ j, A i j * (X i j + X j i))
      = (∑ i, ∑ j, A i j * X i j) + (∑ i, ∑ j, A i j * X j i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => by ring)
  rw [hsplit, hswap]
  show (∑ i, ∑ j, A i j * X i j) = (1 / 2) * ((∑ i, ∑ j, A i j * X i j)
    + (∑ i, ∑ j, A i j * X i j))
  ring

#print axioms QMCLeafB.Sliver2M8.frob_eq_half_pairs

/-- **`-(1 + (3/4)dq)·Rq ≤ frob (wMatrixQ G) X` at a `RelaxMem`-shaped point.** -/
theorem frob_lower_bound_margin {G : QuantumMaxCutEnergy.Input}
    (X : Matrix (Fin G.n) (Fin G.n) ℚ) {DQ : ℚ}
    (hDQ0 : 0 ≤ DQ) (hXband : ∀ i, |X i i - 1| ≤ DQ / 4)
    (hmarg : ∀ x : Fin G.n → ℚ, -(DQ / 2) * (∑ i, x i ^ 2) ≤ qf X x) :
    (-(1 + (3 / 4) * DQ)) * QMCLeafB.EngineRuntime.Rq G
      ≤ QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) X := by
  have hAsym : ∀ i j : Fin G.n,
      QMCLeafB.Finalization.wMatrixQ G i j = QMCLeafB.Finalization.wMatrixQ G j i := by
    intro i j
    rw [QMCLeafB.Finalization.wMatrixQ_apply, QMCLeafB.Finalization.wMatrixQ_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_pos h, dif_neg (not_lt.mpr h.le), dif_pos h]
    · rw [h, dif_neg (lt_irrefl j), dif_neg (lt_irrefl j)]
    · rw [dif_neg (not_lt.mpr h.le), dif_pos h, dif_pos h]
  rw [frob_eq_half_pairs _ _ hAsym]
  have hstep : (1 / 2) * ∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j * (-2 - (3 / 2) * DQ)
      ≤ (1 / 2) * ∑ i, ∑ j,
          QMCLeafB.Finalization.wMatrixQ G i j * (X i j + X j i) := by
    have : (∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j * (-2 - (3 / 2) * DQ))
        ≤ (∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j * (X i j + X j i)) := by
      refine Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ?_)
      refine Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ?_)
      have h1 : 0 ≤ QMCLeafB.Finalization.wMatrixQ G i j := wMatrixQ_nonneg G i j
      have h2 := pair_lower_bound hDQ0 hXband hmarg i j
      nlinarith
    linarith
  refine le_trans ?_ hstep
  have h1 : (∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j * (-2 - (3 / 2) * DQ))
      = (∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j) * (-2 - (3 / 2) * DQ) := by
    rw [Finset.sum_mul]
    simp only [Finset.sum_mul]
  have key : ((1 / 2) * ∑ i, ∑ j,
        QMCLeafB.Finalization.wMatrixQ G i j * (-2 - (3 / 2) * DQ))
      = (-(1 + (3 / 4) * DQ)) * QMCLeafB.EngineRuntime.Rq G := by
    rw [h1, sum_wMatrixQ]
    ring
  rw [key]

#print axioms QMCLeafB.Sliver2M8.frob_lower_bound_margin

/-! ## 7.  No member at all at the bottom -/

/-- **`dqShallow·(3Rq/4 + 1/2) < eps`.** -/
theorem dqShallow_mul_lt_eps' (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.RundataParams.dqShallow G)
        * (3 * QMCLeafB.EngineRuntime.Rq G / 4 + 1 / 2) < QMCLeafB.RundataCert.eps G := by
  have heps : 0 < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    linarith
  rw [QMCLeafB.RundataParams.dqShallow, if_neg (ne_of_gt hRq),
    QMCLeafB.RundataParams.dqShallowCore, div_mul_eq_mul_div,
    div_lt_iff₀ (by linarith : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1)]
  nlinarith [hRq, heps]

#print axioms QMCLeafB.Sliver2M8.dqShallow_mul_lt_eps'

/-- **`hmem` is unsatisfiable at the bottom of the bracket.**  At `t = -Rq G` no rational centre is
a member of the relaxation at the round threshold `t - eps G`, for any input with `Rq G > 0` and any
tolerance `dq ≤ 4` with `dq ≤ dqShallow G`.  So the residual's `ok`-side slot is empty there *by
necessity*: the flag stream is all-`false`, `hverdict` forces the program's bit to be `false`, and the
entire burden on the sliver is the cut side (`C`, `hdriftc`, `hdriftd`) — the part bricks 1/2 own. -/
theorem no_relaxMem_at_bottom {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (DQ : ℚ)
    (hDQ : DQ = QMCLeafB.RundataParams.dqShallow G)
    (cX : Matrix (Fin G.n) (Fin G.n) ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (-QMCLeafB.EngineRuntime.Rq G - QMCLeafB.RundataCert.eps G) DQ := by
  intro hmem
  have hlow := frob_lower_bound_margin cX hmem.δ_pos.le hmem.diag_near hmem.psd_margin
  have htrace := hmem.trace_le
  have harith := dqShallow_mul_lt_eps' G hRq
  rw [hDQ] at hlow htrace
  nlinarith [hlow, htrace, harith]

#print axioms QMCLeafB.Sliver2M8.no_relaxMem_at_bottom

/-- **The canonical flag is `false` everywhere at the bottom.**  The residual's `hverdict` therefore
forces `o G t = false` at `t = -Rq G`. -/
theorem flagOf_false_at_bottom {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdqle : P.dq = QMCLeafB.RundataParams.dqShallow G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    QMCLeafB.FlagsM5.flagOf G (-QMCLeafB.EngineRuntime.Rq G) P cX k = false := by
  refine QMCLeafB.FlagsM5.flagOf_false_of_not_mem G (-QMCLeafB.EngineRuntime.Rq G) P cX k ?_
  have h := no_relaxMem_at_bottom hRq P.dq hdqle (cX k)
  intro hmem
  exact h hmem

#print axioms QMCLeafB.Sliver2M8.flagOf_false_at_bottom

/-! ## 8.  What the residual is forced to do at the bottom -/

/-- **Every `BundleH` at the bracket's bottom forces the verdict bit `false`.**  `hmem` would need a
member at some round `k < K*m`, which `no_relaxMem_at_bottom` refutes; so the `ok` stream is all
`false` and `anyOk` is `false`.  Hence at `t = -Rq G` the residual needs no PSD-margin certificate
and no `ok`-round record at all: the whole content there is the cut side. -/
theorem bundleH_forces_false_at_bottom {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdqle : P.dq = QMCLeafB.RundataParams.dqShallow G)
    {hn : 2 ≤ G.n} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FlagsM5.BundleH o G (-QMCLeafB.EngineRuntime.Rq G) P hn) :
    o G (-QMCLeafB.EngineRuntime.Rq G) = false := by
  have hok : ∀ k, k < P.K * P.m → B.ok k = false := by
    intro k hk
    by_contra h
    have htrue : B.ok k = true := by
      cases hb : B.ok k with
      | false => exact absurd hb h
      | true => rfl
    exact no_relaxMem_at_bottom hRq P.dq hdqle (B.cX k) (B.hmem k hk htrue)
  rw [B.hverdict]
  exact (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).mpr hok

#print axioms QMCLeafB.Sliver2M8.bundleH_forces_false_at_bottom

end QMCLeafB.Sliver2M8


