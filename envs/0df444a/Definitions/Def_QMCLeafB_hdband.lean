-- Prove2me | Definitions.Def_QMCLeafB_hdband
-- name    : QMCLeafB_hdband
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:53:07.012817+00:00
-- url     : https://prove2.me/theorems/6bb58e27-1e52-4ef7-b1d7-6c5791e7c8d6
-- title:
--   QMCLeafB hdband
-- statement:
--   # leaf B phase 30 — m7: the empty stratum is a uniform band above `-Rq` at **every** input
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_refuted_m3
/-
# leaf B phase 30 — m7: the empty stratum is a uniform band above `-Rq` at **every** input

`RunParts.hcut` is the only slot of `hd` that costs analytic content at a body point, and it is
vacuous where the relaxed body is empty.  Phase 21 exhibited ONE empty-body point (at `G₀`, the
single edge of weight `1/2`, `t = -99999/100000`).  This file proves the general fact behind it:

    for every input `G` and every `t` below the explicit boundary
        tE G = -Rq G + dq/2·…        (see `body_empty_lowband`)
    the relaxed body at the engine's level is EMPTY,

so the empty stratum contains the band `[-Rq, tE)` of width `dq·(33·Rq/4 + 1/2) > 0` at every input
— `≈ 0.917·(Rq/40000)` for large `Rq`.  Consequently the `false` lane of `hd`
(`HdM7.hd_of_bit_classes`) is free on that band at **every** input, not just at one anchor.

The engine of the proof is the off-diagonal control that `hcut`'s separation also has to fight:
the relaxation's PSD slack `δ/2` bounds the *symmetric part* of the test point entrywise
(`|Xᵢⱼ + Xⱼᵢ| ≤ 2 + 3δ/2`), and the weight matrix is symmetric with nonnegative entries, so the
antisymmetric part — invisible to the quadratic form — cancels out of `frob`:

    frob A X ≥ -(1 + 3δ/4) · ∑ᵢⱼ |Aᵢⱼ| .

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.HdM7Band

open QuantumMaxCutEnergy

/-! ## 1.  The quadratic form at a pair of unit vectors -/

theorem qfR_single_add {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    QMCLeafB.BallFloor.qfR X (Pi.single i (1 : ℝ) + Pi.single j 1)
      = X i i + X i j + X j i + X j j := by
  rw [QMCLeafB.BallFloor.qfR, Matrix.mulVec_add, dotProduct_add]
  rw [add_dotProduct, add_dotProduct]
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm]
  ring

#print axioms QMCLeafB.HdM7Band.qfR_single_add

theorem qfR_single_sub {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    QMCLeafB.BallFloor.qfR X (Pi.single i (1 : ℝ) - Pi.single j 1)
      = X i i - X i j - X j i + X j j := by
  rw [QMCLeafB.BallFloor.qfR, Matrix.mulVec_sub, dotProduct_sub]
  rw [sub_dotProduct, sub_dotProduct]
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm]
  ring

#print axioms QMCLeafB.HdM7Band.qfR_single_sub

theorem sum_sq_single {n : ℕ} (i : Fin n) (c : ℝ) :
    (∑ k, (Pi.single i c : Fin n → ℝ) k ^ 2) = c ^ 2 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

#print axioms QMCLeafB.HdM7Band.sum_sq_single

theorem sum_sq_add_single {n : ℕ} (i j : Fin n) (a b : ℝ) (hij : i ≠ j) :
    (∑ k, (Pi.single i a + Pi.single j b : Fin n → ℝ) k ^ 2) = a ^ 2 + b ^ 2 := by
  have hterm : ∀ k : Fin n,
      (Pi.single i a + Pi.single j b : Fin n → ℝ) k ^ 2
        = (Pi.single i a : Fin n → ℝ) k ^ 2 + (Pi.single j b : Fin n → ℝ) k ^ 2
          + 2 * ((Pi.single i a : Fin n → ℝ) k * (Pi.single j b : Fin n → ℝ) k) := by
    intro k; rw [Pi.add_apply]; ring
  have hcross : (∑ k, ((Pi.single i a : Fin n → ℝ) k * (Pi.single j b : Fin n → ℝ) k)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simp [hij]
    · simp [hk]
  have hcross2 : (∑ k, 2 * ((Pi.single i a : Fin n → ℝ) k
      * (Pi.single j b : Fin n → ℝ) k)) = 0 := by
    rw [← Finset.mul_sum, hcross]; ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hcross2, sum_sq_single, sum_sq_single]
  ring

#print axioms QMCLeafB.HdM7Band.sum_sq_add_single

/-! ## 2.  The symmetric part is entrywise controlled by the PSD slack -/

theorem pair_bound {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpsd : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR X x)
    (hdiag : ∀ i, |X i i - 1| ≤ δ / 4) (i j : Fin n) :
    |X i j + X j i| ≤ 2 + 3 * δ / 2 := by
  rw [abs_le]
  constructor
  · by_cases hij : i = j
    · subst hij
      have h1 := (abs_le.mp (hdiag i)).1
      linarith
    · have hp := hpsd (Pi.single i (1 : ℝ) + Pi.single j 1)
      rw [qfR_single_add, sum_sq_add_single i j 1 1 hij] at hp
      have h1 := (abs_le.mp (hdiag i)).2
      have h2 := (abs_le.mp (hdiag j)).2
      linarith
  · by_cases hij : i = j
    · subst hij
      have h1 := (abs_le.mp (hdiag i)).2
      linarith
    · have hm := hpsd (Pi.single i (1 : ℝ) - Pi.single j 1)
      have hsub : (Pi.single i (1 : ℝ) - Pi.single j 1 : Fin n → ℝ)
          = Pi.single i 1 + Pi.single j (-1) := by
        funext k
        by_cases hk : k = j
        · subst hk; simp; ring
        · simp [hk]
      rw [qfR_single_sub, hsub, sum_sq_add_single i j 1 (-1) hij] at hm
      have h1 := (abs_le.mp (hdiag i)).2
      have h2 := (abs_le.mp (hdiag j)).2
      linarith

#print axioms QMCLeafB.HdM7Band.pair_bound

/-! ## 3.  The Frobenius pairing against a symmetric nonnegative matrix -/

theorem frob_ge_of_body {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAsym : ∀ i j, A i j = A j i) (hAnn : ∀ i j, 0 ≤ A i j)
    (hpsd : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR X x)
    (hdiag : ∀ i, |X i i - 1| ≤ δ / 4) :
    -(1 + 3 * δ / 4) * (∑ i, ∑ j, |A i j|) ≤ QMCLeafB.BallFloor.frob A X := by
  have hp : ∀ i j : Fin n, |X i j + X j i| ≤ 2 + 3 * δ / 2 :=
    fun i j => pair_bound X hδ hpsd hdiag i j
  have hswap : (∑ i, ∑ j, A i j * X j i) = ∑ i, ∑ j, A i j * X i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hAsym b a]
  have hfrob : QMCLeafB.BallFloor.frob A X
      = (1 / 2) * ∑ i, ∑ j, A i j * (X i j + X j i) := by
    have hdist : (∑ i, ∑ j, A i j * (X i j + X j i))
        = (∑ i, ∑ j, A i j * X i j) + (∑ i, ∑ j, A i j * X j i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [QMCLeafB.BallFloor.frob, hdist, hswap]
    ring
  have hkey : (1 / 2) * ∑ i, ∑ j, (-(2 + 3 * δ / 2)) * |A i j|
      ≤ (1 / 2) * ∑ i, ∑ j, A i j * (X i j + X j i) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [abs_of_nonneg (hAnn i j)]
    have hle : -(2 + 3 * δ / 2) ≤ X i j + X j i := (abs_le.mp (hp i j)).1
    have hscaled := mul_le_mul_of_nonneg_left hle (hAnn i j)
    linarith
  have hpull : ∀ c : ℝ, (∑ i, ∑ j, c * |A i j|) = c * ∑ i, ∑ j, |A i j| := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have heq : -(1 + 3 * δ / 4) * (∑ i, ∑ j, |A i j|)
      = (1 / 2) * ∑ i, ∑ j, (-(2 + 3 * δ / 2)) * |A i j| := by
    rw [hpull]
    ring
  rw [heq, hfrob]
  exact hkey

#print axioms QMCLeafB.HdM7Band.frob_ge_of_body

/-! ## 4.  The two ends: `∑ᵢⱼ |wMatrix G i j| = Rq G` over `ℝ`, symmetry, nonnegativity -/

theorem wMatrix_cast (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    QMCLeafB.wMatrix G i j = ((QMCLeafB.Finalization.wMatrixQ G i j : ℚ) : ℝ) := by
  rw [QMCLeafB.wMatrix_apply, QMCLeafB.Finalization.wMatrixQ_apply]
  split_ifs <;> push_cast <;> ring

#print axioms QMCLeafB.HdM7Band.wMatrix_cast

theorem wMatrix_symm' (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    QMCLeafB.wMatrix G i j = QMCLeafB.wMatrix G j i := by
  have h := congrFun (congrFun (QMCLeafB.wMatrix_symm G) j) i
  simpa [Matrix.transpose_apply] using h

#print axioms QMCLeafB.HdM7Band.wMatrix_symm'

theorem wMatrix_nonneg (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    0 ≤ QMCLeafB.wMatrix G i j := by
  rw [wMatrix_cast]
  have h := QMCLeafB.Finalization.IsQMCWeight.nonneg
    (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G) i j
  exact_mod_cast h

#print axioms QMCLeafB.HdM7Band.wMatrix_nonneg

theorem sum_abs_wMatrix (G : QuantumMaxCutEnergy.Input) :
    (∑ i, ∑ j, |QMCLeafB.wMatrix G i j|)
      = ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
  have h1 : ∀ i j : Fin G.n, |QMCLeafB.wMatrix G i j|
      = ((|QMCLeafB.Finalization.wMatrixQ G i j| : ℚ) : ℝ) := by
    intro i j
    rw [wMatrix_cast, Rat.cast_abs]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))]
  rw [← QMCLeafB.RundataCert.sum_abs_wMatrixQ]
  push_cast
  ring

#print axioms QMCLeafB.HdM7Band.sum_abs_wMatrix

/-! ## 5.  The empty stratum is a band above `-Rq`

The explicit boundary `tEmpty G` (over `ℚ`) is the exact point where the relaxation's own three
fields stop contradicting the Frobenius floor `frob (wMatrix G) X ≥ -(1 + 3δ/4)·Rq G`:

    tEmpty G = -Rq G + eps G - dq/2 - (3/4)·dq·Rq G ,      eps G = Rq G/40000 .

Since `dq·(9·Rq + 1) = eps` at the campaign's family, `tEmpty G + Rq G = dq·(33·Rq/4 + 1/2) > 0`,
i.e. the band `[-Rq, tEmpty)` is non-degenerate at every input with `Rq > 0`. -/

/-- The lower boundary of the empty stratum, over `ℚ`. -/
noncomputable def tEmpty (G : QuantumMaxCutEnergy.Input) : ℚ :=
  - QMCLeafB.EngineRuntime.Rq G + QMCLeafB.RundataCert.eps G
    - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2
    - (3 / 4) * (QMCLeafB.UnionShallow.paramsKbc2 G).dq * QMCLeafB.EngineRuntime.Rq G

/-- **The band is empty**: every `t` strictly below `tEmpty G` puts the engine's relaxed body out of
reach. -/
theorem body_empty_lowband (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 ≤ QMCLeafB.EngineRuntime.Rq G) {t : ℚ} (ht : t < tEmpty G) :
    ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X := by
  intro X hbody
  have hδ : (0 : ℝ) ≤ (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) := by
    have h := (QMCLeafB.UnionShallow.paramsKbc2 G).hdq
    exact_mod_cast le_of_lt h
  have hp := frob_ge_of_body (QMCLeafB.wMatrix G) X hδ (wMatrix_symm' G) (wMatrix_nonneg G)
    hbody.1 hbody.2.1
  rw [sum_abs_wMatrix] at hp
  have htr := hbody.2.2
  have heps : ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ)
      = (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := rfl
  have ht' : ((t : ℚ) : ℝ) < ((tEmpty G : ℚ) : ℝ) := by exact_mod_cast ht
  unfold tEmpty at ht'
  push_cast at ht' ⊢
  rw [heps] at ht'
  nlinarith [hp, htr, hδ, hRq]

#print axioms QMCLeafB.HdM7Band.body_empty_lowband

/-- **The `false` lane is free on the whole band** `[-Rq, tEmpty)`, at every input: the engine's
separation contract is vacuous there, so `RunParts` at the all-`cut`/all-`false` record needs
nothing. -/
noncomputable def runParts_false_lowband (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 ≤ QMCLeafB.EngineRuntime.Rq G) {t : ℚ} (ht : t < tEmpty G) :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => false) G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  QMCLeafB.RefutedM3.runParts_of_emptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn rfl
    (body_empty_lowband G hRq ht)

#print axioms QMCLeafB.HdM7Band.runParts_false_lowband

/-- The campaign tolerance is exactly `eps/(9·Rq + 1)` — the identity that makes the band's width
explicit. -/
theorem dq_mul_width (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq
        * (9 * QMCLeafB.EngineRuntime.Rq G + 1) = QMCLeafB.RundataCert.eps G := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
    QMCLeafB.RundataCert.eps
  rw [if_neg (ne_of_gt hRq)]
  have hpos : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  field_simp

#print axioms QMCLeafB.HdM7Band.dq_mul_width

/-- **The band is non-degenerate**: `tEmpty G` lies strictly above the bracket's floor `-Rq G`, with
gap `dq·(33·Rq/4 + 1/2)`. -/
theorem tEmpty_gt_neg_Rq (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    -(((QMCLeafB.EngineRuntime.Rq G : ℚ)) : ℝ) < ((tEmpty G : ℚ) : ℝ) := by
  have hdqeq := dq_mul_width G hRq
  have hdqp : (0 : ℚ) < (QMCLeafB.UnionShallow.paramsKbc2 G).dq :=
    (QMCLeafB.UnionShallow.paramsKbc2 G).hdq
  have heps : ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ)
      = (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ)
        * (9 * (((QMCLeafB.EngineRuntime.Rq G : ℚ)) : ℝ) + 1) := by
    rw [← hdqeq]
    push_cast
    ring
  have hdqR : (0 : ℝ) < (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) := by
    exact_mod_cast hdqp
  have hRqR : (0 : ℝ) < (((QMCLeafB.EngineRuntime.Rq G : ℚ)) : ℝ) := by exact_mod_cast hRq
  unfold tEmpty
  push_cast
  rw [heps]
  nlinarith [hdqR, hRqR]

#print axioms QMCLeafB.HdM7Band.tEmpty_gt_neg_Rq

end QMCLeafB.HdM7Band


