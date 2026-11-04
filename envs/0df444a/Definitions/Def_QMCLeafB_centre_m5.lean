-- Prove2me | Definitions.Def_QMCLeafB_centre_m5
-- name    : QMCLeafB_centre_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:05:46.947019+00:00
-- url     : https://prove2.me/theorems/eb5fe595-19ce-459f-b20f-e2cadac6882b
-- title:
--   QMCLeafB centre_m5
-- statement:
--   # leaf B phase 14 — brick `centre-track` (swarm `smw1a99tp`, member m5, direction d11)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparts_dilate_m5
/-
# leaf B phase 14 — brick `centre-track` (swarm `smw1a99tp`, member m5, direction d11)

`RunParts`' cut-side contract (`hcut`, via `RunPartsShallow.hcut_of_approx_gen` /
`RunPartsDilate.dilate`) is stated about the **engine's centre** `Cat N 0 cd k`, while the separation
oracle can only be queried at a *rational* matrix.  The engine's centre moves by
`(γ_j/√σ_j) • p_j` — the only irrational quantity of the whole loop (`γ_j = (1-ρ_j)/(N+1)` and
`p_j` are rational, `σ_j = c_j ⬝ p_j` is rational, but `1/√σ_j` is not) — so the run needs a
**rational surrogate** `q_k` together with an error bound in the cut's own normal direction:

    hdrift : c k ⬝ᵥ (Cat N 0 cd k − q_k) ≤ margin_k / 2.

This file supplies the *algebraic* half of that, with no dyadic machinery assumed:

* §1 `Cat_eq_sum` — the centre is the sum of its increments:

      Cat N 0 cd k = ∑_{j<k} (γ_j/√σ_j) • p_j.

* §2 `drift_bound` — if every increment coefficient `λ_j = γ_j/√σ_j` is pinned by a rational
  *interval* `[μ_j, μ_j + δ_j]` (`μ_j` the recorded rational surrogate coefficient), then the
  surrogate `q_k = ∑_{j<k} μ_j • p_j` has

      c ⬝ᵥ (Cat k − q_k) ≤ ∑_{j<k} δ_j · max 0 (c ⬝ᵥ p_j),

  i.e. each interval's width is charged only where the cut direction `c` has the *same* sign as the
  increment `p_j` (where the mismatch can actually hurt).

* §3 `hdrift_of_budget` — the packaged form the run interface consumes: from the surrogate
  identification `flat (castMat qMat) = ∑_{j<k} μ_j • p_j` and the *rational* budget
  `∑_{j<k} δ_j · max 0 (c ⬝ᵥ p_j) ≤ margin/2`, the drift hypothesis `hcut_of_approx_gen` needs.

So the centre approximation reduces to producing, per round, a rational interval for
`(1-ρ_j)/((N+1)·√σ_j)` — i.e. a one-sided dyadic enclosure of `1/√σ_j` (the `DyadicSqrt` layer) —
and the budget above is a plain rational inequality the program can evaluate.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QMCLeafB.CentreTrack

open QuantumMaxCutEnergy

/-! ## 1.  The centre is the sum of its increments -/

/-- The increment coefficient of round `j`: `γ_j / √σ_j`. -/
noncomputable def lam (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j : ℕ) : ℝ :=
  QMCLeafB.EngineIterates.gammaR N ((cd j).rho : ℝ)
    / QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd j)
        (QMCLeafB.EngineIterates.cutPR cd j)

/-- **The closed form of the engine's centre.** -/
theorem Cat_eq_sum (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (k : ℕ) :
    QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
      = ∑ j ∈ Finset.range k, lam N cd j • QMCLeafB.EngineIterates.cutPR cd j := by
  induction k with
  | zero => simp [QMCLeafB.EngineIterates.Cat]
  | succ k ih =>
      rw [QMCLeafB.EngineIterates.Cat_unfold, ih, Finset.sum_range_succ]
      rfl

/-! ## 2.  The drift bound from interval enclosures -/

/-- `c ⬝ (x + y) = c ⬝ x + c ⬝ y` and the `smul` form, for the dot product over `ℝ`. -/
theorem dot_sum_smul {N : ℕ} (c : Fin N → ℝ) (s : Finset ℕ) (f : ℕ → ℝ) (v : ℕ → Fin N → ℝ) :
    c ⬝ᵥ (∑ j ∈ s, f j • v j) = ∑ j ∈ s, f j * (c ⬝ᵥ v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dotProduct_add, ih, dotProduct_smul,
        smul_eq_mul]

/-- **The drift of the engine's centre from a rational surrogate.**  If the increment coefficient
`λ_j` of every round `j < k` is enclosed by `[μ_j, μ_j + δ_j]`, then the surrogate
`q_k = ∑_{j<k} μ_j • p_j` is within `∑_{j<k} δ_j · max 0 (c ⬝ p_j)` of `Cat k` in the direction
`c`. -/
theorem drift_bound (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (c : Fin N → ℝ) (k : ℕ)
    (mu delta : ℕ → ℝ)
    (hlo : ∀ j, j < k → mu j ≤ lam N cd j)
    (hhi : ∀ j, j < k → lam N cd j ≤ mu j + delta j)
    (hd0 : ∀ j, 0 ≤ delta j) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
        - ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR cd j)
      ≤ ∑ j ∈ Finset.range k, delta j * max 0 (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) := by
  classical
  have hsplit : QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
      - ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR cd j
      = ∑ j ∈ Finset.range k, (lam N cd j - mu j) • QMCLeafB.EngineIterates.cutPR cd j := by
    rw [Cat_eq_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_smul]
  rw [hsplit, dot_sum_smul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  have h1 : mu j ≤ lam N cd j := hlo j hjk
  have h2 : lam N cd j ≤ mu j + delta j := hhi j hjk
  rcases le_total 0 (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) with hsign | hsign
  · have h3 : lam N cd j - mu j ≤ delta j := by linarith
    have h4 : lam N cd j - mu j ≥ 0 := by linarith
    have h5 : (lam N cd j - mu j) * (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j)
        ≤ delta j * (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) :=
      mul_le_mul_of_nonneg_right h3 hsign
    rw [max_eq_right hsign]
    exact h5
  · have h5 : (lam N cd j - mu j) * (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) ≤ 0 := by
      have h6 : 0 ≤ lam N cd j - mu j := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos h6 hsign
    rw [max_eq_left hsign]
    exact le_trans h5 (mul_nonneg (hd0 j) le_rfl)

/-! ## 3.  The packaged drift hypothesis of the run interface -/

/-- **`hdriftc` from a rational surrogate and a rational budget.**  `hq` identifies the program's
rational query centre with the surrogate; `hbud` is the rational budget on the accumulated interval
widths.  The conclusion is exactly the drift hypothesis of
`RunPartsShallow.hcut_of_approx_gen` / `RunPartsDilate.runParts_of_dilated`. -/
theorem hdrift_of_budget (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (c : Fin N → ℝ)
    (k : ℕ) (q : Fin N → ℝ) (mu delta : ℕ → ℝ) (margin : ℝ)
    (hq : q = ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR cd j)
    (hlo : ∀ j, j < k → mu j ≤ lam N cd j)
    (hhi : ∀ j, j < k → lam N cd j ≤ mu j + delta j)
    (hd0 : ∀ j, 0 ≤ delta j)
    (hbud : ∑ j ∈ Finset.range k,
        delta j * max 0 (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) ≤ margin / 2) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k - q) ≤ margin / 2 := by
  rw [hq]
  exact le_trans (drift_bound N cd c k mu delta hlo hhi hd0) hbud

#print axioms QMCLeafB.CentreTrack.Cat_eq_sum
#print axioms QMCLeafB.CentreTrack.drift_bound
#print axioms QMCLeafB.CentreTrack.hdrift_of_budget

/-! ## 4.  The intervals themselves, from the dyadic reciprocal brackets -/

/-- `γ_j = (1 − ρ_j)/(N+1)` over `ℚ`. -/
noncomputable def gamQ (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j : ℕ) : ℚ :=
  (1 - (cd j).rho) / ((N : ℚ) + 1)

theorem gammaR_eq_gamQ (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j : ℕ) :
    QMCLeafB.EngineIterates.gammaR N ((cd j).rho : ℝ) = ((gamQ N cd j : ℚ) : ℝ) := by
  simp only [QMCLeafB.EngineIterates.gammaR, gamQ]
  push_cast
  ring

theorem gamQ_nonneg (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) {j : ℕ}
    (hρ1 : (cd j).rho ≤ 1) : 0 ≤ gamQ N cd j := by
  have h1 : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) ≤ 1 - (cd j).rho := by linarith
  exact div_nonneg h2 h1.le

/-- `√σ` in the engine's own notation. -/
theorem sqrtSigmaR_eq (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j : ℕ) :
    QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd j)
        (QMCLeafB.EngineIterates.cutPR cd j)
      = Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p : ℚ)) : ℝ) := by
  rw [QMCLeafB.EngineIterates.sqrtSigmaR, ← QMCLeafB.EngineIterates.cast_sigmaQ]

/-- **The dyadic bracket of the increment coefficient.**  For every round `j` and every grid
`k` with `1 ≤ σ_j·4^k`, the coefficient `λ_j = γ_j/√σ_j` lies in the rational interval
`[γ_j·invSqrtLe, γ_j·invSqrtGe]`. -/
theorem lam_bracket (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j k : ℕ)
    (hρ1 : (cd j).rho ≤ 1)
    (hσ : 0 < QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
    (hk : 1 ≤ QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p * 4 ^ k) :
    ((gamQ N cd j * DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ)
        ≤ lam N cd j
      ∧ lam N cd j
        ≤ ((gamQ N cd j * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ)
            : ℝ) := by
  have hγ0 : 0 ≤ gamQ N cd j := gamQ_nonneg N cd hρ1
  have hγ0R : (0 : ℝ) ≤ ((gamQ N cd j : ℚ) : ℝ) := by exact_mod_cast hγ0
  have h1 : ((DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ)
      ≤ 1 / QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd j)
          (QMCLeafB.EngineIterates.cutPR cd j) := by
    rw [sqrtSigmaR_eq]
    exact DQ.invSqrtLe_le hσ k
  have h2 : 1 / QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd j)
        (QMCLeafB.EngineIterates.cutPR cd j)
      ≤ ((DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ) := by
    rw [sqrtSigmaR_eq]
    exact DQ.le_invSqrtGe hk
  have hlam : lam N cd j
      = ((gamQ N cd j : ℚ) : ℝ)
        * (1 / QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd j)
            (QMCLeafB.EngineIterates.cutPR cd j)) := by
    rw [lam, gammaR_eq_gamQ]
    ring
  constructor
  · rw [hlam]
    have := mul_le_mul_of_nonneg_left h1 hγ0R
    calc ((gamQ N cd j * DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ)
        = ((gamQ N cd j : ℚ) : ℝ)
          * ((DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ) := by
          push_cast; ring
      _ ≤ _ := this
  · rw [hlam]
    have := mul_le_mul_of_nonneg_left h2 hγ0R
    calc ((gamQ N cd j : ℚ) : ℝ)
          * (1 / QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd j)
              (QMCLeafB.EngineIterates.cutPR cd j))
        ≤ ((gamQ N cd j : ℚ) : ℝ)
          * ((DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ) := this
      _ = ((gamQ N cd j * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ)
            : ℝ) := by push_cast; ring

#print axioms QMCLeafB.CentreTrack.gamQ_nonneg
#print axioms QMCLeafB.CentreTrack.lam_bracket

/-- The dyadic reciprocal bracket is ordered (`1/sqrtGe ≤ 1/sqrtLe`), under the scale condition. -/
theorem invSqrtLe_le_invSqrtGe' {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) :
    DQ.invSqrtLe x k ≤ DQ.invSqrtGe x k := by
  simp only [DQ.invSqrtLe, DQ.invSqrtGe]
  exact one_div_le_one_div_of_le (DQ.sqrtLe_pos_of_one_le_mul h) (DQ.sqrtLe_le_sqrtGe x k)

/-- **The drift bound with the dyadic brackets instantiated.**  The surrogate coefficients are
`μ_j = γ_j·invSqrtLe σ_j k_j`; the widths `δ_j = γ_j·(invSqrtGe − invSqrtLe)`.  The only remaining
input is the *rational* budget on the accumulated widths. -/
theorem hdrift_of_dyadic (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (c : Fin N → ℝ)
    (k : ℕ) (q : Fin N → ℝ) (grid : ℕ → ℕ) (margin : ℝ)
    (hq : q = ∑ j ∈ Finset.range k,
      ((gamQ N cd j * DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
        : ℚ) : ℝ) • QMCLeafB.EngineIterates.cutPR cd j)
    (hρ1 : ∀ j, (cd j).rho ≤ 1)
    (hσ : ∀ j, 0 < QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
    (hk : ∀ j, 1 ≤ QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p * 4 ^ (grid j))
    (hbud : ∑ j ∈ Finset.range k,
        ((gamQ N cd j * (DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
          - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)) : ℚ) : ℝ)
          * max 0 (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) ≤ margin / 2) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k - q) ≤ margin / 2 := by
  refine hdrift_of_budget N cd c k q
    (fun j => ((gamQ N cd j * DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
      : ℚ) : ℝ))
    (fun j => ((gamQ N cd j * (DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
      - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)) : ℚ) : ℝ))
    margin hq ?_ ?_ ?_ hbud
  · -- lower end
    intro j _
    exact (lam_bracket N cd j (grid j) (hρ1 j) (hσ j) (hk j)).1
  · -- upper end
    intro j _
    have h2 := (lam_bracket N cd j (grid j) (hρ1 j) (hσ j) (hk j)).2
    have hcast : ((gamQ N cd j * DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
          (grid j) : ℚ) : ℝ)
        + ((gamQ N cd j * (DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
          - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)) : ℚ) : ℝ)
        = ((gamQ N cd j * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
            (grid j) : ℚ) : ℝ) := by
      push_cast
      ring
    linarith
  · -- the widths are nonnegative
    intro j
    have hγ : (0 : ℚ) ≤ gamQ N cd j := gamQ_nonneg N cd (hρ1 j)
    have hw : 0 ≤ DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
        - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j) := by
      have := invSqrtLe_le_invSqrtGe' (x := QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
        (k := grid j) (hk j)
      linarith
    have := mul_nonneg hγ hw
    exact_mod_cast this

#print axioms QMCLeafB.CentreTrack.invSqrtLe_le_invSqrtGe'
#print axioms QMCLeafB.CentreTrack.hdrift_of_dyadic

end QMCLeafB.CentreTrack


