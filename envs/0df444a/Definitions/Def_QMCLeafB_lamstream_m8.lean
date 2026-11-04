-- Prove2me | Definitions.Def_QMCLeafB_lamstream_m8
-- name    : QMCLeafB_lamstream_m8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:26:25.81027+00:00
-- url     : https://prove2.me/theorems/1bbb7661-d38c-45a1-b862-bf24ebae6c74
-- title:
--   QMCLeafB lamstream_m8
-- statement:
--   # leaf B phase 18/19 — brick `lambda-stream` (swarm `smw1i2drp`, member m8, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_traceBudget2_m8
/-
# leaf B phase 18/19 — brick `lambda-stream` (swarm `smw1i2drp`, member m8, direction d9)

Follows `Check_traceBudget2_m8.lean`, which collapsed the drift block onto the strict trace budget
(`exists_lam_happr`: given `dOne ⪝ v < 0`, for every rational lower bound `L` there is `λ ≥ L` with
the dilated centre approximation).  What that left open is the *other* lower bound on `λ`: `hlam2`.

This file supplies it:

* `flatQ_one_ne_zero` — the dilation direction `u₀ = flatQ 1` is nonzero;
* `witAt_pairing_pos` — **`hlam2`'s coefficient is strictly positive**:
  `0 < u₀ ⪝ witAt (u₀) k = u₀ ⪝ runShape k⁻¹ u₀`, from `PosQ` (`runShape_posQ`) and `u₀ ≠ 0`;
  so `hlam2` really is a *lower* bound on `λ k`, and it depends only on `cn j` for `j < k`
  (`runShape` is the shape of the past stream).
* `exists_lam_of_hl` — **the multiplier exists**: given the strict trace budget and any rational
  `N, σ` with `σ > 0`, there is `λ` with `1 ≤ λ`, `N ≤ λ·σ` (i.e. `hlam1` and `hlam2`, abstracted)
  *and* the dilated centre approximation.

So the sequential `λ`-choice the collapse needed is a genuine lower-bound intersection, and this
brick's two facts are exactly why: positivity of `σ`, and `exists_lam_happr` monotone in the bound.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.LamStreamM8

open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate

/-- The rational identity reads `1` on the diagonal. -/
theorem flatQ_one_apply {n : ℕ} (i : Fin n) :
    QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv (i, i)) = 1 := by
  have hs : finProdFinEquiv.symm (finProdFinEquiv (i, i)) = (i, i) :=
    Equiv.symm_apply_apply _ _
  show (1 : Matrix (Fin n) (Fin n) ℚ)
      (finProdFinEquiv.symm (finProdFinEquiv (i, i))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, i))).2 = 1
  rw [hs, Matrix.one_apply_eq]

/-- The dilation direction `flatQ 1` is nonzero. -/
theorem flatQ_one_ne_zero {n : ℕ} (hn : 0 < n) :
    QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
  intro h
  have h1 := congrFun h (finProdFinEquiv (⟨0, hn⟩, ⟨0, hn⟩))
  rw [flatQ_one_apply] at h1
  exact one_ne_zero h1

/-- **`hlam2`'s coefficient is strictly positive.**  `u₀ = flatQ 1 ≠ 0` and `runShape k` is
positive definite, so `u₀ ⪝ runShape k⁻¹ u₀ > 0`; the left-hand side of `hlam2` is therefore a
genuine lower bound on `λ k`. -/
theorem witAt_pairing_pos (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (k : ℕ) :
    0 < QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
        ⬝ᵥ witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k := by
  have hA : QMCLeafB.EngineIterates.PosQ (runShape G P hn cn hcne k) :=
    runShape_posQ G P hn cn hcne k
  have hn0 : 0 < G.n := by omega
  have hwit : witAt G P hn cn hcne
      (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k ≠ 0 := by
    intro hz
    have hspec := witAt_spec G P hn cn hcne
      (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
    rw [hz, Matrix.mulVec_zero] at hspec
    exact flatQ_one_ne_zero hn0 hspec.symm
  have hspec := witAt_spec G P hn cn hcne
    (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
  have hq : QMCLeafB.EngineIterates.qf (runShape G P hn cn hcne k)
        (witAt G P hn cn hcne
          (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
      = QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
        ⬝ᵥ witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k := by
    rw [QMCLeafB.EngineIterates.qf, hspec, dotProduct_comm]
  rw [← hq]
  exact hA.2 _ hwit

/-- **The multiplier exists.**  Given the strict trace budget and any rational `N, σ` with
`σ > 0` (the abstraction of `hlam2`: `N ≤ λ·σ`), there is `λ ≥ 1` satisfying `hlam2` *and* the
dilated centre approximation.  So `hlam1`, `hlam2` and `happr` are jointly satisfiable by one `λ`. -/
theorem exists_lam_of_hl {n : ℕ} (v c : Fin (n * n) → ℝ) (m N σ : ℚ) (hσ : 0 < σ)
    (hstrict : dOne n ⬝ᵥ v < 0) :
    ∃ lam : ℚ, 1 ≤ lam ∧ N ≤ lam * σ
      ∧ (c + ((lam : ℚ) : ℝ) • dOne n) ⬝ᵥ v ≤ ((m : ℚ) : ℝ) / 2 := by
  obtain ⟨lam, hL, hle⟩ :=
    QMCLeafB.TraceBudgetM8.exists_lam_happr v c m (max 1 (N / σ)) hstrict
  refine ⟨lam, le_trans (le_max_left _ _) hL, ?_, hle⟩
  have h : N / σ ≤ lam := le_trans (le_max_right _ _) hL
  rw [div_le_iff₀ hσ] at h
  linarith [h]

end QMCLeafB.LamStreamM8

/-! ## Axiom audit -/

#print axioms QMCLeafB.LamStreamM8.flatQ_one_apply
#print axioms QMCLeafB.LamStreamM8.flatQ_one_ne_zero
#print axioms QMCLeafB.LamStreamM8.witAt_pairing_pos
#print axioms QMCLeafB.LamStreamM8.exists_lam_of_hl


