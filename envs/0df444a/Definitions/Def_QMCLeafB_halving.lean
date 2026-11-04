-- Prove2me | Definitions.Def_QMCLeafB_halving
-- name    : QMCLeafB_halving
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:28:07.832073+00:00
-- url     : https://prove2.me/theorems/ef2ba54d-0f10-413f-bd23-11a0e3989517
-- title:
--   QMCLeafB halving — the halving inequality at a positive depth ceiling
-- statement:
--   The halving bound $(\sqrt{\rho_0(N,\varrho)})^{-m}\le 1/2$ of the QMC ellipsoid engine at the positive shallow depth ceiling $\varrho = 1/(4N)$ with halving time $m = 16N^2$ (`hhalveOf`), plus `rundata_shallow`: the RunData constants at `dqShallow` and that ceiling. Replaces the deprecated `QMCLeafB_brick_halving_m5` (stale transitive import).

import Mathlib
import Definitions.Def_QMCLeafB_hdCert
/-
# leaf B phase 13 — brick `halving` (swarm `smw17fqzz`, member m5, direction d8)

`RunData.hhalve` is `(√(rho0R N rmax))⁻¹ ^ m ≤ 1/2`, and the shelf only proves it at `rmax = 0`
(`ClosingBracket.runData_hhalve_close`, `m = 4N`).  But `rmax = 0` is not usable by a run with cut
rounds: `hle` forces `ρ = 0`, then `hcheck` forces `δ = 0`, and a zero-margin cut cannot carry the
ball-floor containment (`RoundData` witness: `QMCLeafB.RundataCert.del_eq_zero_of_rmax_zero`).

This file proves the halving inequality at a **positive** ceiling and a still-polynomial halving
time:

    rmax = 1/(4·N),      m = 16·N²,      (√(rho0R N rmax))⁻¹ ^ m ≤ 1/2,      N = n·n ≥ 2.

The mathematics is the explicit formula

    rho0R N ρ = (1 − 1/N²)^N · (N+1)/(N−1) / (1 + ρ/N)^(2N),

three Bernoulli bounds and one rational inequality.  No analysis beyond Bernoulli: the point is to
make the shallow regime available, not to sharpen any constant.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false

namespace QMCLeafB.RundataHalving

open QuantumMaxCutEnergy

/-- **The explicit formula for the determinant multiplier.**  At order `N` and depth `ρ`, the
engine's step multiplies the determinant by `rho0R N ρ`; this is that number in the shape the
estimates need. -/
theorem rho0R_factor (N : ℕ) (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    QMCLeafB.EngineIterates.rho0R N ρ
      = (1 - 1 / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
          / (1 + ρ / (N : ℝ)) ^ (2 * N) := by
  have hx0 : (0 : ℝ) < (N : ℝ) := by positivity
  have hx1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hxa : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have e1 : (1 - 1 / (N : ℝ) ^ 2 : ℝ) = ((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2 := by
    field_simp
  have e2 : (1 + ρ / (N : ℝ) : ℝ) = ((N : ℝ) + ρ) / (N : ℝ) := by
    field_simp
  have e3 : ((N : ℝ) ^ 2) ^ N = (N : ℝ) ^ (2 * N) := (pow_mul (N : ℝ) 2 N).symm
  unfold QMCLeafB.EngineIterates.rho0R
  rw [e1, e2, div_pow, div_pow, e3]
  field_simp

/-- Bernoulli in the form the estimates want: `1 - n·x ≤ (1-x)^n` for `0 ≤ x ≤ 2`. -/
theorem one_sub_mul_le_pow {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 2) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  have h := one_add_mul_le_pow (R := ℝ) (a := -x) (by linarith) n
  have e : (1 : ℝ) + -x = 1 - x := by ring
  rw [e] at h
  nlinarith [h]

/-- `(1+u)⁻¹ ≥ 1-u` for `0 ≤ u`. -/
theorem one_sub_le_inv {u : ℝ} (hu : 0 ≤ u) : 1 - u ≤ (1 + u)⁻¹ := by
  rw [show (1 + u)⁻¹ = 1 / (1 + u) from (one_div (1 + u)).symm]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **The shallow ceiling is at least `1 + 1/(8N)`.**  Three Bernoulli bounds on the explicit
formula: `(1-1/N²)^N ≥ 1-1/N`, the exact middle factor `(N+1)/(N-1)`, and
`(1+1/(4N²))^{-2N} ≥ 1-1/(2N)`. -/
theorem rho0R_shallow_lower (N : ℕ) (hN : 2 ≤ N) :
    1 + 1 / (8 * (N : ℝ)) ≤ QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))) := by
  have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hρ0 : (0 : ℝ) ≤ 1 / (4 * (N : ℝ)) := by positivity
  rw [rho0R_factor N hN hρ0]
  -- factor 1
  have hx1 : 1 / (N : ℝ) ^ 2 ≤ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2' : 1 / (N : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hNsq]; exact h1
    linarith
  have hf1 : 1 - 1 / (N : ℝ) ≤ (1 - 1 / (N : ℝ) ^ 2) ^ N := by
    have hb := one_sub_mul_le_pow (x := 1 / (N : ℝ) ^ 2) (by positivity) hx1 N
    have hcoef : (N : ℝ) * (1 / (N : ℝ) ^ 2) = 1 / (N : ℝ) := by field_simp
    rw [hcoef] at hb
    exact hb
  -- factor 3
  have hu : (1 / (4 * (N : ℝ))) / (N : ℝ) = 1 / (4 * (N : ℝ) ^ 2) := by field_simp
  have hu0 : (0 : ℝ) ≤ 1 / (4 * (N : ℝ) ^ 2) := by positivity
  have hx3 : 1 / (4 * (N : ℝ) ^ 2) ≤ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2' : 1 / (4 * (N : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hx3' : 1 / (4 * (N : ℝ) ^ 2) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    rw [div_le_one (by positivity)]; linarith
  have huinv : 1 - 1 / (4 * (N : ℝ) ^ 2) ≤ (1 + 1 / (4 * (N : ℝ) ^ 2))⁻¹ :=
    one_sub_le_inv hu0
  have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 - 1 / (4 * (N : ℝ) ^ 2))
    huinv (2 * N)
  have hbern : 1 - 1 / (2 * (N : ℝ))
      ≤ (1 - 1 / (4 * (N : ℝ) ^ 2)) ^ (2 * N) := by
    have hb := one_sub_mul_le_pow (x := 1 / (4 * (N : ℝ) ^ 2)) hu0 hx3 (2 * N)
    have hN0' : (N : ℝ) ≠ 0 := ne_of_gt hN0
    have hcoef : ((2 * N : ℕ) : ℝ) * (1 / (4 * (N : ℝ) ^ 2)) = 1 / (2 * (N : ℝ)) := by
      push_cast
      field_simp
      ring
    rw [hcoef] at hb
    exact hb
  have hinv3 : 1 - 1 / (2 * (N : ℝ))
      ≤ ((1 + (1 / (4 * (N : ℝ))) / (N : ℝ)) ^ (2 * N))⁻¹ := by
    rw [hu, ← inv_pow]
    exact le_trans hbern hpow
  -- the rational bookkeeping
  have hrat : 1 + 1 / (8 * (N : ℝ))
      ≤ (1 - 1 / (N : ℝ)) * (((N : ℝ) + 1) / ((N : ℝ) - 1)) * (1 - 1 / (2 * (N : ℝ))) := by
    have h8 : (0 : ℝ) < 8 * (N : ℝ) := by linarith
    have h2N : (0 : ℝ) < 2 * (N : ℝ) := by linarith
    have hN0' : (N : ℝ) ≠ 0 := ne_of_gt hN0
    have hN1' : (N : ℝ) - 1 ≠ 0 := ne_of_gt hN1pos
    have h8' : 8 * (N : ℝ) ≠ 0 := ne_of_gt h8
    have h2N' : 2 * (N : ℝ) ≠ 0 := ne_of_gt h2N
    field_simp
    nlinarith [h2, sq_nonneg ((N : ℝ) - 2), sq_nonneg ((N : ℝ) - 4)]
  have hF1nn : (0 : ℝ) ≤ (1 - 1 / (N : ℝ) ^ 2) ^ N := by
    have h0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) ^ 2 := by
      rw [sub_nonneg, div_le_one hNsq]; nlinarith
    positivity
  have hF2nn : (0 : ℝ) ≤ ((N : ℝ) + 1) / ((N : ℝ) - 1) := by positivity
  have hleft : (0 : ℝ) ≤ (1 - 1 / (N : ℝ)) * (((N : ℝ) + 1) / ((N : ℝ) - 1)) := by
    have h1 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
      rw [sub_nonneg, div_le_one hN0]; linarith
    exact mul_nonneg h1 hF2nn
  have hstep1 : (1 - 1 / (N : ℝ)) * (((N : ℝ) + 1) / ((N : ℝ) - 1))
      ≤ (1 - 1 / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_right hf1 hF2nn
  have hstep2 : (1 - 1 / (N : ℝ)) * (((N : ℝ) + 1) / ((N : ℝ) - 1)) * (1 - 1 / (2 * (N : ℝ)))
      ≤ (1 - 1 / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
          * ((1 + (1 / (4 * (N : ℝ))) / (N : ℝ)) ^ (2 * N))⁻¹ := by
    refine mul_le_mul hstep1 hinv3 ?_ ?_
    · rw [sub_nonneg, div_le_one (by linarith : (0 : ℝ) < 2 * (N : ℝ))]; linarith
    · exact mul_nonneg hF1nn hF2nn
  refine le_trans hrat (le_trans hstep2 (le_of_eq ?_))
  rw [div_eq_mul_inv]
  ring

/-- **The halving inequality at the positive ceiling `1/(4N)` and halving time `16N²`.** -/
theorem halving_shallow (N : ℕ) (hN : 2 ≤ N) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))))⁻¹ ^ (16 * (N * N))
      ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlow := rho0R_shallow_lower N hN
  have hr0 : (0 : ℝ) ≤ QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))) := by
    have hp : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
    linarith
  have hA : 2 ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))))) ^ (16 * (N * N)) := by
    have hsq : (Real.sqrt (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))))) ^ (16 * (N * N))
        = (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))) ^ (8 * (N * N)) := by
      rw [show 16 * (N * N) = 2 * (8 * (N * N)) by ring, pow_mul, Real.sq_sqrt hr0]
    rw [hsq]
    have hmono : (1 + 1 / (8 * (N : ℝ))) ^ (8 * (N * N))
        ≤ (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))) ^ (8 * (N * N)) :=
      pow_le_pow_left₀ (by positivity) hlow _
    have hbern : 1 + (N : ℝ) ≤ (1 + 1 / (8 * (N : ℝ))) ^ (8 * (N * N)) := by
      have hpos : (0 : ℝ) ≤ 1 / (8 * (N : ℝ)) := by positivity
      have hb := one_add_mul_le_pow (R := ℝ) (a := 1 / (8 * (N : ℝ))) (by linarith) (8 * (N * N))
      have e2 : ((8 * (N * N) : ℕ) : ℝ) * (1 / (8 * (N : ℝ))) = (N : ℝ) := by
        have hN0' : (N : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [e2] at hb
      exact hb
    linarith
  rw [inv_pow]
  have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hA
  simpa using this

/-- The same at the rational ceiling `rmax = 1/(4·N)` used by `RunData` (`rmax : ℚ`). -/
theorem hhalve_shallow (N : ℕ) (hN : 2 ≤ N) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N (((1 : ℚ) / (4 * (N : ℚ)) : ℚ) : ℝ)))⁻¹
        ^ (16 * (N * N)) ≤ 1 / 2 := by
  have h := halving_shallow N hN
  push_cast
  exact h

#print axioms QMCLeafB.RundataHalving.rho0R_factor
#print axioms QMCLeafB.RundataHalving.one_sub_mul_le_pow
#print axioms QMCLeafB.RundataHalving.one_sub_le_inv
#print axioms QMCLeafB.RundataHalving.rho0R_shallow_lower
#print axioms QMCLeafB.RundataHalving.halving_shallow
#print axioms QMCLeafB.RundataHalving.hhalve_shallow

/-- The shallow regime's ceiling for a run at order `N`: `1/(4N)`, positive. -/
noncomputable def rmaxOf (N : ℕ) : ℚ := 1 / (4 * (N : ℚ))

/-- The halving time for a run at order `N`: `16N²` rounds per halving (polynomial). -/
def mOf (N : ℕ) : ℕ := 16 * (N * N)

theorem rmaxOf_pos (N : ℕ) (hN : 1 ≤ N) : 0 < rmaxOf N := by
  unfold rmaxOf
  have h : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  positivity

theorem mOf_ge_one (N : ℕ) (hN : 1 ≤ N) : 1 ≤ mOf N := by
  unfold mOf
  have h1 : 1 ≤ N * N := Nat.mul_le_mul hN hN
  omega

/-- **`RunData.hhalve` at a positive ceiling.**  This is the form to plug into
`QMCLeafB.RundataCert.rundata_of_relaxRun` (or `QMCLeafB.RundataArith.rundata_of_run`) at
`rmax = rmaxOf (G.n·G.n)`, `m = mOf (G.n·G.n)`: unlike the shelf's `rmax = 0`, it leaves the cut
depth `ρ` room to be positive, which the separation margin `δ > 0` needs. -/
theorem hhalveOf (N : ℕ) (hN : 2 ≤ N) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ((rmaxOf N : ℚ) : ℝ)))⁻¹ ^ mOf N ≤ 1 / 2 := by
  have h := hhalve_shallow N hN
  unfold rmaxOf mOf
  exact h

#print axioms QMCLeafB.RundataHalving.hhalveOf
#print axioms QMCLeafB.RundataHalving.rmaxOf_pos
#print axioms QMCLeafB.RundataHalving.mOf_ge_one

/-! ## The fully specialised `RunData` constructor

With the ceiling and the halving time fixed here, `QMCLeafB.RundataCert.rundata_of_relaxRun` has no
scalar parameter left: a run of the relaxed oracle at the shallow ceiling is a `RunData`.  This is
the form the assembly of `hd` should call. -/

/-- **`RunData` at the shallow constants.**  Hypotheses: the run's stream `cd`, its centres `cX`,
the oracle's verdicts (`RelaxCut` on cut rounds, `RelaxMem` on ok rounds), the three stream
identifications, symmetry of the centres, the ledger facts `hwit`, `ρ ≥ 0`, `c ≠ 0`, `δ ≥ 0`,
`δ² ≤ ρ²σ`, and the shallow ceiling `ρ ≤ 1/(4·n²)`. -/
noncomputable def rundata_shallow
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataCert.dq G))
    (hmem : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataCert.dq G))
    (hCsym : ∀ k, Matrix.transpose (cX k) = cX k)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), del k = (C k hok).margin)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
    (hwit : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = false →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (QMCLeafB.RundataArith.capOf G (QMCLeafB.RundataCert.dq G))) cd k *ᵥ (cd k).p
        = (cd k).c)
    (hrho : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = false →
      0 ≤ (cd k).rho)
    (hcne : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = false →
      (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = false →
      0 ≤ del k)
    (hcheck : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = false →
      (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G)
        (QMCLeafB.RundataCert.cAq G) (mOf (G.n * G.n)) 0 * mOf (G.n * G.n) → ok k = false →
      (cd k).rho ≤ rmaxOf (G.n * G.n))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      (QMCLeafB.RundataArith.runK G (QMCLeafB.RundataCert.dq G) (QMCLeafB.RundataCert.cAq G)
        (mOf (G.n * G.n)) 0 * mOf (G.n * G.n))) :
    QMCLeafB.VerdictSound.RunData o G t := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  exact QMCLeafB.RundataCert.rundata_of_relaxRun o G t hn hRq (rmaxOf (G.n * G.n))
    (rmaxOf_pos (G.n * G.n) (by omega)).le (mOf (G.n * G.n)) (mOf_ge_one (G.n * G.n) (by omega))
    (hhalveOf (G.n * G.n) hN) 0 ok cd del cX C hmem hCsym hnorm hmg hctr hwit hrho hcne hdel0
    hcheck hle hverdict

#print axioms QMCLeafB.RundataHalving.rundata_shallow

end QMCLeafB.RundataHalving


