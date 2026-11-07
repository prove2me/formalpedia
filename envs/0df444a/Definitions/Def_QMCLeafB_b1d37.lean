-- Prove2me | Definitions.Def_QMCLeafB_b1d37
-- name    : QMCLeafB_b1d37
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:16:16.706045+00:00
-- url     : https://prove2.me/theorems/d0b56caf-3b68-45ec-88d4-2afc5aadd39c
-- title:
--   QMCLeafB b1d37
-- statement:
--   The Check_b1d37_m5 module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm35
import Definitions.Def_QMCLeafB_crux_m1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.B1D37M5

open QMCLeafB.EngineIterates
/-
# `Check_b1d37_m5` — phase 37, member m5, direction `b1-centre-identity` (DECIDED)

## The question this file answers

The phase-37 dichotomy needs, in its case **(B)** (every round reports a non-member), a rational
centre `cX k` whose cut can be read as a cut at the engine's own accumulated centre `Cat k`; the
gap is m4/ph36's **price** `margin_k − n_k·(flat cX k − Cat k)`, which must be paid out of the
ledger `del k² ≤ ρ_k²σ_k` with `ρ_k ≤ rmax`.  Candidate **(B1)** proposes to make the price vanish
*by construction*: choose the programme's state/coding so that the round's rational centre **is**
`Cat k` at every round.  m1/ph35's `hctr_one_forces_square` was recorded as the obstruction, "for
one specific `NormalCut`/`rStep` choice", and this phase was asked to decide whether a different
normalisation/state coding avoids it.

**Verdict: (B1) is INTRINSIC, and it is an arithmetic condition, not a coding choice.**  Four
machine-checked facts decide it.

1. **`isSquare_sigma_of_rational_step`** (coding-free).  For *any* cut stream, at *any* round `k`
   (`k = 0` recovers m1's theorem), if `Cat k` and `Cat (k+1)` are both rational points of
   `ℝ^{n·n}` then `σ_k = c_k ⬝ p_k` is a **rational square** — as soon as `σ_k > 0` and the round's
   depth is not the frozen `ρ_k = 1`.  The proof uses `Cat`'s step law
   `Cat (k+1) − Cat k = (γ_k/√σ_k) • p_k` and nothing else: no `NormalCut`, no oracle, no gate, no
   programme.  So no state coding can dodge it.
2. **`ratVec_cat_one_iff`** (an exact iff, not an implication).  At round `1`, the accumulated
   centre is rational **iff** `σ_0` is a rational square.  There is no half-way house: the centre
   identity *is* the square condition.
3. **`sigma_class_scale_free`** (no normalisation escape).  `σ` is homogeneous of degree `2` under
   `c ↦ t·c`, `p ↦ t·p`, so rescaling the normal (or any state re-presentation that rescales it)
   multiplies `σ` by a square and cannot change whether it is a square.  The condition is a function
   of the **projective** normal, as m1 said.
4. **`runParts_gamma_ne_zero` / `runParts_isSquare_of_rational_centres` / `runParts_rho_ne_one`**
   (the only exact escape is closed by the programme's own numbers).  `γ(ρ) = 0 ↔ ρ = 1`: freezing
   the centre is the *only* way to keep it rational with an arbitrary `σ`.  But `RunParams.hhalve`
   forces `rho0R (n²) rmax > 1`, `rho0R ≤ 1` at every `ρ ≥ 1` (`rho0R_le_one_of_one_le_rho`) and
   hence **`rmax < 1`** (`runParams_rmax_lt_one`) — so every recorded depth `ρ_k ≤ rmax` is `< 1`,
   `γ_k ≠ 0`, and **in every `RunParts` at the campaign's parameters a rational accumulated centre
   forces every recorded `σ_k` to be a rational square.**

**Is the square condition satisfiable at all?** Yes, and the file says exactly when: at the
campaign's init shape `A₀ = M⁻¹ • 1` the recorded `σ` is `M` times a rational sum of squares
(`sigmaQ_initShape`), so at round `0` the class is that of `M·‖c₀‖²`; and the two classical
witnesses differ by nothing but the class — `coordCd_four_ratVec` (`M = 4`) has a **rational**
accumulated centre, while `coordCd_two_not_ratVec` (`M = 2`) has none for any rational presentation.
So (B1) is not vacuous: it is realisable precisely by controlling the normals' square classes — a
resource the separation oracle, not the programme, owns.

## What this does to the dichotomy

Case (A) is unaffected (it is the `hok` lane: `bit_true_of_some_ok` below is the record-level
half).  Case (B) therefore has only candidate **(B2)** left, and this file fixes its exact size:
`runParts_del_le_rmax_sqrt` — **the ledger has no slack**: `hcheck` plus `ρ_k ≤ rmax` gives
`del k ≤ rmax·√σ_k`, so a price charged on top of the oracle's own margin
`ρ^oracle_k·√σ_k` fits only in the room `(rmax − ρ^oracle_k)·√σ_k`.  Paying the price is thus a
*shallow-cut condition at the accumulated centre*, i.e. `ShallowCut` with the oracle's own normals —
and m6/ph35's `shallowCut_of_separating` / m4/ph34's `encl_of_bodyRec` show that condition is the
campaign's obligation, not a free budget.  **The collar does not disappear from case (B).**
-/
def RatVec (n : ℕ) (v : Fin (n * n) → ℝ) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) ℚ, v = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)

theorem flat_sub {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (X - Y))
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y) := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat, QMCLeafB.SepOracle.castMat_apply]

theorem ratVec_flatQ {n : ℕ} (v : Fin (n * n) → ℚ) : RatVec n (fun i => ((v i : ℚ) : ℝ)) := by
  refine ⟨Matrix.of (fun i j => v (finProdFinEquiv (i, j))), ?_⟩
  rw [QMCLeafB.CruxM1.flat_castMat_eq]
  funext k
  simp only [QMCLeafB.RelaxOracle.flatQ, Matrix.of_apply]
  rw [Equiv.apply_symm_apply]

theorem ratVec_sub {n : ℕ} {u v : Fin (n * n) → ℝ} (hu : RatVec n u) (hv : RatVec n v) :
    RatVec n (u - v) := by
  obtain ⟨X, rfl⟩ := hu
  obtain ⟨Y, rfl⟩ := hv
  exact ⟨X - Y, (flat_sub X Y).symm⟩

theorem ratVec_zero (n : ℕ) : RatVec n 0 := by
  have h := ratVec_flatQ (n := n) (fun _ => (0 : ℚ))
  convert h using 2 <;> simp

/-! ### The step law at an arbitrary round -/

theorem cat_step_eq {N : ℕ} (a0 : Fin N → ℝ) (cd : ℕ → CutData N) (k : ℕ) :
    Cat N a0 cd (k + 1) - Cat N a0 cd k
      = (gammaR N ((cd k).rho : ℝ) / sqrtSigmaR (cutCR cd k) (cutPR cd k)) • cutPR cd k := by
  rw [Cat_unfold, stepCentre]
  abel

set_option maxHeartbeats 2000000 in
theorem isSquare_sigma_of_rational_step {n : ℕ} {a0 : Fin (n * n) → ℝ} (cd : ℕ → CutData (n * n))
    (k : ℕ) (hσ : 0 < sigmaQ (cd k).c (cd k).p)
    (hγ : gammaR (n * n) ((cd k).rho : ℝ) ≠ 0)
    (h0 : RatVec n (Cat (n * n) a0 cd k))
    (h1 : RatVec n (Cat (n * n) a0 cd (k + 1))) :
    IsSquare (sigmaQ (cd k).c (cd k).p) := by
  classical
  obtain ⟨X, hX⟩ := h0
  obtain ⟨Y, hY⟩ := h1
  have hσR : (0 : ℝ) < sigmaR (cutCR cd k) (cutPR cd k) := by
    rw [← QMCLeafB.EngineIterates.cast_sigmaQ]
    exact_mod_cast hσ
  have hsqrt : sqrtSigmaR (cutCR cd k) (cutPR cd k) ≠ 0 :=
    (Real.sqrt_pos.mpr hσR).ne'
  have hp : (cd k).p ≠ 0 := by
    intro hp0
    have hz : sigmaQ (cd k).c (cd k).p = 0 := by simp [sigmaQ, hp0]
    rw [hz] at hσ
    exact lt_irrefl (0 : ℚ) hσ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
  have hstep : Cat (n * n) a0 cd (k + 1) i - Cat (n * n) a0 cd k i
      = (gammaR (n * n) ((cd k).rho : ℝ) / sqrtSigmaR (cutCR cd k) (cutPR cd k))
        * ((cd k).p i : ℝ) := by
    have h := congrFun (cat_step_eq a0 cd k) i
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cutPR] using h
  have hrat : Cat (n * n) a0 cd (k + 1) i - Cat (n * n) a0 cd k i
      = (((QMCLeafB.RelaxOracle.flatQ Y i : ℚ) : ℝ)
          - ((QMCLeafB.RelaxOracle.flatQ X i : ℚ) : ℝ)) := by
    rw [hY, hX, QMCLeafB.CruxM1.flat_castMat_eq, QMCLeafB.CruxM1.flat_castMat_eq]
  set q : ℚ := QMCLeafB.RelaxOracle.flatQ Y i - QMCLeafB.RelaxOracle.flatQ X i with hqdef
  have hqcast : (q : ℝ) = ((QMCLeafB.RelaxOracle.flatQ Y i : ℚ) : ℝ)
      - ((QMCLeafB.RelaxOracle.flatQ X i : ℚ) : ℝ) := by
    rw [hqdef]; push_cast; ring
  have hq : (q : ℝ) = gammaR (n * n) ((cd k).rho : ℝ)
      / sqrtSigmaR (cutCR cd k) (cutPR cd k) * ((cd k).p i : ℝ) := by
    rw [hqcast, ← hrat, hstep]
  have hir : ((cd k).p i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hqne : q ≠ 0 := by
    intro hq0
    have hzero : (gammaR (n * n) ((cd k).rho : ℝ)
        / sqrtSigmaR (cutCR cd k) (cutPR cd k)) * ((cd k).p i : ℝ) = 0 := by
      rw [← hq, hq0]; simp
    rcases mul_eq_zero.mp hzero with h | h
    · exact hγ (by
        rcases div_eq_zero_iff.mp h with h' | h'
        · exact h'
        · exact absurd h' hsqrt)
    · exact hir h
  have hqR : (q : ℝ) ≠ 0 := fun h => hqne (Rat.cast_injective (by rw [h]; simp))
  have hmul : (q : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)
      = gammaR (n * n) ((cd k).rho : ℝ) * ((cd k).p i : ℝ) := by
    rw [hq]
    field_simp
  have hsqrt_eq : sqrtSigmaR (cutCR cd k) (cutPR cd k)
      = gammaR (n * n) ((cd k).rho : ℝ) * ((cd k).p i : ℝ) / (q : ℝ) := by
    rw [eq_div_iff hqR, mul_comm, hmul]
  have hσeq : ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)
      = sqrtSigmaR (cutCR cd k) (cutPR cd k) ^ 2 := by
    rw [QMCLeafB.EngineIterates.cast_sigmaQ]
    exact (Real.sq_sqrt hσR.le).symm
  have hsq : ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)
      = (gammaR (n * n) ((cd k).rho : ℝ) * ((cd k).p i : ℝ) / (q : ℝ)) ^ 2 := by
    rw [hσeq, hsqrt_eq]
  refine ⟨QMCLeafB.CruxM1.gammaQ (n * n) (cd k).rho * (cd k).p i / q, ?_⟩
  have hfin : (((QMCLeafB.CruxM1.gammaQ (n * n) (cd k).rho * (cd k).p i / q) ^ 2 : ℚ) : ℝ)
      = ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) := by
    rw [hsq]
    push_cast
    rw [QMCLeafB.CruxM1.cast_gammaQ]
  have hfin' : (QMCLeafB.CruxM1.gammaQ (n * n) (cd k).rho * (cd k).p i / q) ^ 2
      = sigmaQ (cd k).c (cd k).p := by
    exact_mod_cast hfin
  simpa [pow_two] using hfin'.symm



/-! ### The exact characterization at round 1 -/

theorem sigmaQ_smul {n : ℕ} (t : ℚ) (c p : Fin n → ℚ) :
    sigmaQ (t • c) (t • p) = t ^ 2 * sigmaQ c p := by
  simp only [sigmaQ, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem isSquare_sigmaQ_smul {n : ℕ} {t : ℚ} (ht : t ≠ 0) (c p : Fin n → ℚ) :
    IsSquare (sigmaQ (t • c) (t • p)) ↔ IsSquare (sigmaQ c p) := by
  rw [sigmaQ_smul]
  constructor
  · intro ⟨y, hy⟩
    refine ⟨y / t, ?_⟩
    have h2 : (0:ℚ) < t ^ 2 := by positivity
    have : t ^ 2 * sigmaQ c p = y * y := hy
    field_simp
    linear_combination this
  · intro ⟨y, hy⟩
    exact ⟨t * y, by rw [hy]; ring⟩


/-! ### Round 1: the exact iff -/

theorem cat_one_formula {N : ℕ} (cd : ℕ → CutData N) :
    Cat N (0 : Fin N → ℝ) cd 1
      = (gammaR N ((cd 0).rho : ℝ) / sqrtSigmaR (cutCR cd 0) (cutPR cd 0)) • cutPR cd 0 := by
  rw [Cat_unfold]
  simp [Cat, stepCentre]

theorem ratVec_cat_one_of_isSquare {n : ℕ} (cd : ℕ → CutData (n * n))
    (hσ : 0 < sigmaQ (cd 0).c (cd 0).p)
    (hsq : IsSquare (sigmaQ (cd 0).c (cd 0).p)) :
    RatVec n (Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1) := by
  classical
  obtain ⟨q, hq⟩ := hsq
  have hqσ : sigmaQ (cd 0).c (cd 0).p = q * q := hq
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hqσ
    exact (lt_irrefl (0:ℚ) (hqσ ▸ hσ))
  set q' : ℚ := if 0 < q then q else -q with hq'def
  have hq'pos : 0 < q' := by
    rw [hq'def]
    split_ifs with h
    · exact h
    · have h2 : q ≤ 0 := not_lt.mp h
      have h3 : q < 0 := lt_of_le_of_ne h2 hqne
      linarith
  have hq'sq : q' * q' = sigmaQ (cd 0).c (cd 0).p := by
    rw [hq'def]
    split_ifs with h
    · exact hqσ.symm
    · rw [neg_mul_neg]; exact hqσ.symm
  have hsqrt : sqrtSigmaR (cutCR cd 0) (cutPR cd 0) = (q' : ℝ) := by
    have h1 : ((sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ) = ((q' : ℚ) : ℝ) ^ 2 := by
      rw [← hq'sq]; push_cast; ring
    rw [sqrtSigmaR, ← QMCLeafB.EngineIterates.cast_sigmaQ, h1, Real.sqrt_sq_eq_abs,
      abs_of_pos (by exact_mod_cast hq'pos)]
  have hCat : Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1
      = fun i => (((QMCLeafB.CruxM1.gammaQ (n * n) (cd 0).rho / q') * (cd 0).p i : ℚ) : ℝ) := by
    funext i
    rw [cat_one_formula]
    simp only [Pi.smul_apply, smul_eq_mul, cutPR, hsqrt]
    push_cast
    rw [QMCLeafB.CruxM1.cast_gammaQ]
  rw [hCat]
  exact ratVec_flatQ _

/-- **THE EXACT CHARACTERIZATION AT ROUND 1.**  The engine's accumulated centre after one round is
a rational point of `ℝ^{n*n}` **iff** the recorded `σ_0 = c_0 ⬝ p_0` is a rational square.  Not
"if": the square condition is *equivalent* to the centre being rational, so no state coding can
produce a rational accumulated centre at a non-square `σ`. -/
theorem ratVec_cat_one_iff {n : ℕ} (cd : ℕ → CutData (n * n))
    (hσ : 0 < sigmaQ (cd 0).c (cd 0).p)
    (hγ : gammaR (n * n) ((cd 0).rho : ℝ) ≠ 0) :
    RatVec n (Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1)
      ↔ IsSquare (sigmaQ (cd 0).c (cd 0).p) := by
  constructor
  · intro h
    exact isSquare_sigma_of_rational_step cd 0 hσ hγ (ratVec_zero n) h
  · exact ratVec_cat_one_of_isSquare cd hσ


/-! ### The frozen-centre escape, and why the campaign's own parameters forbid it -/

theorem gammaR_eq_zero_iff {N : ℕ} {ρ : ℝ} : gammaR N ρ = 0 ↔ ρ = 1 := by
  rw [gammaR, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · have : (0:ℝ) < (N:ℝ) + 1 := by positivity
      linarith
  · intro h; left; linarith

theorem gammaQ_eq_zero_iff {N : ℕ} {ρ : ℚ} : QMCLeafB.CruxM1.gammaQ N ρ = 0 ↔ ρ = 1 := by
  rw [QMCLeafB.CruxM1.gammaQ, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · have : ((N:ℚ) + 1) ≠ 0 := by positivity
      exact absurd h this
  · intro h; left; linarith

/-- **The contraction factor at depth `1` is `((N−1)/(N+1))^{N−1} ≤ 1`**, and `rho0R` is the
determinant contraction of the GLS step, decreasing in the depth.  So `rho0R > 1` forces `ρ < 1`. -/
theorem pow_eq_mul_pow_sub_one {a : ℝ} {n : ℕ} (hn : 1 ≤ n) : a ^ n = a * a ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ k => rw [pow_succ']; simp

theorem rho0R_le_one_of_one_le_rho {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    rho0R N ρ ≤ 1 := by
  have hNR : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have hNp : (0:ℝ) < (N:ℝ) + 1 := by linarith
  have hd : (0:ℝ) < (N:ℝ) + ρ := by linarith
  have hd1 : (N:ℝ) + 1 ≤ (N:ℝ) + ρ := by linarith
  have hNr1 : 1 ≤ N := by omega
  have hmN : ((N:ℝ) - 1) ^ N = ((N:ℝ) - 1) * ((N:ℝ) - 1) ^ (N - 1) :=
    pow_eq_mul_pow_sub_one hNr1
  have hA : ((N:ℝ) ^ 2 - 1) ^ N * ((N:ℝ) + 1)
      = ((N:ℝ) - 1) ^ N * ((N:ℝ) + 1) ^ (N + 1) := by
    rw [show ((N:ℝ) ^ 2 - 1) = ((N:ℝ) - 1) * ((N:ℝ) + 1) from by ring, mul_pow, pow_succ]
    ring
  have hmono : ((N:ℝ) + 1) ^ (2 * N) ≤ ((N:ℝ) + ρ) ^ (2 * N) :=
    pow_le_pow_left₀ (le_of_lt hNp) hd1 _
  have hpow : ((N:ℝ) - 1) ^ (N - 1) ≤ ((N:ℝ) + 1) ^ (N - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hstep : ((N:ℝ) - 1) ^ (N - 1) * ((N:ℝ) + 1) ^ (N + 1)
      ≤ ((N:ℝ) + 1) ^ (N - 1) * ((N:ℝ) + 1) ^ (N + 1) :=
    mul_le_mul_of_nonneg_right hpow (by positivity)
  have hcomb : ((N:ℝ) + 1) ^ (N - 1) * ((N:ℝ) + 1) ^ (N + 1) = ((N:ℝ) + 1) ^ (2 * N) := by
    rw [← pow_add]
    congr 1
    omega
  have hB : ((N:ℝ) - 1) ^ N * ((N:ℝ) + 1) ^ (N + 1)
      ≤ ((N:ℝ) - 1) * ((N:ℝ) + 1) ^ (2 * N) := by
    rw [hmN]
    calc ((N:ℝ) - 1) * ((N:ℝ) - 1) ^ (N - 1) * ((N:ℝ) + 1) ^ (N + 1)
        = ((N:ℝ) - 1) * (((N:ℝ) - 1) ^ (N - 1) * ((N:ℝ) + 1) ^ (N + 1)) := by ring
      _ ≤ ((N:ℝ) - 1) * ((N:ℝ) + 1) ^ (2 * N) :=
          mul_le_mul_of_nonneg_left (hcomb ▸ hstep) (le_of_lt hN1)
  rw [rho0R, div_le_one (by positivity), hA]
  exact le_trans hB (mul_le_mul_of_nonneg_left hmono (le_of_lt hN1))

/-- **The campaign's own parameters exclude the frozen centre.**  `RunParams.hhalve` needs
`rho0R (n²) rmax > 1`, and `rho0R ≤ 1` at every depth `ρ ≥ 1`; hence `rmax < 1`, so every recorded
depth `ρ_k ≤ rmax` is `< 1` and its `γ` is nonzero. -/
theorem rmax_lt_one_of_halve {N : ℕ} (hN : 2 ≤ N) {rmax : ℝ} (h0 : 0 ≤ rmax) {m : ℕ}
    (hh : (Real.sqrt (rho0R N rmax))⁻¹ ^ m ≤ 1 / 2) : rmax < 1 := by
  have hpos : 0 < rho0R N rmax := rho0R_pos hN h0
  have hgt : 1 < rho0R N rmax := by
    by_contra hcon
    push Not at hcon
    have hs1 : Real.sqrt (rho0R N rmax) ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hcon
    have hspos : 0 < Real.sqrt (rho0R N rmax) := Real.sqrt_pos.mpr hpos
    have hinv : 1 ≤ (Real.sqrt (rho0R N rmax))⁻¹ := by
      rw [← one_div]
      exact (one_le_div hspos).mpr hs1
    have hge : 1 ≤ (Real.sqrt (rho0R N rmax))⁻¹ ^ m := one_le_pow₀ hinv
    linarith
  by_contra hcon
  push Not at hcon
  have := rho0R_le_one_of_one_le_rho hN (ρ := rmax) hcon
  linarith


/-! ### At the record: the same obstruction, and the ledger's total budget -/

theorem runParams_rmax_lt_one {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hG : 2 ≤ G.n) : P.rmax < 1 := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have h0 : (0 : ℝ) ≤ (P.rmax : ℝ) := by exact_mod_cast P.hrmax
  have h := rmax_lt_one_of_halve hN h0 P.hhalve
  exact_mod_cast h

theorem runParts_rho_ne_one {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hG : 2 ≤ G.n) (k : ℕ)
    (hk : k < P.K * P.m) (hok : B.ok k = false) : (B.cd k).rho ≠ 1 := by
  intro h
  have h1 := B.hle k hk hok
  rw [h] at h1
  have h2 := runParams_rmax_lt_one P hG
  linarith

theorem runParts_gamma_ne_zero {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hG : 2 ≤ G.n) (k : ℕ)
    (hk : k < P.K * P.m) (hok : B.ok k = false) :
    gammaR (G.n * G.n) ((B.cd k).rho : ℝ) ≠ 0 := by
  intro h
  rw [gammaR_eq_zero_iff] at h
  exact runParts_rho_ne_one B hG k hk hok (Rat.cast_injective (by rw [h]; simp))

/-- **THE (B1) NO-GO AT THE RECORD.**  In any `RunParts` (any bit, any threshold, any parameters
with `2 ≤ G.n`), if the engine's accumulated centre is a rational point at two consecutive rounds,
then the recorded `σ_k` is a rational square.  The shallow cap `ρ_k ≤ rmax < 1` is what makes the
frozen-centre escape unavailable; `RunParams.hhalve` is what makes `rmax < 1`. -/
theorem runParts_isSquare_of_rational_centres {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hG : 2 ≤ G.n) (k : ℕ)
    (hk : k < P.K * P.m) (hok : B.ok k = false)
    (hσ : 0 < sigmaQ (B.cd k).c (B.cd k).p)
    (h0 : RatVec G.n (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k))
    (h1 : RatVec G.n (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (k + 1))) :
    IsSquare (sigmaQ (B.cd k).c (B.cd k).p) :=
  isSquare_sigma_of_rational_step B.cd k hσ (runParts_gamma_ne_zero B hG k hk hok) h0 h1

/-- **THE LEDGER HAS NO SLACK.**  `hcheck` together with the shallow cap `ρ ≤ rmax` gives exactly
`del k ≤ rmax · √σ_k`: the recorded depth cannot exceed `rmax·√σ_k`.  So a price `p_k` charged on
top of the oracle's own margin `margin_k` fits only in the room `(rmax − margin_k/√σ_k)·√σ_k`, and
never out of a "free" budget. -/
theorem runParts_del_le_rmax_sqrt {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (k : ℕ) (hk : k < P.K * P.m)
    (hok : B.ok k = false) (hσ : 0 < sigmaQ (B.cd k).c (B.cd k).p) :
    (B.del k : ℝ) ≤ (P.rmax : ℝ) * Real.sqrt ((sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ) := by
  have hd0 := B.hdel0 k hk hok
  have hr0 := B.hrho k hk hok
  have hchk := B.hcheck k hk hok
  have hle := B.hle k hk hok
  have hsq : ((B.del k : ℚ)) ^ 2 ≤ ((P.rmax : ℚ)) ^ 2 * (sigmaQ (B.cd k).c (B.cd k).p) := by
    have h1 : ((B.cd k).rho) ^ 2 ≤ (P.rmax) ^ 2 := by nlinarith
    have h2 : 0 ≤ (sigmaQ (B.cd k).c (B.cd k).p) := le_of_lt hσ
    nlinarith
  have hcast : (((B.del k : ℚ) : ℝ)) ^ 2
      ≤ (((P.rmax : ℚ) : ℝ)) ^ 2 * ((sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ) := by
    exact_mod_cast hsq
  have hd0R : (0 : ℝ) ≤ ((B.del k : ℚ) : ℝ) := by exact_mod_cast hd0
  have hrmR : (0 : ℝ) ≤ ((P.rmax : ℚ) : ℝ) := by exact_mod_cast P.hrmax
  calc ((B.del k : ℚ) : ℝ) = Real.sqrt ((((B.del k : ℚ) : ℝ)) ^ 2) := (Real.sqrt_sq hd0R).symm
    _ ≤ Real.sqrt ((((P.rmax : ℚ) : ℝ)) ^ 2 * ((sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ)) :=
        Real.sqrt_le_sqrt hcast
    _ = ((P.rmax : ℚ) : ℝ) * Real.sqrt ((sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hrmR]

/-! ### Is the square condition satisfiable at all?  Yes — and at round `0` it is explicit -/

/-- At the campaign's own init shape `A₀ = M⁻¹ • 1` the recorded `σ` is `M` times a rational sum
of squares, so its square class is the class of `M·‖c₀‖²`. -/
theorem sigmaQ_initShape {N : ℕ} {M : ℚ} (hM : M ≠ 0) {c p : Fin N → ℚ}
    (hw : QMCLeafB.Boundary.initShapeOf N M *ᵥ p = c) :
    sigmaQ c p = M * (dotProduct c c) := by
  have hp : p = M • c := by
    have h := congrArg (fun v => (M • v)) hw
    simpa [QMCLeafB.Boundary.initShapeOf, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, mul_inv_cancel₀ hM] using h
  rw [hp, sigmaQ, dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The class is not a normalisation artefact**: rescaling the recorded normal by `t ≠ 0`
multiplies `σ` by `t²`, which does not change whether it is a square.  So no renormalisation of the
state or the normal can make a rational accumulated centre at a non-square `σ` possible. -/
theorem sigma_class_scale_free {n : ℕ} {t : ℚ} (ht : t ≠ 0) (c p : Fin n → ℚ) :
    IsSquare (sigmaQ (t • c) (t • p)) ↔ IsSquare (sigmaQ c p) :=
  isSquare_sigmaQ_smul ht c p

/-- **NON-VACUITY at a square init radius**: at `M = 4` with the coordinate normal, the accumulated
centre after one round IS rational.  Compare `QMCLeafB.CruxM1.not_hctr_initShape_two` (`M = 2`):
the same step, the same normal, a different arithmetic class. -/
theorem coordCd_four_ratVec : RatVec 2 (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ)
    (QMCLeafB.CruxM1.coordCd 4) 1) := by
  have hσ : 0 < sigmaQ (QMCLeafB.CruxM1.coordCd 4 0).c (QMCLeafB.CruxM1.coordCd 4 0).p := by
    rw [QMCLeafB.CruxM1.sigmaQ_coord]; norm_num
  have hγ : gammaR (2 * 2) (((QMCLeafB.CruxM1.coordCd 4) 0).rho : ℝ) ≠ 0 := by
    have hρ : (((QMCLeafB.CruxM1.coordCd 4) 0).rho : ℝ) = 0 := by
      simp [QMCLeafB.CruxM1.coordCd]
    rw [hρ]
    norm_num [gammaR]
  refine (ratVec_cat_one_iff (n := 2) (QMCLeafB.CruxM1.coordCd 4) hσ hγ).mpr ?_
  rw [QMCLeafB.CruxM1.sigmaQ_coord]
  exact ⟨2, by norm_num⟩

/-- At `M = 2` the same trajectory has NO rational presentation of its accumulated centre
(`QMCLeafB.CruxM1.not_hctr_initShape_two`, restated in `RatVec` form). -/
theorem coordCd_two_not_ratVec :
    ¬ RatVec 2 (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ) (QMCLeafB.CruxM1.coordCd 2) 1) :=
  QMCLeafB.CruxM1.not_hctr_initShape_two


/-! ### The *weak* form of (B1): the price can vanish only on a rational projection -/

theorem dot_cast {N : ℕ} (u v : Fin N → ℚ) :
    (fun i => (u i : ℝ)) ⬝ᵥ (fun i => (v i : ℝ)) = ((u ⬝ᵥ v : ℚ) : ℝ) := by
  simp [dotProduct]

theorem dot_cast_smul_right {N : ℕ} (u : Fin N → ℚ) (r : ℝ) (v : Fin N → ℝ) :
    (fun i => (u i : ℝ)) ⬝ᵥ (r • v) = r * ((fun i => (u i : ℝ)) ⬝ᵥ v) := by
  rw [dotProduct_smul, smul_eq_mul]

/-- **The price is a rational-dot-product distance.**  A rational normal `n` can present the
engine's centre `A` with zero price only if `n ⬝ A` is rational: with the programme's centre `a`
rational, `n ⬝ (A − a) = 0` puts `n ⬝ A = n ⬝ a ∈ ℚ`.  So the (B1) price is not a slack variable
that a clever coding can nudge to zero — it vanishes only on a rational projection of `Cat k`. -/
theorem price_zero_needs_rational_dot {N : ℕ} (nrm a : Fin N → ℚ) (A : Fin N → ℝ)
    (h : (fun i => (nrm i : ℝ)) ⬝ᵥ (A - fun i => (a i : ℝ)) = 0) :
    ∃ q : ℚ, (fun i => (nrm i : ℝ)) ⬝ᵥ A = (q : ℝ) := by
  refine ⟨nrm ⬝ᵥ a, ?_⟩
  rw [dotProduct_sub] at h
  have h2 := dot_cast nrm a
  linarith

/-- **THE WEAK (B1) IS ALSO ARITHMETIC.**  At round `1` — where the programme's centre is `0`, so
the price at round `0` already vanishes — a rational normal `nrm` can present the engine's
accumulated centre at ZERO price only if either `nrm` is `A₀`-orthogonal to the round's witness `p₀`
or `σ₀` is a rational square.  So even the price-zero-for-the-normal-used reading of (B1) forces
the square condition off a codimension-one slice. -/
theorem price_zero_at_one_forces_square_or_orth {n : ℕ} (cd : ℕ → CutData (n * n))
    (hσ : 0 < sigmaQ (cd 0).c (cd 0).p)
    (hγ : gammaR (n * n) ((cd 0).rho : ℝ) ≠ 0)
    {nrm a : Fin (n * n) → ℚ}
    (h : (fun i => (nrm i : ℝ)) ⬝ᵥ
      (Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1 - fun i => (a i : ℝ)) = 0) :
    nrm ⬝ᵥ (cd 0).p = 0 ∨ IsSquare (sigmaQ (cd 0).c (cd 0).p) := by
  classical
  set N₀ : ℚ := nrm ⬝ᵥ (cd 0).p with hN₀
  set q : ℚ := nrm ⬝ᵥ a with hq
  have hσR : (0:ℝ) < sigmaR (cutCR cd 0) (cutPR cd 0) := by
    rw [← QMCLeafB.EngineIterates.cast_sigmaQ]; exact_mod_cast hσ
  have hsqrt : sqrtSigmaR (cutCR cd 0) (cutPR cd 0) ≠ 0 := (Real.sqrt_pos.mpr hσR).ne'
  have hcut : cutPR cd 0 = fun i => ((cd 0).p i : ℝ) := rfl
  have h1 : (fun i => (nrm i : ℝ)) ⬝ᵥ Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1 = (q : ℝ) := by
    rw [hq]
    have h2 : (fun i => (nrm i : ℝ)) ⬝ᵥ (fun i => (a i : ℝ)) = ((nrm ⬝ᵥ a : ℚ) : ℝ) :=
      dot_cast nrm a
    rw [dotProduct_sub] at h
    linarith
  have hdot : ((fun i => (nrm i : ℝ)) ⬝ᵥ fun i => ((cd 0).p i : ℝ)) = (N₀ : ℝ) := by
    rw [hN₀, dot_cast]
  rw [cat_one_formula, dot_cast_smul_right, hcut, hdot] at h1
  -- `h1 : (γ/√σ) * N₀ = q`
  rcases eq_or_ne N₀ 0 with h0 | h0
  · exact Or.inl h0
  refine Or.inr ?_
  have hqne : q ≠ 0 := by
    intro hq0
    rw [hq0] at h1
    have hz : (gammaR (n * n) ((cd 0).rho : ℝ) / sqrtSigmaR (cutCR cd 0) (cutPR cd 0))
        * (N₀ : ℝ) = 0 := by simpa using h1
    rcases mul_eq_zero.mp hz with hh | hh
    · rcases div_eq_zero_iff.mp hh with h1' | h1'
      · exact hγ h1'
      · exact hsqrt h1'
    · exact h0 (Rat.cast_injective (by rw [hh]; simp))
  have hqR : (q : ℝ) ≠ 0 := fun hh => hqne (Rat.cast_injective (by rw [hh]; simp))
  have hN₀R : (N₀ : ℝ) ≠ 0 := fun hh => h0 (Rat.cast_injective (by rw [hh]; simp))
  have hmul : (q : ℝ) * sqrtSigmaR (cutCR cd 0) (cutPR cd 0)
      = gammaR (n * n) ((cd 0).rho : ℝ) * (N₀ : ℝ) := by
    rw [← h1]; field_simp
  have hsqrt_eq : sqrtSigmaR (cutCR cd 0) (cutPR cd 0)
      = gammaR (n * n) ((cd 0).rho : ℝ) * (N₀ : ℝ) / (q : ℝ) := by
    rw [eq_div_iff hqR, mul_comm, hmul]
  have hσeq : ((sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ)
      = sqrtSigmaR (cutCR cd 0) (cutPR cd 0) ^ 2 := by
    rw [QMCLeafB.EngineIterates.cast_sigmaQ]
    exact (Real.sq_sqrt hσR.le).symm
  have hsq : ((sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ)
      = (gammaR (n * n) ((cd 0).rho : ℝ) * (N₀ : ℝ) / (q : ℝ)) ^ 2 := by
    rw [hσeq, hsqrt_eq]
  refine ⟨QMCLeafB.CruxM1.gammaQ (n * n) (cd 0).rho * N₀ / q, ?_⟩
  have hfin : (((QMCLeafB.CruxM1.gammaQ (n * n) (cd 0).rho * N₀ / q) ^ 2 : ℚ) : ℝ)
      = ((sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ) := by
    rw [hsq]
    push_cast
    rw [QMCLeafB.CruxM1.cast_gammaQ]
  have hfin' : (QMCLeafB.CruxM1.gammaQ (n * n) (cd 0).rho * N₀ / q) ^ 2
      = sigmaQ (cd 0).c (cd 0).p := by
    exact_mod_cast hfin
  simpa [pow_two] using hfin'.symm


/-! ### The (A) horn at the record level -/

/-- **Case (A).**  A round that reports `ok` makes the run's bit `true` — `anyOk`'s own spec, no
geometry and no search.  Together with the repaired membership gate (`OkTopB.programGate`, m5/ph36)
this is the whole content of the coordinator's case (A). -/
theorem bit_true_of_some_ok {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) {k : ℕ} (hk : k < P.K * P.m)
    (hok : B.ok k = true) : o G t = true := by
  rw [B.hverdict, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  exact ⟨k, hk, hok⟩

/-- **The packaged verdict on (B1).**  At the campaign's parameters, in any record: if the engine's
accumulated centre is rational at *every* round, then every recorded `σ_k` is a rational square.
Since `runParams_rmax_lt_one` is a theorem about `RunParams` (not a choice of ours), there is no
parameter setting of the campaign at which the centre identity could be had for a non-square `σ`. -/
theorem centre_identity_forces_squares {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hG : 2 ≤ G.n)
    (hσpos : ∀ k, k < P.K * P.m → 0 < sigmaQ (B.cd k).c (B.cd k).p)
    (hrat : ∀ k, RatVec G.n (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k))
    (k : ℕ) (hk : k < P.K * P.m) (hok : B.ok k = false) :
    IsSquare (sigmaQ (B.cd k).c (B.cd k).p) :=
  runParts_isSquare_of_rational_centres B hG k hk hok (hσpos k hk) (hrat k) (hrat (k + 1))


/-- **The record, with the budget substituted**: at every cut round the whole relaxation lies in
the halfspace of depth `rmax·√σ_k` at the accumulated centre, along the recorded normal.  This is
the exact form of case (B)'s content at a fixed stream — the "one signed scalar inequality per
round" that the price must reproduce. -/
theorem runParts_cut_ge_rmax {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (k : ℕ) (hk : k < P.K * P.m)
    (hok : B.ok k = false) (hσ : 0 < sigmaQ (B.cd k).c (B.cd k).p) :
    ∀ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
      -((P.rmax : ℚ) : ℝ) * Real.sqrt ((sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ)
        ≤ cutCR B.cd k ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) := by
  intro z hz
  have h1 := B.hcut k hk hok z hz
  have h2 := runParts_del_le_rmax_sqrt B k hk hok hσ
  linarith

/-- **Case (B) at a fixed stream, in one line.**  If the recorded normal stream is the one the
price was computed for, then the record's content is exactly
`margin_k + n_k ⬝ (Cat k − flat cX k) ≤ rmax·√σ_k` — the signed scalar inequality that (B2) has to
meet, with the oracle's own margin `margin_k` already spent inside the budget. -/
theorem case_B_shape {N : ℕ} {margin del rmax σ : ℚ} {nrm : Fin N → ℚ}
    {a : Fin N → ℝ} {cX : Fin N → ℝ}
    (hσ : 0 < σ) (hd : 0 ≤ del) (hr : 0 ≤ rmax)
    (hprice : ((margin : ℚ) : ℝ) - (fun i => (nrm i : ℝ)) ⬝ᵥ (cX - a) ≤ ((del : ℚ) : ℝ))
    (hledger : ((del : ℚ) : ℝ) ≤ (rmax : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) :
    ((margin : ℚ) : ℝ) ≤ (fun i => (nrm i : ℝ)) ⬝ᵥ (cX - a)
      + (rmax : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) := by
  linarith

#print axioms QMCLeafB.B1D37M5.flat_sub
#print axioms QMCLeafB.B1D37M5.ratVec_flatQ
#print axioms QMCLeafB.B1D37M5.ratVec_sub
#print axioms QMCLeafB.B1D37M5.ratVec_zero
#print axioms QMCLeafB.B1D37M5.cat_step_eq
#print axioms QMCLeafB.B1D37M5.isSquare_sigma_of_rational_step
#print axioms QMCLeafB.B1D37M5.sigmaQ_smul
#print axioms QMCLeafB.B1D37M5.isSquare_sigmaQ_smul
#print axioms QMCLeafB.B1D37M5.cat_one_formula
#print axioms QMCLeafB.B1D37M5.ratVec_cat_one_of_isSquare
#print axioms QMCLeafB.B1D37M5.ratVec_cat_one_iff
#print axioms QMCLeafB.B1D37M5.gammaR_eq_zero_iff
#print axioms QMCLeafB.B1D37M5.gammaQ_eq_zero_iff
#print axioms QMCLeafB.B1D37M5.pow_eq_mul_pow_sub_one
#print axioms QMCLeafB.B1D37M5.rho0R_le_one_of_one_le_rho
#print axioms QMCLeafB.B1D37M5.rmax_lt_one_of_halve
#print axioms QMCLeafB.B1D37M5.runParams_rmax_lt_one
#print axioms QMCLeafB.B1D37M5.runParts_rho_ne_one
#print axioms QMCLeafB.B1D37M5.runParts_gamma_ne_zero
#print axioms QMCLeafB.B1D37M5.runParts_isSquare_of_rational_centres
#print axioms QMCLeafB.B1D37M5.runParts_del_le_rmax_sqrt
#print axioms QMCLeafB.B1D37M5.sigmaQ_initShape
#print axioms QMCLeafB.B1D37M5.sigma_class_scale_free
#print axioms QMCLeafB.B1D37M5.coordCd_four_ratVec
#print axioms QMCLeafB.B1D37M5.coordCd_two_not_ratVec
#print axioms QMCLeafB.B1D37M5.dot_cast
#print axioms QMCLeafB.B1D37M5.dot_cast_smul_right
#print axioms QMCLeafB.B1D37M5.price_zero_needs_rational_dot
#print axioms QMCLeafB.B1D37M5.price_zero_at_one_forces_square_or_orth
#print axioms QMCLeafB.B1D37M5.bit_true_of_some_ok
#print axioms QMCLeafB.B1D37M5.centre_identity_forces_squares
#print axioms QMCLeafB.B1D37M5.runParts_cut_ge_rmax
#print axioms QMCLeafB.B1D37M5.case_B_shape

end QMCLeafB.B1D37M5


