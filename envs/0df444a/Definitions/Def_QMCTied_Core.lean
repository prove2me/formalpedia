-- Prove2me | Definitions.Def_QMCTied_Core
-- name    : QMCTied_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:13:29.538218+00:00
-- url     : https://prove2.me/theorems/b3bfafc5-db79-4eca-bf99-f45636b1bb57
-- title:
--   Soundness and accuracy of the penalty supergradient iteration
-- statement:
--   For a tied-entry instance with normalized objective: **soundness**, the best recorded value is at most the objective of some feasible point; **accuracy**, every feasible value is at most the best recorded value plus $1/D_2+6N^2\delta$ plus an explicit convergence error $\frac{N^2D}{2\eta T}+\frac{2N^2}{\eta}+\frac{N^2(4N^2\eta+1)^2}{2\eta D}$. The proof uses an exact supergradient inequality for the penalized objective, nonexpansiveness of clamping to the box, and the matrix power lemma for the certified shift.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter
import Definitions.Def_QMCTied_Defs

/-!
Soundness and accuracy of the integer penalty supergradient iteration for tied-entry SDPs.
-/

namespace QMCTied
open Matrix QMCSub
open scoped BigOperators

variable {N : ℕ} {κ : Type} [DecidableEq κ]

set_option linter.unusedSectionVars false

/-- The convergence error of the iteration, as a function of the parameters. -/
noncomputable def convErr (N : ℕ) (P : Par) (T : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * (P.D : ℝ) / (2 * (P.eta : ℝ) * T) + 2 * (N : ℝ) ^ 2 / (P.eta : ℝ) +
    (N : ℝ) ^ 2 * ((P.eta : ℝ) * (4 * (N : ℝ) ^ 2) + 1) ^ 2 / (2 * (P.eta : ℝ) * (P.D : ℝ))

/-! ### Elementary facts about the iteration -/

theorem clampZ_abs (D x : ℤ) (hD : 0 ≤ D) : |clampZ D x| ≤ D := by
  unfold clampZ
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by omega) (min_le_left _ _)⟩

theorem lamSeq_zero (I : Inst N κ) (P : Par) : lamSeq I P 0 = lam0 I P := rfl

theorem lamSeq_succ (I : Inst N κ) (P : Par) (k : ℕ) :
    lamSeq I P (k + 1) = next I P (lamSeq I P k) := by
  unfold lamSeq
  rw [Function.iterate_succ_apply']

theorem bestSeq_zero (I : Inst N κ) (P : Par) : bestSeq I P 0 = 0 := rfl

theorem bestSeq_succ (I : Inst N κ) (P : Par) (k : ℕ) :
    bestSeq I P (k + 1) = bestStep I P (lamSeq I P k) (bestSeq I P k) := rfl

/-- The iterates stay in the box and keep the normalization. -/
theorem lamSeq_box (I : Inst N κ) (P : Par) (hD : 0 ≤ P.D) (k : ℕ) (c : κ) :
    |lamSeq I P k c| ≤ P.D := by
  induction k generalizing c with
  | zero =>
    rw [lamSeq_zero]
    unfold lam0
    split_ifs
    · rw [abs_of_nonneg hD]
    · simpa using hD
  | succ k ih =>
    rw [lamSeq_succ]
    simp only [next]
    split_ifs
    · exact ih c
    · exact clampZ_abs _ _ hD

theorem lamSeq_k0 (I : Inst N κ) (P : Par) (k : ℕ) : lamSeq I P k I.k0 = P.D := by
  induction k with
  | zero => simp [lamSeq_zero, lam0]
  | succ k ih => rw [lamSeq_succ]; simp [next, ih]

/-- The recorded best value is nonnegative and bounded. -/
theorem bestSeq_nonneg (I : Inst N κ) (P : Par) (T : ℕ) : 0 ≤ bestSeq I P T := by
  induction T with
  | zero => rw [bestSeq_zero]
  | succ T ih => rw [bestSeq_succ]; exact le_trans ih (le_max_left _ _)

/-! ### The integer matrices -/

theorem cls_self (I : Inst N κ) (hI : I.Good) (i : Fin N) : I.cls i i = I.k0 :=
  (hI.cls_diag i i).mpr rfl

theorem Mz_apply (I : Inst N κ) (D : ℤ) (lam : κ → ℤ) (i j : Fin N) :
    Mz I D lam i j = (if i = j then (N : ℤ) * D else 0) - I.sgn i j * lam (I.cls i j) := by
  show ((N : ℤ) * D) • ((1 : Matrix (Fin N) (Fin N) ℤ) i j) - I.sgn i j * lam (I.cls i j) = _
  rw [Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem Mz_entry_abs_le (I : Inst N κ) (hI : I.Good) (D : ℤ) (hD : 0 ≤ D)
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ D) (i j : Fin N) :
    |Mz I D lam i j| ≤ (N : ℤ) * D + D := by
  rw [Mz_apply]
  have h1 : |I.sgn i j * lam (I.cls i j)| ≤ D := by
    rw [abs_mul]
    calc |I.sgn i j| * |lam (I.cls i j)| ≤ 1 * D :=
          mul_le_mul (hI.sgn_abs i j) (hbox _) (abs_nonneg _) zero_le_one
      _ = D := one_mul D
  have h2 : (0 : ℤ) ≤ N * D := mul_nonneg (Int.natCast_nonneg N) hD
  rw [abs_le] at h1 ⊢
  split_ifs <;> constructor <;> linarith [h1.1, h1.2]

theorem Mz_symm (I : Inst N κ) (hI : I.Good) (D : ℤ) (lam : κ → ℤ) (i j : Fin N) :
    Mz I D lam j i = Mz I D lam i j := by
  rw [Mz_apply, Mz_apply, hI.sgn_symm j i, hI.cls_symm j i]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem Qz_symm (I : Inst N κ) (hI : I.Good) (D : ℤ) (K : ℕ) (lam : κ → ℤ) (i j : Fin N) :
    Qz I D K lam j i = Qz I D K lam i j := by
  have hT : (Mz I D lam)ᵀ = Mz I D lam := by
    ext a b
    exact Mz_symm I hI D lam a b
  have h : (Qz I D K lam)ᵀ = Qz I D K lam := by
    unfold Qz
    rw [Matrix.transpose_pow, hT]
  have h2 := congrFun (congrFun h i) j
  simpa using h2

theorem trace_Mz (I : Inst N κ) (hI : I.Good) (D : ℤ) (lam : κ → ℤ) (hk0 : lam I.k0 = D) :
    (Mz I D lam).trace = N * (N * D - D) := by
  simp [Matrix.trace, Mz_apply, hI.sgn_diag, cls_self I hI, hk0]
  ring

/-! ### Real casts -/

theorem Gam_apply (I : Inst N κ) (f : κ → ℝ) (i j : Fin N) :
    Gam I f i j = (I.sgn i j : ℝ) * f (I.cls i j) := rfl

theorem Gam_symm (I : Inst N κ) (hI : I.Good) (f : κ → ℝ) (i j : Fin N) :
    Gam I f j i = Gam I f i j := by
  rw [Gam_apply, Gam_apply, hI.sgn_symm j i, hI.cls_symm j i]

theorem Gam_herm (I : Inst N κ) (hI : I.Good) (f : κ → ℝ) : (Gam I f).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by rw [star_trivial]; exact Gam_symm I hI f i j

theorem sgn_abs_real (I : Inst N κ) (hI : I.Good) (i j : Fin N) : |(I.sgn i j : ℝ)| ≤ 1 := by
  have h := hI.sgn_abs i j
  exact_mod_cast h

theorem Gam_abs_le (I : Inst N κ) (hI : I.Good) (f : κ → ℝ) (d : ℝ) (hf : ∀ c, |f c| ≤ d)
    (i j : Fin N) : |Gam I f i j| ≤ d := by
  rw [Gam_apply, abs_mul]
  calc |(I.sgn i j : ℝ)| * |f (I.cls i j)| ≤ 1 * d :=
        mul_le_mul (sgn_abs_real I hI i j) (hf _) (abs_nonneg _) zero_le_one
    _ = d := one_mul d

theorem trace_castR (A : Matrix (Fin N) (Fin N) ℤ) : (castM A).trace = (A.trace : ℝ) := by
  simp only [Matrix.trace, Matrix.diag_apply, castM_apply]
  rw [Int.cast_sum]

theorem castM_Mz (I : Inst N κ) (D : ℤ) (lam : κ → ℤ) :
    castM (Mz I D lam) = ((N : ℝ) * (D : ℝ)) • (1 : Matrix (Fin N) (Fin N) ℝ) -
      Gam I (fun c => (lam c : ℝ)) := by
  ext i j
  rw [castM_apply, Mz_apply]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Gam_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem castM_Qz (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) :
    castM (Qz I D K lam) = castM (Mz I D lam) ^ (2 * K) := by
  unfold Qz
  rw [map_pow]

theorem tau_cast (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) :
    (tau I D K lam : ℝ) = (castM (Mz I D lam) ^ (2 * K)).trace := by
  rw [← castM_Qz, trace_castR]
  rfl

theorem rnum_cast (I : Inst N κ) (hI : I.Good) (D : ℤ) (K : ℕ) (lam : κ → ℤ) :
    (rnum I D K lam : ℝ) = (castM (Mz I D lam) * castM (Qz I D K lam)).trace := by
  simp only [rnum, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, castM_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Qz_symm I hI D K lam i j]

/-- A symmetric real matrix with entries bounded by `d` is dominated by `N d`. -/
theorem shift_psd (A : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 ≤ d) (hA : A.IsHermitian)
    (hbd : ∀ i j, |A i j| ≤ d) :
    (((N : ℝ) * d) • (1 : Matrix (Fin N) (Fin N) ℝ) - A).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    have h := hA.apply i j
    simp only [star_trivial] at h ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, h, smul_eq_mul]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
    have h1 : x ⬝ᵥ (A *ᵥ x) ≤ d * (∑ i, |x i|) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      calc x i * (A i j * x j) ≤ |x i * (A i j * x j)| := le_abs_self _
        _ = |A i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
        _ ≤ d * (|x i| * |x j|) := mul_le_mul_of_nonneg_right (hbd i j) (by positivity)
    have h2 : (∑ i, |x i|) ^ 2 ≤ (N : ℝ) * (x ⬝ᵥ x) := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin N => |x i|)
      simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
      simpa [dotProduct, sq] using h
    nlinarith [mul_le_mul_of_nonneg_left h2 hd]

theorem Mr_psd (I : Inst N κ) (hI : I.Good) (D : ℤ) (hD : 0 ≤ D) (lam : κ → ℤ)
    (hbox : ∀ c, |lam c| ≤ D) : (castM (Mz I D lam)).PosSemidef := by
  rw [castM_Mz]
  refine shift_psd _ _ (by exact_mod_cast hD) (Gam_herm I hI _) (Gam_abs_le I hI _ _ ?_)
  intro c
  have h := hbox c
  exact_mod_cast h

theorem Qr_psd (I : Inst N κ) (hI : I.Good) (D : ℤ) (hD : 0 ≤ D) (K : ℕ) (lam : κ → ℤ)
    (hbox : ∀ c, |lam c| ≤ D) : (castM (Qz I D K lam)).PosSemidef := by
  rw [castM_Qz]
  exact psd_even_pow (Mr_psd I hI D hD lam hbox).1 K

/-- The power matrix is positive semidefinite with positive trace on the box. -/
theorem tau_pos (I : Inst N κ) (hI : I.Good) (D : ℤ) (K : ℕ) (hN : 2 ≤ N) (hD : 0 < D)
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ D) (hk0 : lam I.k0 = D) : 0 < tau I D K lam := by
  have hM := Mr_psd I hI D hD.le lam hbox
  have htr : 0 < (castM (Mz I D lam)).trace := by
    rw [trace_castR, trace_Mz I hI D lam hk0]
    push_cast
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h3 : (0 : ℝ) < D := by exact_mod_cast hD
    have h4 : (0 : ℝ) < (N : ℝ) * D - D := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < (N : ℝ) - 1) h3]
    exact mul_pos (by linarith) h4
  have h := psd_pow_trace_pos hM htr (2 * K)
  rw [← tau_cast] at h
  exact_mod_cast h

/-! ### The certified shift -/

theorem rank_one_bound (I : Inst N κ) (hI : I.Good) (P : Par) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (v : Fin N → ℝ) :
    ((P.dN : ℝ) - 1) * (v ⬝ᵥ (castM (Mz I P.D lam) *ᵥ v)) * (tau I P.D P.K lam : ℝ) ≤
      ((P.dN : ℝ) + 1) * (rnum I P.D P.K lam : ℝ) * (v ⬝ᵥ v) := by
  have hM := Mr_psd I hI P.D hD.le lam hbox
  have hX : (vecMulVec v v).PosSemidef := by
    have h := posSemidef_vecMulVec_self_star v
    rwa [star_trivial] at h
  have hd : (2 : ℝ) ≤ P.dN := by exact_mod_cast hdN
  have hdpos : (0 : ℝ) < P.dN := by linarith
  have hδ0 : (0 : ℝ) < 1 / P.dN := by positivity
  have hδ1 : (1 : ℝ) / P.dN < 1 := by rw [div_lt_one hdpos]; linarith
  have h := power_lemma hM hX hδ0 hδ1 P.K hK
  rw [← tau_cast, pow_succ', ← castM_Qz, ← rnum_cast I hI, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm _ v] at h
  have e1 : ((P.dN : ℝ) - 1) = P.dN * (1 - 1 / P.dN) := by field_simp
  have e2 : ((P.dN : ℝ) + 1) = P.dN * (1 + 1 / P.dN) := by field_simp
  rw [e1, e2]
  calc (P.dN : ℝ) * (1 - 1 / P.dN) * (v ⬝ᵥ (castM (Mz I P.D lam) *ᵥ v)) * (tau I P.D P.K lam : ℝ)
      = P.dN * ((1 - 1 / P.dN) * (v ⬝ᵥ (castM (Mz I P.D lam) *ᵥ v)) *
          (tau I P.D P.K lam : ℝ)) := by ring
    _ ≤ P.dN * ((1 + 1 / P.dN) * (rnum I P.D P.K lam : ℝ) * (v ⬝ᵥ v)) :=
        mul_le_mul_of_nonneg_left h hdpos.le
    _ = _ := by ring

theorem shift_arith (g s τ D n d rn : ℝ) (hs : 0 ≤ s) (hτ : 0 < τ) (hD : 0 < D) (hd : 2 ≤ d)
    (h : (d - 1) * (n * D * s - D * g) * τ ≤ (d + 1) * rn * s) :
    0 ≤ g + max 0 (rn * (d + 1) / (τ * (d - 1)) - n * D) / D * s := by
  have hden : 0 < τ * (d - 1) := mul_pos hτ (by linarith)
  set r := rn * (d + 1) / (τ * (d - 1)) with hr
  have h1 : n * D * s - D * g ≤ r * s := by
    rw [hr, div_mul_eq_mul_div, le_div_iff₀ hden]
    linarith
  have h2 : r - n * D ≤ max 0 (r - n * D) := le_max_right _ _
  have h4 : D * (g + max 0 (r - n * D) / D * s) = D * g + max 0 (r - n * D) * s := by
    field_simp
  have h5 : 0 ≤ D * (g + max 0 (r - n * D) / D * s) := by
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_right h2 hs]
  exact (mul_nonneg_iff_of_pos_left hD).mp h5

/-- The real point `ℓ = lam / D`. -/
noncomputable def ellR (D : ℤ) (lam : κ → ℤ) : κ → ℝ := fun c => (lam c : ℝ) / (D : ℝ)

theorem Gam_cast (I : Inst N κ) (D : ℤ) (hD : 0 < D) (lam : κ → ℤ) :
    Gam I (fun c => (lam c : ℝ)) = (D : ℝ) • Gam I (ellR D lam) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  ext i j
  simp only [Gam_apply, Matrix.smul_apply, smul_eq_mul, ellR]
  field_simp

theorem aq_cast (I : Inst N κ) (P : Par) (lam : κ → ℤ) :
    ((aq I P lam : ℚ) : ℝ) = max 0 ((rnum I P.D P.K lam : ℝ) * ((P.dN : ℝ) + 1) /
      ((tau I P.D P.K lam : ℝ) * ((P.dN : ℝ) - 1)) - (N : ℝ) * (P.D : ℝ)) / (P.D : ℝ) := by
  unfold aq
  push_cast
  rfl

theorem aq_nonneg (I : Inst N κ) (P : Par) (hD : 0 < P.D) (lam : κ → ℤ) : 0 ≤ aq I P lam := by
  unfold aq
  exact div_nonneg (le_max_left _ _) (by exact_mod_cast hD.le)

theorem aq_nonneg_real (I : Inst N κ) (P : Par) (hD : 0 < P.D) (lam : κ → ℤ) :
    (0 : ℝ) ≤ ((aq I P lam : ℚ) : ℝ) := by
  exact_mod_cast aq_nonneg I P hD lam

theorem Gam_shift_psd (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D) :
    (Gam I (ellR P.D lam) +
      ((aq I P lam : ℚ) : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Gam_symm I hI _ i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  · rw [star_trivial, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, aq_cast]
    have hrb := rank_one_bound I hI P hD hdN hK lam hbox v
    have hq : v ⬝ᵥ (castM (Mz I P.D lam) *ᵥ v) =
        (N : ℝ) * (P.D : ℝ) * (v ⬝ᵥ v) - (P.D : ℝ) * (v ⬝ᵥ (Gam I (ellR P.D lam) *ᵥ v)) := by
      rw [castM_Mz, Gam_cast I P.D hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul]
    rw [hq] at hrb
    have hs : 0 ≤ v ⬝ᵥ v := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hτ : (0 : ℝ) < (tau I P.D P.K lam : ℝ) := by
      exact_mod_cast tau_pos I hI P.D P.K hN hD lam hbox hk0
    exact shift_arith _ _ _ _ _ _ _ hs hτ (by exact_mod_cast hD) (by exact_mod_cast hdN) hrb

/-- The repaired point `(ℓ + a ℓ0) / (1 + a)`. -/
noncomputable def ellRep (I : Inst N κ) (P : Par) (lam : κ → ℤ) : κ → ℝ := fun c =>
  (ellR P.D lam c + ((aq I P lam : ℚ) : ℝ) * (if c = I.k0 then 1 else 0)) /
    (1 + ((aq I P lam : ℚ) : ℝ))

/-- The base point `ℓ0`, the indicator of `k0`. -/
noncomputable def ell0 (I : Inst N κ) : κ → ℝ := fun c => if c = I.k0 then 1 else 0

theorem Gam_ell0 (I : Inst N κ) (hI : I.Good) : Gam I (ell0 I) = 1 := by
  ext i j
  rw [Gam_apply, Matrix.one_apply]
  unfold ell0
  by_cases hij : i = j
  · subst hij
    rw [if_pos (cls_self I hI i), if_pos rfl, hI.sgn_diag]
    norm_num
  · rw [if_neg (fun h => hij ((hI.cls_diag i j).mp h)), if_neg hij, mul_zero]

theorem ell0_feas (I : Inst N κ) (hI : I.Good) : Feas I (ell0 I) := by
  refine ⟨by simp [ell0], ?_⟩
  rw [Gam_ell0 I hI]
  exact PosSemidef.one

theorem Cs_ind (I : Inst N κ) (hI : I.Good) (i j : Fin N) :
    (I.Cs i j : ℝ) * (if I.cls i j = I.k0 then (1 : ℝ) else 0) = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [hI.Cs_diag]
    simp
  · rw [if_neg (fun h => hij ((hI.cls_diag i j).mp h)), mul_zero]

theorem obj_ell0 (I : Inst N κ) (hI : I.Good) : obj I (ell0 I) = (I.c0 : ℝ) := by
  unfold obj ell0
  simp only [Cs_ind I hI, Finset.sum_const_zero, add_zero]

theorem c0_nonneg_real (I : Inst N κ) (hI : I.Good) : (0 : ℝ) ≤ (I.c0 : ℝ) := by
  exact_mod_cast hI.c0_nonneg

theorem c0_le_real (I : Inst N κ) (hI : I.Good) : (I.c0 : ℝ) ≤ 1 / 2 := by
  have h := hI.c0_le
  have h' : ((I.c0 : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h
  simpa using h'

theorem Cs_sum_real (I : Inst N κ) (hI : I.Good) : ∑ i, ∑ j, |(I.Cs i j : ℝ)| ≤ 3 / 2 := by
  have h := hI.Cs_sum
  have h' : ((∑ i, ∑ j, |I.Cs i j| : ℚ) : ℝ) ≤ ((3 / 2 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

theorem obj_sub_abs (I : Inst N κ) (hI : I.Good) (f : κ → ℝ) (hf : ∀ c, |f c| ≤ 1) :
    |obj I f - I.c0| ≤ 3 / 2 := by
  unfold obj
  rw [add_sub_cancel_left]
  calc |∑ i, ∑ j, (I.Cs i j : ℝ) * f (I.cls i j)|
      ≤ ∑ i, |∑ j, (I.Cs i j : ℝ) * f (I.cls i j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(I.Cs i j : ℝ) * f (I.cls i j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(I.Cs i j : ℝ)| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hf _)
    _ ≤ 3 / 2 := Cs_sum_real I hI

theorem ellR_k0 (D : ℤ) (hD : 0 < D) (lam : κ → ℤ) (k : κ) (hk0 : lam k = D) :
    ellR D lam k = 1 := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold ellR
  rw [hk0, div_self hD']

theorem ellR_abs (D : ℤ) (hD : 0 < D) (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ D) (c : κ) :
    |ellR D lam c| ≤ 1 := by
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h : |(lam c : ℝ)| ≤ (D : ℝ) := by exact_mod_cast hbox c
  unfold ellR
  rw [abs_div, abs_of_pos hD', div_le_one hD']
  exact h

theorem objq_cast (I : Inst N κ) (P : Par) (lam : κ → ℤ) :
    ((objq I P lam : ℚ) : ℝ) = obj I (ellR P.D lam) := by
  unfold objq obj ellR
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]

theorem valq_cast (I : Inst N κ) (P : Par) (lam : κ → ℤ) :
    ((valq I P lam : ℚ) : ℝ) =
      (obj I (ellR P.D lam) + ((aq I P lam : ℚ) : ℝ) * (I.c0 : ℝ)) /
        (1 + ((aq I P lam : ℚ) : ℝ)) := by
  rw [valq, Rat.cast_div, Rat.cast_add, Rat.cast_add, Rat.cast_mul, Rat.cast_one, objq_cast]

theorem rep_spec (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D) :
    Feas I (ellRep I P lam) ∧ obj I (ellRep I P lam) = ((valq I P lam : ℚ) : ℝ) ∧
      ∀ c, |ellRep I P lam c| ≤ 1 := by
  have ha := aq_nonneg_real I P hD lam
  have h1a : (0 : ℝ) < 1 + ((aq I P lam : ℚ) : ℝ) := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold ellRep
    rw [if_pos rfl, ellR_k0 P.D hD lam I.k0 hk0, mul_one, div_self h1a.ne']
  · have hG : Gam I (ellRep I P lam) = (1 / (1 + ((aq I P lam : ℚ) : ℝ))) •
        (Gam I (ellR P.D lam) + ((aq I P lam : ℚ) : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) := by
      ext i j
      simp only [Gam_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul,
        ellRep]
      by_cases hij : i = j
      · subst hij
        rw [if_pos (cls_self I hI i), if_pos rfl, hI.sgn_diag]
        push_cast
        ring
      · rw [if_neg (fun h => hij ((hI.cls_diag i j).mp h)), if_neg hij]
        ring
    rw [hG]
    exact (Gam_shift_psd I hI P hN hD hdN hK lam hbox hk0).smul (by positivity)
  · rw [valq_cast]
    have hterm : ∀ i j, (I.Cs i j : ℝ) * ellRep I P lam (I.cls i j) =
        (I.Cs i j : ℝ) * ellR P.D lam (I.cls i j) / (1 + ((aq I P lam : ℚ) : ℝ)) := by
      intro i j
      have h := Cs_ind I hI i j
      unfold ellRep
      rw [mul_div_assoc', mul_add, ← mul_assoc, mul_comm (I.Cs i j : ℝ) ((aq I P lam : ℚ) : ℝ),
        mul_assoc, h, mul_zero, add_zero]
    unfold obj
    simp only [hterm, ← Finset.sum_div]
    rw [eq_div_iff h1a.ne', add_mul, div_mul_cancel₀ _ h1a.ne']
    ring
  · intro c
    unfold ellRep
    rw [abs_div, abs_of_pos h1a, div_le_one h1a]
    have h1 := ellR_abs P.D hD lam hbox c
    rw [abs_le] at h1 ⊢
    split_ifs <;> constructor <;> linarith [h1.1, h1.2]

theorem valq_le_two (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D) :
    valq I P lam ≤ 2 := by
  obtain ⟨-, ho, hb⟩ := rep_spec I hI P hN hD hdN hK lam hbox hk0
  have h1 := obj_sub_abs I hI _ hb
  have h2 := c0_le_real I hI
  rw [abs_le] at h1
  have h3 : ((valq I P lam : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := by
    rw [← ho]
    push_cast
    linarith [h1.2]
  exact_mod_cast h3

theorem bestSeq_le (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (T : ℕ) : bestSeq I P T ≤ 2 * (P.D2 : ℤ) := by
  induction T with
  | zero => rw [bestSeq_zero]; positivity
  | succ T ih =>
    rw [bestSeq_succ]
    unfold bestStep
    refine max_le ih ?_
    have hv := valq_le_two I hI P hN hD hdN hK (lamSeq I P T)
      (lamSeq_box I P hD.le T) (lamSeq_k0 I P T)
    have hm : max 0 (valq I P (lamSeq I P T)) ≤ 2 := max_le (by norm_num) hv
    have h1 : (P.D2 : ℚ) * max 0 (valq I P (lamSeq I P T)) ≤ ((2 * (P.D2 : ℤ) : ℤ) : ℚ) := by
      push_cast
      nlinarith [(Nat.cast_nonneg P.D2 : (0 : ℚ) ≤ P.D2)]
    have h2 := (Int.floor_le _).trans h1
    exact_mod_cast h2

theorem sound_aux (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ)) (T : ℕ) :
    ∃ ℓ : κ → ℝ, Feas I ℓ ∧ (bestSeq I P T : ℝ) ≤ (P.D2 : ℝ) * obj I ℓ := by
  have h0 : (0 : ℝ) ≤ (P.D2 : ℝ) * obj I (ell0 I) := by
    rw [obj_ell0 I hI]
    exact mul_nonneg (Nat.cast_nonneg _) (c0_nonneg_real I hI)
  induction T with
  | zero =>
    refine ⟨ell0 I, ell0_feas I hI, ?_⟩
    rw [bestSeq_zero]
    exact_mod_cast h0
  | succ T ih =>
    obtain ⟨ℓ, hℓ, hb⟩ := ih
    rw [bestSeq_succ]
    unfold bestStep
    rcases le_total ⌊(P.D2 : ℚ) * max 0 (valq I P (lamSeq I P T))⌋ (bestSeq I P T) with h | h
    · rw [max_eq_left h]
      exact ⟨ℓ, hℓ, hb⟩
    · rw [max_eq_right h]
      rcases le_total (valq I P (lamSeq I P T)) 0 with hv | hv
      · rw [max_eq_left hv, mul_zero, Int.floor_zero]
        exact ⟨ell0 I, ell0_feas I hI, by exact_mod_cast h0⟩
      · rw [max_eq_right hv]
        obtain ⟨hf, ho, -⟩ := rep_spec I hI P hN hD hdN hK (lamSeq I P T)
          (lamSeq_box I P hD.le T) (lamSeq_k0 I P T)
        refine ⟨ellRep I P (lamSeq I P T), hf, ?_⟩
        rw [ho]
        have h1 := Int.floor_le ((P.D2 : ℚ) * valq I P (lamSeq I P T))
        have h2 : ((⌊(P.D2 : ℚ) * valq I P (lamSeq I P T)⌋ : ℤ) : ℝ) ≤
            (((P.D2 : ℚ) * valq I P (lamSeq I P T) : ℚ) : ℝ) := by exact_mod_cast h1
        push_cast at h2
        exact h2

/-- Soundness: the recorded best value is attained from below by a feasible point. -/
theorem tied_sound (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (hD2 : 0 < P.D2) (T : ℕ) :
    ∃ ℓ : κ → ℝ, Feas I ℓ ∧ (bestSeq I P T : ℝ) / (P.D2 : ℝ) ≤ obj I ℓ := by
  obtain ⟨ℓ, hℓ, hb⟩ := sound_aux I hI P hN hD hdN hK T
  refine ⟨ℓ, hℓ, ?_⟩
  have hD2' : (0 : ℝ) < (P.D2 : ℝ) := by exact_mod_cast hD2
  rw [div_le_iff₀ hD2']
  linarith

/-! ### Accuracy: class coordinates -/

/-- The classes that occur. -/
def occ (I : Inst N κ) : Finset κ :=
  (Finset.univ : Finset (Fin N × Fin N)).image fun p => I.cls p.1 p.2

theorem mem_occ (I : Inst N κ) (i j : Fin N) : I.cls i j ∈ occ I :=
  Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

theorem card_occ (I : Inst N κ) : ((occ I).card : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h : (occ I).card ≤ N * N := by
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin N × Fin N)))
      (f := fun p => I.cls p.1 p.2)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
    exact h1
  have h' : ((occ I).card : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h
  rw [sq]
  push_cast at h'
  exact h'

/-- Regrouping a double sum by classes. -/
theorem regroup (I : Inst N κ) (a : Fin N → Fin N → ℝ) (f : κ → ℝ) :
    ∑ k ∈ occ I, (∑ i, ∑ j, if I.cls i j = k then a i j else 0) * f k =
      ∑ i, ∑ j, a i j * f (I.cls i j) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (mem_occ I i j)]

theorem gC_cast (I : Inst N κ) (k : κ) :
    ((gC I k : ℚ) : ℝ) = ∑ i, ∑ j, if I.cls i j = k then (I.Cs i j : ℝ) else 0 := by
  rw [gC, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : I.cls i j = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Rat.cast_zero]

theorem gQ_cast (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) (k : κ) :
    ((gQ I D K lam k : ℤ) : ℝ) =
      ∑ i, ∑ j, if I.cls i j = k then (I.sgn i j : ℝ) * castM (Qz I D K lam) i j else 0 := by
  rw [gQ, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : I.cls i j = k
  · rw [if_pos h, if_pos h, castM_apply, Int.cast_mul]
  · rw [if_neg h, if_neg h, Int.cast_zero]

theorem sum_gC (I : Inst N κ) (f : κ → ℝ) :
    ∑ k ∈ occ I, ((gC I k : ℚ) : ℝ) * f k = obj I f - I.c0 := by
  simp only [gC_cast]
  rw [regroup I (fun i j => (I.Cs i j : ℝ)) f]
  unfold obj
  ring

theorem sum_gQ (I : Inst N κ) (hI : I.Good) (D : ℤ) (K : ℕ) (lam : κ → ℤ) (f : κ → ℝ) :
    ∑ k ∈ occ I, ((gQ I D K lam k : ℤ) : ℝ) * f k = (castM (Qz I D K lam) * Gam I f).trace := by
  simp only [gQ_cast]
  rw [regroup I (fun i j => (I.sgn i j : ℝ) * castM (Qz I D K lam) i j) f]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Gam_symm I hI f i j, Gam_apply]
  ring

theorem sum_gQ_lam (I : Inst N κ) (hI : I.Good) (D : ℤ) (K : ℕ) (lam : κ → ℤ) :
    ∑ k ∈ occ I, ((gQ I D K lam k : ℤ) : ℝ) * (lam k : ℝ) =
      (N : ℝ) * (D : ℝ) * (tau I D K lam : ℝ) - (rnum I D K lam : ℝ) := by
  rw [sum_gQ I hI D K lam (fun c => (lam c : ℝ))]
  have h : Gam I (fun c => (lam c : ℝ)) =
      ((N : ℝ) * (D : ℝ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM (Mz I D lam) := by
    rw [castM_Mz, sub_sub_cancel]
  rw [h, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    smul_eq_mul, Matrix.trace_mul_comm, ← rnum_cast I hI, castM_Qz, ← tau_cast]

theorem psd_abs_le_trace {X : Matrix (Fin N) (Fin N) ℝ} (hX : X.PosSemidef) (i j : Fin N) :
    |X i j| ≤ X.trace := by
  have hsym : X j i = X i j := by
    have h := hX.1.apply i j
    simpa using h
  have key : ∀ t : ℝ, 0 ≤ X i i + t * X i j + t * X j i + t * t * X j j := by
    intro t
    have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 + t • Pi.single j 1)
    simp only [star_trivial, mulVec_add, mulVec_smul, mulVec_single_one, add_dotProduct,
      smul_dotProduct, dotProduct_add, dotProduct_smul, single_dotProduct, one_mul,
      smul_eq_mul, col_apply] at h
    linarith
  have hp := key 1
  have hm := key (-1)
  rw [hsym] at hp hm
  have hi : X i i ≤ X.trace :=
    Finset.single_le_sum (f := fun k => X k k) (fun k _ => hX.diag_nonneg) (Finset.mem_univ i)
  have hj : X j j ≤ X.trace :=
    Finset.single_le_sum (f := fun k => X k k) (fun k _ => hX.diag_nonneg) (Finset.mem_univ j)
  rw [abs_le]
  constructor <;> linarith

theorem gC_abs (I : Inst N κ) (hI : I.Good) (k : κ) : |((gC I k : ℚ) : ℝ)| ≤ 3 / 2 := by
  rw [gC_cast]
  calc |∑ i, ∑ j, if I.cls i j = k then (I.Cs i j : ℝ) else 0|
      ≤ ∑ i, |∑ j, if I.cls i j = k then (I.Cs i j : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |if I.cls i j = k then (I.Cs i j : ℝ) else 0| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(I.Cs i j : ℝ)| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          split_ifs
          · exact le_rfl
          · rw [abs_zero]; exact abs_nonneg _
    _ ≤ 3 / 2 := Cs_sum_real I hI

theorem gQ_abs (I : Inst N κ) (hI : I.Good) (D : ℤ) (hD : 0 ≤ D) (K : ℕ) (lam : κ → ℤ)
    (hbox : ∀ c, |lam c| ≤ D) (k : κ) :
    |((gQ I D K lam k : ℤ) : ℝ)| ≤ (N : ℝ) ^ 2 * (tau I D K lam : ℝ) := by
  have hQ := Qr_psd I hI D hD K lam hbox
  have hτ : (castM (Qz I D K lam)).trace = (tau I D K lam : ℝ) := by rw [castM_Qz, tau_cast]
  rw [gQ_cast]
  calc |∑ i, ∑ j, if I.cls i j = k then (I.sgn i j : ℝ) * castM (Qz I D K lam) i j else 0|
      ≤ ∑ i, |∑ j, if I.cls i j = k then (I.sgn i j : ℝ) * castM (Qz I D K lam) i j else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |if I.cls i j = k then (I.sgn i j : ℝ) * castM (Qz I D K lam) i j else 0| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, (tau I D K lam : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h := psd_abs_le_trace hQ i j
          rw [hτ] at h
          have hτ0 : (0 : ℝ) ≤ (tau I D K lam : ℝ) := le_trans (abs_nonneg _) h
          split_ifs
          · rw [abs_mul]
            calc |(I.sgn i j : ℝ)| * |castM (Qz I D K lam) i j| ≤ 1 * (tau I D K lam : ℝ) :=
                  mul_le_mul (sgn_abs_real I hI i j) h (abs_nonneg _) zero_le_one
              _ = (tau I D K lam : ℝ) := one_mul _
          · rw [abs_zero]; exact hτ0
    _ = (N : ℝ) ^ 2 * (tau I D K lam : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Accuracy: the supergradient inequality -/

/-- The supergradient in class coordinates. -/
noncomputable def Gr (I : Inst N κ) (P : Par) (lam : κ → ℤ) (k : κ) : ℝ :=
  ((gC I k : ℚ) : ℝ) + if active I P.D P.K lam then
    2 * ((gQ I P.D P.K lam k : ℤ) : ℝ) / (tau I P.D P.K lam : ℝ) else 0

theorem stepv_cast (I : Inst N κ) (P : Par) (lam : κ → ℤ) (k : κ) :
    ((stepv I P lam k : ℚ) : ℝ) = (P.eta : ℝ) * Gr I P lam k := by
  unfold stepv Gr
  split_ifs <;> push_cast <;> ring

theorem active_iff (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) :
    active I D K lam = true ↔
      (N : ℝ) * (D : ℝ) * (tau I D K lam : ℝ) < (rnum I D K lam : ℝ) := by
  unfold active
  rw [decide_eq_true_iff]
  constructor <;> intro h <;> exact_mod_cast h

theorem Gr_abs (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D) (k : κ) :
    |Gr I P lam k| ≤ 4 * (N : ℝ) ^ 2 := by
  have hτ : (0 : ℝ) < (tau I P.D P.K lam : ℝ) := by
    exact_mod_cast tau_pos I hI P.D P.K hN hD lam hbox hk0
  have h1 := abs_le.mp (gC_abs I hI k)
  have h2 := abs_le.mp (gQ_abs I hI P.D hD.le P.K lam hbox k)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h3 : |2 * ((gQ I P.D P.K lam k : ℤ) : ℝ) / (tau I P.D P.K lam : ℝ)| ≤
      2 * (N : ℝ) ^ 2 := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hτ]; linarith [h2.1]
    · rw [div_le_iff₀ hτ]; linarith [h2.2]
  have h3' := abs_le.mp h3
  unfold Gr
  rw [abs_le]
  split_ifs <;> constructor <;> linarith [h1.1, h1.2, h3'.1, h3'.2]

/-- The penalized objective at the current point. -/
noncomputable def ft (I : Inst N κ) (P : Par) (lam : κ → ℤ) : ℝ :=
  obj I (ellR P.D lam) +
    if (N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) < (rnum I P.D P.K lam : ℝ) then
      2 * ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) - (rnum I P.D P.K lam : ℝ)) /
        ((tau I P.D P.K lam : ℝ) * (P.D : ℝ)) else 0

theorem sum_G_ge (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D)
    (ℓs : κ → ℝ) (hfeas : Feas I ℓs) :
    (P.D : ℝ) * (obj I ℓs - ft I P lam) ≤
      ∑ k ∈ occ I, Gr I P lam k * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) := by
  have hτ : (0 : ℝ) < (tau I P.D P.K lam : ℝ) := by
    exact_mod_cast tau_pos I hI P.D P.K hN hD lam hbox hk0
  have hDr : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast hD
  have hC : ∑ k ∈ occ I, ((gC I k : ℚ) : ℝ) * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) =
      (P.D : ℝ) * (obj I ℓs - obj I (ellR P.D lam)) := by
    have hterm : ∀ k, ((gC I k : ℚ) : ℝ) * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) =
        (P.D : ℝ) * (((gC I k : ℚ) : ℝ) * ℓs k) -
          (P.D : ℝ) * (((gC I k : ℚ) : ℝ) * ellR P.D lam k) := by
      intro k
      unfold ellR
      field_simp
    simp only [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_gC, sum_gC]
    ring
  by_cases hact : active I P.D P.K lam = true
  · have hlt := (active_iff I P.D P.K lam).mp hact
    have hQ : -(2 * ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) - (rnum I P.D P.K lam : ℝ)) /
        (tau I P.D P.K lam : ℝ)) ≤
        ∑ k ∈ occ I, (2 * ((gQ I P.D P.K lam k : ℤ) : ℝ) / (tau I P.D P.K lam : ℝ)) *
          ((P.D : ℝ) * ℓs k - (lam k : ℝ)) := by
      have hterm : ∀ k, (2 * ((gQ I P.D P.K lam k : ℤ) : ℝ) / (tau I P.D P.K lam : ℝ)) *
          ((P.D : ℝ) * ℓs k - (lam k : ℝ)) =
          (2 * (P.D : ℝ) / (tau I P.D P.K lam : ℝ)) * (((gQ I P.D P.K lam k : ℤ) : ℝ) * ℓs k) -
            (2 / (tau I P.D P.K lam : ℝ)) * (((gQ I P.D P.K lam k : ℤ) : ℝ) * (lam k : ℝ)) := by
        intro k
        ring
      simp only [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_gQ I hI,
        sum_gQ_lam I hI]
      have hnn := psd_trace_mul_nonneg (Qr_psd I hI P.D hD.le P.K lam hbox) hfeas.2
      have h1 : 0 ≤ 2 * (P.D : ℝ) / (tau I P.D P.K lam : ℝ) *
          (castM (Qz I P.D P.K lam) * Gam I ℓs).trace := by positivity
      have e : 2 / (tau I P.D P.K lam : ℝ) *
          ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) - (rnum I P.D P.K lam : ℝ)) =
          2 * ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) - (rnum I P.D P.K lam : ℝ)) /
            (tau I P.D P.K lam : ℝ) := by ring
      linarith
    have hG : ∀ k, Gr I P lam k * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) =
        ((gC I k : ℚ) : ℝ) * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) +
          (2 * ((gQ I P.D P.K lam k : ℤ) : ℝ) / (tau I P.D P.K lam : ℝ)) *
            ((P.D : ℝ) * ℓs k - (lam k : ℝ)) := by
      intro k
      unfold Gr
      rw [if_pos hact]
      ring
    simp only [hG]
    rw [Finset.sum_add_distrib, hC]
    unfold ft
    rw [if_pos hlt]
    have e : (P.D : ℝ) * (2 * ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) -
        (rnum I P.D P.K lam : ℝ)) / ((tau I P.D P.K lam : ℝ) * (P.D : ℝ))) =
        2 * ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) - (rnum I P.D P.K lam : ℝ)) /
          (tau I P.D P.K lam : ℝ) := by
      field_simp
    rw [mul_sub, mul_add, e]
    linarith
  · have hnlt : ¬ ((N : ℝ) * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) < (rnum I P.D P.K lam : ℝ)) :=
      fun h => hact ((active_iff I P.D P.K lam).mpr h)
    have hG : ∀ k, Gr I P lam k * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) =
        ((gC I k : ℚ) : ℝ) * ((P.D : ℝ) * ℓs k - (lam k : ℝ)) := by
      intro k
      unfold Gr
      rw [if_neg hact, add_zero]
    simp only [hG]
    rw [hC]
    unfold ft
    rw [if_neg hnlt, add_zero]

/-! ### Accuracy: the certified value against the penalized objective -/

theorem val_arith (o c0 τ D n d rn a : ℝ) (hτ : 0 < τ) (hD : 0 < D) (hd : 2 ≤ d)
    (hrn : rn ≤ n ^ 2 * D * τ) (hrn0 : 0 ≤ rn) (ho : |o - c0| ≤ 3 / 2)
    (ha : a = max 0 (rn * (d + 1) / (τ * (d - 1)) - n * D) / D) :
    o + (if n * D * τ < rn then 2 * (n * D * τ - rn) / (τ * D) else 0) ≤
      (o + a * c0) / (1 + a) + 6 * n ^ 2 / d := by
  obtain ⟨e, he⟩ : ∃ e, e = rn / τ := ⟨_, rfl⟩
  have hrn' : rn = e * τ := by rw [he]; field_simp
  subst hrn'
  have he0 : 0 ≤ e := nonneg_of_mul_nonneg_left hrn0 hτ
  have hen : e ≤ n ^ 2 * D := le_of_mul_le_mul_right hrn hτ
  have hd1 : 0 < d - 1 := by linarith
  have hd0 : 0 < d := by linarith
  have hu : e * τ * (d + 1) / (τ * (d - 1)) - n * D ≤ (e - n * D) + 4 * n ^ 2 * D / d := by
    have h1 : e * τ * (d + 1) / (τ * (d - 1)) = e + 2 * e / (d - 1) := by
      field_simp
      ring
    have h2 : 2 * e / (d - 1) ≤ 4 * e / d := by
      rw [div_le_div_iff₀ hd1 hd0]
      nlinarith
    have h3 : 4 * e / d ≤ 4 * n ^ 2 * D / d :=
      div_le_div_of_nonneg_right (by linarith) hd0.le
    rw [h1]
    linarith
  obtain ⟨m, hm⟩ : ∃ m, m = max 0 (e - n * D) / D := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg (le_max_left _ _) hD.le
  have ham : a ≤ m + 4 * n ^ 2 / d := by
    rw [ha, hm]
    have h4 : max 0 (e * τ * (d + 1) / (τ * (d - 1)) - n * D) ≤
        max 0 (e - n * D) + 4 * n ^ 2 * D / d := by
      apply max_le
      · have h5 : 0 ≤ 4 * n ^ 2 * D / d := by positivity
        linarith [le_max_left 0 (e - n * D)]
      · linarith [le_max_right 0 (e - n * D)]
    rw [div_le_iff₀ hD]
    have e5 : (max 0 (e - n * D) / D + 4 * n ^ 2 / d) * D =
        max 0 (e - n * D) + 4 * n ^ 2 * D / d := by
      field_simp
    rw [e5]
    exact h4
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (le_max_left _ _) hD.le
  have h1a : 0 < 1 + a := by linarith
  have hv : o - 3 / 2 * a ≤ (o + a * c0) / (1 + a) := by
    rw [le_div_iff₀ h1a]
    have h6 := (abs_le.mp ho).2
    nlinarith [mul_nonneg ha0 ha0, mul_le_mul_of_nonneg_left h6 ha0]
  have hite : (if n * D * τ < e * τ then 2 * (n * D * τ - e * τ) / (τ * D) else 0) ≤
      -(3 / 2) * m := by
    split_ifs with hc
    · have hpos : n * D < e := lt_of_mul_lt_mul_right hc hτ.le
      have hmm : m = (e - n * D) / D := by rw [hm, max_eq_right (by linarith)]
      have e6 : 2 * (n * D * τ - e * τ) / (τ * D) = -2 * ((e - n * D) / D) := by
        field_simp
        ring
      rw [e6, ← hmm]
      linarith
    · have hle : e ≤ n * D := le_of_mul_le_mul_right (not_lt.mp hc) hτ
      have hmm : m = 0 := by rw [hm, max_eq_left (by linarith), zero_div]
      rw [hmm]
      norm_num
  have h6 : 6 * n ^ 2 / d = 3 / 2 * (4 * n ^ 2 / d) := by ring
  linarith

theorem ft_le (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (hdN : 2 ≤ P.dN)
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D) :
    ft I P lam ≤ ((valq I P lam : ℚ) : ℝ) + 6 * (N : ℝ) ^ 2 / (P.dN : ℝ) := by
  have hτ : (0 : ℝ) < (tau I P.D P.K lam : ℝ) := by
    exact_mod_cast tau_pos I hI P.D P.K hN hD lam hbox hk0
  have hDr : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast hD
  have hM := Mr_psd I hI P.D hD.le lam hbox
  have hQ := Qr_psd I hI P.D hD.le P.K lam hbox
  have hrn0 : (0 : ℝ) ≤ (rnum I P.D P.K lam : ℝ) := by
    rw [rnum_cast I hI]
    exact psd_trace_mul_nonneg hM hQ
  have hrn : (rnum I P.D P.K lam : ℝ) ≤ (N : ℝ) ^ 2 * (P.D : ℝ) * (tau I P.D P.K lam : ℝ) := by
    have h := psd_trace_mul_le hM hQ
    rw [← rnum_cast I hI, castM_Qz, ← tau_cast, trace_castR, trace_Mz I hI P.D lam hk0] at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (mul_pos hDr hτ).le]
  rw [valq_cast]
  exact val_arith _ _ _ _ _ _ _ _ hτ hDr (by exact_mod_cast hdN) hrn hrn0
    (obj_sub_abs I hI _ (ellR_abs P.D hD lam hbox)) (aq_cast I P lam)

/-! ### Accuracy: one step of the potential -/

theorem rnd_sub_abs (q : ℚ) : |((rnd q : ℤ) : ℚ) - q| ≤ 1 := by
  unfold rnd
  split_ifs with h
  · have h1 := Int.floor_le (-q)
    have h2 := Int.lt_floor_add_one (-q)
    rw [abs_le]
    push_cast
    constructor <;> linarith
  · have h1 := Int.floor_le q
    have h2 := Int.lt_floor_add_one q
    rw [abs_le]
    constructor <;> linarith

theorem rnd_sub_abs_real (q : ℚ) : |((rnd q : ℤ) : ℝ) - ((q : ℚ) : ℝ)| ≤ 1 := by
  have h := rnd_sub_abs q
  have h' : ((|((rnd q : ℤ) : ℚ) - q| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

theorem clamp_sq_le (D z : ℤ) (y : ℝ) (hy : |y| ≤ (D : ℝ)) :
    (((clampZ D z : ℤ) : ℝ) - y) ^ 2 ≤ ((z : ℝ) - y) ^ 2 := by
  have hy' := abs_le.mp hy
  have hD : (0 : ℝ) ≤ D := le_trans (abs_nonneg _) hy
  have hDz : (0 : ℤ) ≤ D := by exact_mod_cast hD
  rcases le_or_gt z (-D) with h1 | h1
  · have hc : clampZ D z = -D := by
      unfold clampZ
      rw [min_eq_right (by omega), max_eq_left h1]
    rw [hc]
    have h3 : (z : ℝ) ≤ -(D : ℝ) := by exact_mod_cast h1
    push_cast
    have a1 : 0 ≤ -(D : ℝ) - z := by linarith
    have a2 : 0 ≤ (y - z) + (y + D) := by linarith [hy'.1]
    nlinarith [mul_nonneg a1 a2]
  · rcases le_or_gt z D with h2 | h2
    · have hc : clampZ D z = z := by
        unfold clampZ
        rw [min_eq_right h2, max_eq_right h1.le]
      rw [hc]
    · have hc : clampZ D z = D := by
        unfold clampZ
        rw [min_eq_left h2.le, max_eq_right (by omega)]
      rw [hc]
      have h3 : (D : ℝ) < z := by exact_mod_cast h2
      have a1 : 0 ≤ (z : ℝ) - D := by linarith
      have a2 : 0 ≤ ((z : ℝ) - y) + (D - y) := by linarith [hy'.2]
      nlinarith [mul_nonneg a1 a2]

theorem coord_step (x y st r G η Dr n : ℝ) (hη : 0 ≤ η) (hx : |x| ≤ Dr) (hy : |y| ≤ Dr)
    (hst : st = η * G) (hG : |G| ≤ 4 * n ^ 2) (hr : |r - st| ≤ 1) :
    (x + r - y) ^ 2 ≤
      (x - y) ^ 2 - 2 * η * (G * (y - x)) + (4 * Dr + (η * (4 * n ^ 2) + 1) ^ 2) := by
  subst hst
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hr' := abs_le.mp hr
  have hηG : |η * G| ≤ η * (4 * n ^ 2) := by
    rw [abs_mul, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hG hη
  have hηG' := abs_le.mp hηG
  have h1 : 2 * ((x - y) * (r - η * G)) ≤ 4 * Dr := by
    have h0 : |(x - y) * (r - η * G)| ≤ 2 * Dr * 1 := by
      rw [abs_mul]
      refine mul_le_mul ?_ hr (abs_nonneg _) (by linarith)
      rw [abs_le]
      constructor <;> linarith
    have h0' := (abs_le.mp h0).2
    linarith
  have h2 : r ^ 2 ≤ (η * (4 * n ^ 2) + 1) ^ 2 := by
    apply sq_le_sq' <;> linarith
  nlinarith [h1, h2]

/-- The constant error of one step. -/
noncomputable def stepC (N : ℕ) (P : Par) : ℝ :=
  4 * (P.D : ℝ) + ((P.eta : ℝ) * (4 * (N : ℝ) ^ 2) + 1) ^ 2

/-- The potential: squared distance to the comparator, in grid units. -/
noncomputable def Phi (I : Inst N κ) (P : Par) (ℓs : κ → ℝ) (lam : κ → ℤ) : ℝ :=
  ∑ c ∈ (occ I).erase I.k0, ((lam c : ℝ) - (P.D : ℝ) * ℓs c) ^ 2

theorem card_erase_occ (I : Inst N κ) : (((occ I).erase I.k0).card : ℝ) ≤ (N : ℝ) ^ 2 := by
  refine le_trans ?_ (card_occ I)
  exact_mod_cast Finset.card_erase_le

theorem Phi_step (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (heta : 0 < P.eta)
    (lam : κ → ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D)
    (ℓs : κ → ℝ) (hfeas : Feas I ℓs) (hℓs : ∀ c, |ℓs c| ≤ 1) :
    Phi I P ℓs (next I P lam) ≤
      Phi I P ℓs lam - 2 * (P.eta : ℝ) * ((P.D : ℝ) * (obj I ℓs - ft I P lam)) +
        (N : ℝ) ^ 2 * stepC N P := by
  have hηr : (0 : ℝ) ≤ (P.eta : ℝ) := by exact_mod_cast heta.le
  have hDr : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast hD
  have hC0 : 0 ≤ stepC N P := by unfold stepC; positivity
  have hcoord : ∀ c ∈ (occ I).erase I.k0,
      ((next I P lam c : ℝ) - (P.D : ℝ) * ℓs c) ^ 2 ≤
        ((lam c : ℝ) - (P.D : ℝ) * ℓs c) ^ 2 -
          2 * (P.eta : ℝ) * (Gr I P lam c * ((P.D : ℝ) * ℓs c - (lam c : ℝ))) + stepC N P := by
    intro c hc
    have hne : c ≠ I.k0 := (Finset.mem_erase.mp hc).1
    have hy : |(P.D : ℝ) * ℓs c| ≤ (P.D : ℝ) := by
      rw [abs_mul, abs_of_pos hDr]
      exact mul_le_of_le_one_right hDr.le (hℓs c)
    have hx : |(lam c : ℝ)| ≤ (P.D : ℝ) := by exact_mod_cast hbox c
    have hnext : next I P lam c = clampZ P.D (lam c + rnd (stepv I P lam c)) := by
      simp [next, hne]
    rw [hnext]
    refine le_trans (clamp_sq_le _ _ _ hy) ?_
    have h := coord_step (lam c : ℝ) ((P.D : ℝ) * ℓs c) ((stepv I P lam c : ℚ) : ℝ)
      ((rnd (stepv I P lam c) : ℤ) : ℝ) (Gr I P lam c) (P.eta : ℝ) (P.D : ℝ) (N : ℝ) hηr hx hy
      (stepv_cast I P lam c) (Gr_abs I hI P hN hD lam hbox hk0 c) (rnd_sub_abs_real _)
    rw [Int.cast_add]
    exact h
  have hk : ∑ c ∈ (occ I).erase I.k0, Gr I P lam c * ((P.D : ℝ) * ℓs c - (lam c : ℝ)) =
      ∑ c ∈ occ I, Gr I P lam c * ((P.D : ℝ) * ℓs c - (lam c : ℝ)) := by
    apply Finset.sum_erase
    rw [hfeas.1, hk0]
    ring
  have hsum := sum_G_ge I hI P hN hD lam hbox hk0 ℓs hfeas
  have hcard := card_erase_occ I
  calc Phi I P ℓs (next I P lam)
      ≤ ∑ c ∈ (occ I).erase I.k0, (((lam c : ℝ) - (P.D : ℝ) * ℓs c) ^ 2 -
          2 * (P.eta : ℝ) * (Gr I P lam c * ((P.D : ℝ) * ℓs c - (lam c : ℝ))) + stepC N P) :=
        Finset.sum_le_sum hcoord
    _ = Phi I P ℓs lam - 2 * (P.eta : ℝ) *
          ∑ c ∈ occ I, Gr I P lam c * ((P.D : ℝ) * ℓs c - (lam c : ℝ)) +
          (((occ I).erase I.k0).card : ℝ) * stepC N P := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hk,
          Finset.sum_const, nsmul_eq_mul]
        rfl
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hsum (mul_nonneg zero_le_two hηr)
        have h2 := mul_le_mul_of_nonneg_right hcard hC0
        linarith

/-! ### Accuracy: telescoping -/

theorem bestSeq_mono (I : Inst N κ) (P : Par) {k T : ℕ} (h : k ≤ T) :
    bestSeq I P k ≤ bestSeq I P T := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (by rw [bestSeq_succ]; exact le_max_left _ _)

theorem valq_le_best (I : Inst N κ) (P : Par) (hD2 : 0 < P.D2) (k T : ℕ) (h : k < T) :
    ((valq I P (lamSeq I P k) : ℚ) : ℝ) ≤
      (bestSeq I P T : ℝ) / (P.D2 : ℝ) + 1 / (P.D2 : ℝ) := by
  have h1 : ⌊(P.D2 : ℚ) * max 0 (valq I P (lamSeq I P k))⌋ ≤ bestSeq I P T :=
    le_trans (by rw [bestSeq_succ]; exact le_max_right _ _)
      (bestSeq_mono I P (Nat.succ_le_of_lt h))
  have h2 := Int.lt_floor_add_one ((P.D2 : ℚ) * max 0 (valq I P (lamSeq I P k)))
  have h3 : (P.D2 : ℚ) * valq I P (lamSeq I P k) ≤
      (P.D2 : ℚ) * max 0 (valq I P (lamSeq I P k)) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
  have h4 : (P.D2 : ℚ) * valq I P (lamSeq I P k) ≤ (bestSeq I P T : ℚ) + 1 := by
    have h5 : ((⌊(P.D2 : ℚ) * max 0 (valq I P (lamSeq I P k))⌋ : ℤ) : ℚ) ≤
        (bestSeq I P T : ℚ) := by exact_mod_cast h1
    linarith
  have h5 : (P.D2 : ℝ) * ((valq I P (lamSeq I P k) : ℚ) : ℝ) ≤ (bestSeq I P T : ℝ) + 1 := by
    exact_mod_cast h4
  have hD2' : (0 : ℝ) < (P.D2 : ℝ) := by exact_mod_cast hD2
  rw [← add_div, le_div_iff₀ hD2']
  linarith

theorem accurate_box (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (heta : 0 < P.eta) (hdN : 2 ≤ P.dN)
    (hD2 : 0 < P.D2) (T : ℕ) (hT : 0 < T) (ℓs : κ → ℝ) (hfeas : Feas I ℓs)
    (hℓs : ∀ c, |ℓs c| ≤ 1) :
    obj I ℓs ≤ (bestSeq I P T : ℝ) / (P.D2 : ℝ) + 1 / (P.D2 : ℝ) +
      6 * (N : ℝ) ^ 2 / (P.dN : ℝ) + convErr N P T := by
  have hηr : (0 : ℝ) < (P.eta : ℝ) := by exact_mod_cast heta
  have hDr : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast hD
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  obtain ⟨A, hA⟩ : ∃ A, A = obj I ℓs - ((bestSeq I P T : ℝ) / (P.D2 : ℝ) + 1 / (P.D2 : ℝ)) -
      6 * (N : ℝ) ^ 2 / (P.dN : ℝ) := ⟨_, rfl⟩
  have hstep : ∀ k < T, Phi I P ℓs (lamSeq I P (k + 1)) ≤
      Phi I P ℓs (lamSeq I P k) - 2 * (P.eta : ℝ) * ((P.D : ℝ) * A) +
        (N : ℝ) ^ 2 * stepC N P := by
    intro k hk
    rw [lamSeq_succ]
    have h1 := Phi_step I hI P hN hD heta (lamSeq I P k) (lamSeq_box I P hD.le k)
      (lamSeq_k0 I P k) ℓs hfeas hℓs
    have h2 := ft_le I hI P hN hD hdN (lamSeq I P k) (lamSeq_box I P hD.le k) (lamSeq_k0 I P k)
    have h3 := valq_le_best I P hD2 k T hk
    have h4 : (P.D : ℝ) * A ≤ (P.D : ℝ) * (obj I ℓs - ft I P (lamSeq I P k)) :=
      mul_le_mul_of_nonneg_left (by rw [hA]; linarith) hDr.le
    have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg zero_le_two hηr.le)
    linarith
  have htel : ∀ n ≤ T, (n : ℝ) * (2 * (P.eta : ℝ) * ((P.D : ℝ) * A)) ≤
      Phi I P ℓs (lamSeq I P 0) - Phi I P ℓs (lamSeq I P n) +
        (n : ℝ) * ((N : ℝ) ^ 2 * stepC N P) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := hstep n hn
      push_cast
      linarith
  have hT' := htel T le_rfl
  have hPhiT : 0 ≤ Phi I P ℓs (lamSeq I P T) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hPhi0 : Phi I P ℓs (lamSeq I P 0) ≤ (N : ℝ) ^ 2 * (P.D : ℝ) ^ 2 := by
    unfold Phi
    calc ∑ c ∈ (occ I).erase I.k0, ((lamSeq I P 0 c : ℝ) - (P.D : ℝ) * ℓs c) ^ 2
        ≤ ∑ _c ∈ (occ I).erase I.k0, (P.D : ℝ) ^ 2 :=
          Finset.sum_le_sum fun c hc => by
            have hne : c ≠ I.k0 := (Finset.mem_erase.mp hc).1
            have h0 : lamSeq I P 0 c = 0 := by simp [lamSeq_zero, lam0, hne]
            rw [h0]
            have hb := abs_le.mp (hℓs c)
            push_cast
            have h1 : (ℓs c) ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
            have h2 : ((0 : ℝ) - (P.D : ℝ) * ℓs c) ^ 2 = (P.D : ℝ) ^ 2 * (ℓs c) ^ 2 := by ring
            rw [h2]
            calc (P.D : ℝ) ^ 2 * (ℓs c) ^ 2 ≤ (P.D : ℝ) ^ 2 * 1 :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (P.D : ℝ) ^ 2 := mul_one _
      _ = (((occ I).erase I.k0).card : ℝ) * (P.D : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ 2 * (P.D : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (card_erase_occ I) (sq_nonneg _)
  have key : A ≤ convErr N P T := by
    have hpos : 0 < 2 * (P.eta : ℝ) * (P.D : ℝ) * (T : ℝ) := by positivity
    have e : convErr N P T = ((N : ℝ) ^ 2 * (P.D : ℝ) ^ 2 + (T : ℝ) * ((N : ℝ) ^ 2 * stepC N P)) /
        (2 * (P.eta : ℝ) * (P.D : ℝ) * (T : ℝ)) := by
      unfold convErr stepC
      field_simp
      ring
    rw [e, le_div_iff₀ hpos]
    linarith
  rw [hA] at key
  linarith

/-! ### Accuracy: reduction to a comparator in the box -/

/-- Clamp a vector of class values to `[-1, 1]`. -/
noncomputable def clampR (ℓ : κ → ℝ) : κ → ℝ := fun c => max (-1) (min 1 (ℓ c))

theorem clampR_abs (ℓ : κ → ℝ) (c : κ) : |clampR ℓ c| ≤ 1 := by
  unfold clampR
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clampR_eq (ℓ : κ → ℝ) (c : κ) (h : |ℓ c| ≤ 1) : clampR ℓ c = ℓ c := by
  have h' := abs_le.mp h
  unfold clampR
  rw [min_eq_right h'.2, max_eq_right h'.1]

theorem feas_entry (I : Inst N κ) (hI : I.Good) (ℓ : κ → ℝ) (hℓ : Feas I ℓ) (i j : Fin N)
    (hs : I.sgn i j ≠ 0) : |ℓ (I.cls i j)| ≤ 1 := by
  have h1 : ∀ i, Gam I ℓ i i = 1 := fun i => by
    rw [Gam_apply, hI.sgn_diag, cls_self I hI, hℓ.1]
    norm_num
  have h := psd_unitDiag_abs_le_one hℓ.2 h1 i j
  rw [Gam_apply, abs_mul] at h
  have hs1 : |(I.sgn i j : ℝ)| = 1 := by
    have h2 : |I.sgn i j| = 1 := le_antisymm (hI.sgn_abs i j) (Int.one_le_abs hs)
    exact_mod_cast h2
  rwa [hs1, one_mul] at h

theorem clamp_cls (I : Inst N κ) (hI : I.Good) (ℓ : κ → ℝ) (hℓ : Feas I ℓ) (i j : Fin N)
    (hs : I.sgn i j ≠ 0) : clampR ℓ (I.cls i j) = ℓ (I.cls i j) :=
  clampR_eq _ _ (feas_entry I hI ℓ hℓ i j hs)

theorem Gam_clamp (I : Inst N κ) (hI : I.Good) (ℓ : κ → ℝ) (hℓ : Feas I ℓ) :
    Gam I (clampR ℓ) = Gam I ℓ := by
  ext i j
  rw [Gam_apply, Gam_apply]
  by_cases hs : I.sgn i j = 0
  · rw [hs]
    simp
  · rw [clamp_cls I hI ℓ hℓ i j hs]

theorem obj_clamp (I : Inst N κ) (hI : I.Good) (ℓ : κ → ℝ) (hℓ : Feas I ℓ) :
    obj I (clampR ℓ) = obj I ℓ := by
  unfold obj
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : I.Cs i j = 0
  · rw [hc]
    simp
  · rw [clamp_cls I hI ℓ hℓ i j (hI.Cs_sgn i j hc)]

theorem clamp_feas (I : Inst N κ) (hI : I.Good) (ℓ : κ → ℝ) (hℓ : Feas I ℓ) :
    Feas I (clampR ℓ) := by
  refine ⟨?_, ?_⟩
  · rw [clampR_eq _ _ (by rw [hℓ.1, abs_one])]
    exact hℓ.1
  · rw [Gam_clamp I hI ℓ hℓ]
    exact hℓ.2

/-- Accuracy: every feasible value is within an explicit error of the recorded best value. -/
theorem tied_accurate (I : Inst N κ) (hI : I.Good) (P : Par) (hN : 2 ≤ N) (hD : 0 < P.D)
    (heta : 0 < P.eta) (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (hD2 : 0 < P.D2) (T : ℕ) (hT : 0 < T) (ℓ : κ → ℝ) (hℓ : Feas I ℓ) :
    obj I ℓ ≤ (bestSeq I P T : ℝ) / (P.D2 : ℝ) + 1 / (P.D2 : ℝ) +
      6 * (N : ℝ) ^ 2 / (P.dN : ℝ) + convErr N P T := by
  have _ := hK
  rw [← obj_clamp I hI ℓ hℓ]
  exact accurate_box I hI P hN hD heta hdN hD2 T hT (clampR ℓ) (clamp_feas I hI ℓ hℓ)
    (clampR_abs ℓ)

end QMCTied


