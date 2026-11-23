-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:40.708808+00:00
-- url     : https://prove2.me/theorems/7276c24c-9370-4fb0-b87b-23d4a9ad10e6
-- title:
--   Le Two Mul Of Forall Scale
-- statement:
--   Definitions and structural lemmas for Le Two Mul Of Forall Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
namespace GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
def form (H : Matrix n n ℂ) (v w : n → ℂ) : ℂ := v ⬝ᵥ H *ᵥ star w
def gnorm (H : Matrix n n ℂ) (v : n → ℂ) : ℝ := √(form H v v).re
theorem form_eq_sum (H : Matrix n n ℂ) (v w : n → ℂ) :
    form H v w = ∑ a, ∑ b, v a * H a b * conj (w b) := by
  simp [form, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
theorem form_eq_transpose (H : Matrix n n ℂ) (v w : n → ℂ) :
    form H v w = star w ⬝ᵥ Hᵀ *ᵥ v := by
  rw [form, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
theorem posDef_iff {H : Matrix n n ℂ} :
    H.PosDef ↔ H.IsHermitian ∧ ∀ v, v ≠ 0 → 0 < form H v v := by
  constructor
  · intro h
    refine ⟨h.isHermitian, fun v hv => ?_⟩
    simpa [form] using h.dotProduct_mulVec_pos (x := star v) (by simpa using hv)
  · rintro ⟨h, h'⟩
    refine PosDef.of_dotProduct_mulVec_pos h fun x hx => ?_
    simpa [form] using h' (star x) (by simpa using hx)
theorem exists_root {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    ∃ R : (n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ n,
      (∀ v w, form H v w = inner ℂ (R w) (R v)) ∧ ∀ v, gnorm H v = ‖R v‖ := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.transpose.nonneg
  have h1 : ∀ v w, form H v w =
      inner ℂ (WithLp.toLp 2 (B *ᵥ w)) (WithLp.toLp 2 (B *ᵥ v)) := fun v w => by
    rw [form_eq_transpose, hB, EuclideanSpace.inner_toLp_toLp, star_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, dotProduct_comm, star_eq_conjTranspose]
  refine ⟨(WithLp.linearEquiv 2 ℂ (n → ℂ)).symm.toLinearMap ∘ₗ B.mulVecLin, h1, fun v => ?_⟩
  rw [gnorm, h1, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact Real.sqrt_sq (norm_nonneg _)
theorem gnorm_nonneg (H : Matrix n n ℂ) (v : n → ℂ) : 0 ≤ gnorm H v := Real.sqrt_nonneg _
theorem gnorm_smul {H : Matrix n n ℂ} (hH : H.PosSemidef) (c : ℂ) (v : n → ℂ) :
    gnorm H (c • v) = ‖c‖ * gnorm H v := by
  obtain ⟨R, -, h2⟩ := exists_root hH
  rw [h2, h2, map_smul, norm_smul]
@[simp] theorem gnorm_zero (H : Matrix n n ℂ) : gnorm H 0 = 0 := by simp [gnorm, form]
theorem gnorm_pos {H : Matrix n n ℂ} (hH : H.PosDef) {v : n → ℂ} (hv : v ≠ 0) : 0 < gnorm H v :=
  Real.sqrt_pos.2 (Complex.lt_def.1 ((posDef_iff.1 hH).2 v hv)).1
def adj [DecidableEq m] (H : Matrix m m ℂ) (K : Matrix n n ℂ) (T : Matrix n m ℂ) : Matrix m n ℂ :=
  Hᵀ⁻¹ * Tᴴ * Kᵀ
def opNorm (H : Matrix m m ℂ) (K : Matrix n n ℂ) (T : Matrix n m ℂ) : ℝ :=
  sInf {C | 0 ≤ C ∧ ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v}
section OpNorm
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}
theorem exists_bound (hH : H.PosDef) (hK : K.PosSemidef) (T : Matrix n m ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v := by
  obtain ⟨R, -, h2⟩ := exists_root hH.posSemidef
  obtain ⟨S, -, h3⟩ := exists_root hK
  have hR : LinearMap.ker R = ⊥ := LinearMap.ker_eq_bot'.2 fun v hv => by
    by_contra h
    have := gnorm_pos hH h
    rw [h2, hv, norm_zero] at this
    exact lt_irrefl _ this
  obtain ⟨g, hg⟩ := R.exists_leftInverse_of_injective hR
  let A := LinearMap.toContinuousLinearMap (S ∘ₗ T.mulVecLin ∘ₗ g)
  refine ⟨‖A‖, norm_nonneg _, fun v => ?_⟩
  have hv : g (R v) = v := by simpa using LinearMap.congr_fun hg v
  have := A.le_opNorm (R v)
  rw [h2, h3]
  simpa [A, hv] using this
theorem opNorm_nonneg (H : Matrix m m ℂ) (K : Matrix n n ℂ) (T : Matrix n m ℂ) :
    0 ≤ opNorm H K T := Real.sInf_nonneg fun _ h => h.1
theorem opNorm_le_of_bound {T : Matrix n m ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v) : opNorm H K T ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, h⟩
theorem gnorm_mulVec_le (hH : H.PosDef) (hK : K.PosSemidef) (T : Matrix n m ℂ) (v : m → ℂ) :
    gnorm K (T *ᵥ v) ≤ opNorm H K T * gnorm H v := by
  by_cases hv : v = 0
  · simp [hv]
  · have hp := gnorm_pos hH hv
    rw [← div_le_iff₀ hp]
    exact le_csInf (exists_bound hH hK T) fun C hC => (div_le_iff₀ hp).2 (hC.2 v)
theorem opNorm_le_iff (hH : H.PosDef) (hK : K.PosSemidef) {T : Matrix n m ℂ} {C : ℝ} :
    opNorm H K T ≤ C ↔ 0 ≤ C ∧ ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v :=
  ⟨fun h => ⟨(opNorm_nonneg H K T).trans h, fun v => (gnorm_mulVec_le hH hK T v).trans
    (mul_le_mul_of_nonneg_right h (gnorm_nonneg _ _))⟩, fun h => opNorm_le_of_bound h.1 h.2⟩
end OpNorm
section Sesq
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]
structure IsSesq (F : V → V → M) : Prop where

  add_left : ∀ x x' y, F (x + x') y = F x y + F x' y

  smul_left : ∀ (c : ℂ) x y, F (c • x) y = c • F x y

  add_right : ∀ x y y', F x (y + y') = F x y + F x y'

  smul_right : ∀ (c : ℂ) x y, F x (c • y) = conj c • F x y
end Sesq
section Blocks
variable [DecidableEq m] [DecidableEq l]
def subGram (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m m ℂ := H.toBlocks₁₁
def quotGram (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix l l ℂ :=
  H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂
def orthCoeff (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m l ℂ := H.toBlocks₁₁ᵀ⁻¹ * H.toBlocks₂₁ᵀ
variable (m l) in

def incl : Matrix (m ⊕ l) m ℂ := fromRows 1 0
variable (m l) in

def quotMap : Matrix l (m ⊕ l) ℂ := fromCols 0 1
def orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix (m ⊕ l) l ℂ := fromRows (-orthCoeff H) 1
def orthProj (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m (m ⊕ l) ℂ := fromCols 1 (orthCoeff H)
def blockSS (H T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m m ℂ := orthProj H * T * incl m l
def blockSQ (H T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m l ℂ := orthProj H * T * orthLift H
def blockQS (T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix l m ℂ := quotMap m l * T * incl m l
def blockQQ (H T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix l l ℂ := quotMap m l * T * orthLift H
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
end Blocks
section FinFrame
variable {N : ℕ}
def splitFin {k : ℕ} (hk : k ≤ N) : Fin k ⊕ Fin (N - k) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))
def adapt {k : ℕ} (hk : k ≤ N) (T : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin k ⊕ Fin (N - k)) (Fin k ⊕ Fin (N - k)) ℂ :=
  T.submatrix (splitFin hk) (splitFin hk)
def firstGram {k : ℕ} (hk : k ≤ N) (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  H.submatrix (Fin.castLE hk) (Fin.castLE hk)
def lastGram {k : ℕ} (hk : k ≤ N) (H : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin (N - k)) (Fin (N - k)) ℂ := quotGram (adapt hk H)
def stepGram (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Matrix (Fin i ⊕ Unit) (Fin i ⊕ Unit) ℂ :=
  H.submatrix (Sum.elim (Fin.castLE i.2.le) fun _ => i) (Sum.elim (Fin.castLE i.2.le) fun _ => i)
def gradedGram (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : Matrix Unit Unit ℂ :=
  quotGram (stepGram H i)
end FinFrame
example : form (1 : Matrix Unit Unit ℂ) (fun _ => I) (fun _ => 1) = I := by simp [form_eq_sum]
example : quotGram (fromBlocks (1 : Matrix Unit Unit ℂ) (of fun _ _ => I) (of fun _ _ => -I)
    (of fun _ _ => 3) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) () () = 2 := by
  simp [quotGram, mul_apply]; norm_num
example : opNorm (1 : Matrix Unit Unit ℂ) 1 ((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) ≤ 2 ∧
    ¬ opNorm (1 : Matrix Unit Unit ℂ) 1 ((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) ≤ 1 := by
  have h : ∀ v : Unit → ℂ, gnorm 1 (((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) *ᵥ v) = 2 * gnorm 1 v :=
    fun v => by rw [smul_mulVec, one_mulVec, gnorm_smul PosSemidef.one]; simp
  simp only [opNorm_le_iff PosDef.one PosSemidef.one, h]
  refine ⟨⟨by norm_num, fun v => le_rfl⟩, fun h' => ?_⟩
  have := gnorm_pos (H := (1 : Matrix Unit Unit ℂ)) PosDef.one (v := fun _ => 1)
    (fun h0 => one_ne_zero (congrFun h0 ()))
  linarith [h'.2 fun _ => 1]
end GlobalTheory.HermFrame


