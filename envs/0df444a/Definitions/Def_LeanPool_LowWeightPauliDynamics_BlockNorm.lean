-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_BlockNorm
-- name    : LeanPool_LowWeightPauliDynamics_BlockNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:58:18.246241+00:00
-- url     : https://prove2.me/theorems/ee86ac91-68c1-40ef-b053-c5aea349f84c
-- title:
--   Block Norm
-- statement:
--   Definitions and structural lemmas for Block Norm, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
set_option autoImplicit true
@[expose] public section
open scoped Matrix.Norms.L2Operator
open Matrix Finset WithLp
@[expose] public section
namespace Lean4LPD
variable {𝕜 : Type*} [RCLike 𝕜]
noncomputable def restrictCLM (𝕜 : Type*) [RCLike 𝕜] {p m : Type*}
    (f : p → m) : EuclideanSpace 𝕜 m →L[𝕜] EuclideanSpace 𝕜 p where
  toFun x := toLp 2 (fun i => ofLp x (f i))
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
@[simp] lemma restrictCLM_apply {p m : Type*} (f : p → m)
    (x : EuclideanSpace 𝕜 m) (i : p) : restrictCLM 𝕜 f x i = x (f i) := rfl
section Restrict
variable {m p : Type*} [Fintype m] [Fintype p]
lemma norm_restrictCLM_apply_le {f : p → m} (hf : Function.Injective f)
    (x : EuclideanSpace 𝕜 m) : ‖restrictCLM 𝕜 f x‖ ≤ ‖x‖ := by
  classical
  have hsq : ‖restrictCLM 𝕜 f x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ a ∈ Finset.univ.image f, ‖x a‖ ^ 2 := by
        rw [Finset.sum_image]
        · simp
        · intro a _ b _ hab; exact hf hab
      _ ≤ ∑ a : m, ‖x a‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (by intros; positivity)
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
lemma norm_restrictCLM_le_one {f : p → m} (hf : Function.Injective f) :
    ‖restrictCLM 𝕜 f‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_restrictCLM_apply_le hf x
end Restrict
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
omit [DecidableEq m] [DecidableEq p] in
/-- Selecting a subfamily of rows factors, **definitionally**, through coordinate restriction:
`clm (A.submatrix f id) = restrictCLM 𝕜 f ∘L clm A`. -/
lemma clm_submatrix_id (A : Matrix m n 𝕜) (f : p → m) :
    clm (A.submatrix f (id : n → n)) = (restrictCLM 𝕜 f).comp (clm A) := rfl
omit [DecidableEq m] [DecidableEq p] in
/-- **Row selection does not increase the ℓ² operator norm.** -/
lemma l2_opNorm_submatrix_id_le (A : Matrix m n 𝕜) {f : p → m} (hf : Function.Injective f) :
    ‖A.submatrix f (id : n → n)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def (A := A)]
  calc ‖clm (A.submatrix f (id : n → n))‖
      = ‖(restrictCLM 𝕜 f).comp (clm A)‖ := by rw [clm_submatrix_id]
    _ ≤ ‖restrictCLM 𝕜 f‖ * ‖clm A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖clm A‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_restrictCLM_le_one hf)
omit [DecidableEq m] [DecidableEq p] in
/-- **A block of a matrix has ℓ² operator norm at most that of the matrix.**

`A.submatrix f g` selects the rows indexed by `f` and the columns indexed by `g`. Both index maps
are required to be injective, and that hypothesis cannot be dropped: repeating the single row of
the `1 × 1` identity gives a matrix of norm `√2` (see the last `example` of this file).

The proof selects rows with `l2_opNorm_submatrix_id_le`, conjugate-transposes, and selects rows
again. -/
theorem l2_opNorm_submatrix_le (A : Matrix m n 𝕜) {f : p → m} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  have h1 : A.submatrix f g
      = ((A.submatrix f (id : n → n))ᴴ.submatrix g (id : p → p))ᴴ := by
    ext i j; simp
  rw [h1, Matrix.l2_opNorm_conjTranspose]
  calc ‖(A.submatrix f (id : n → n))ᴴ.submatrix g (id : p → p)‖
      ≤ ‖(A.submatrix f (id : n → n))ᴴ‖ := l2_opNorm_submatrix_id_le _ hg
    _ = ‖A.submatrix f (id : n → n)‖ := Matrix.l2_opNorm_conjTranspose _
    _ ≤ ‖A‖ := l2_opNorm_submatrix_id_le A hf
omit [DecidableEq m] in
/-- `Matrix.toBlock` form of `l2_opNorm_submatrix_le`. -/
theorem l2_opNorm_toBlock_le (A : Matrix m n 𝕜) (P : m → Prop) (Q : n → Prop)
    [DecidablePred P] [DecidablePred Q] : ‖A.toBlock P Q‖ ≤ ‖A‖ :=
  l2_opNorm_submatrix_le A Subtype.val_injective Subtype.val_injective
lemma l2_opNorm_le_one_of_mem_unitary {U : Matrix n n 𝕜} (hU : U ∈ unitary (Matrix n n 𝕜)) :
    ‖U‖ ≤ 1 := by
  have h1 : ‖U‖ = ‖(1 : Matrix n n 𝕜)‖ := by
    rw [← CStarRing.norm_mul_mem_unitary (1 : Matrix n n 𝕜) hU, Matrix.one_mul]
  rw [h1, Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le
omit [DecidableEq m] in
/-- `Matrix.toBlock` form: the `(P, Q)` block of a unitary has ℓ² operator norm at most `1`. -/
theorem l2_opNorm_toBlock_le_one_of_mem_unitary {U : Matrix n n 𝕜}
    (hU : U ∈ unitary (Matrix n n 𝕜)) (P Q : n → Prop) [DecidablePred P] [DecidablePred Q] :
    ‖U.toBlock P Q‖ ≤ 1 :=
  (l2_opNorm_toBlock_le U P Q).trans (l2_opNorm_le_one_of_mem_unitary hU)
section Checks
example {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (w : n → ℕ) (a b : ℕ) :
    ‖U.toBlock (fun s => a ≤ w s) (fun s => w s < b)‖ ≤ 1 :=
  l2_opNorm_toBlock_le_one_of_mem_unitary hU _ _
example : ¬ ‖(1 : Matrix (Fin 1) (Fin 1) ℝ).submatrix (fun _ : Fin 2 => 0) (id : Fin 1 → Fin 1)‖
    ≤ 1 := by
  set A : Matrix (Fin 2) (Fin 1) ℝ :=
    (1 : Matrix (Fin 1) (Fin 1) ℝ).submatrix (fun _ : Fin 2 => 0) (id : Fin 1 → Fin 1) with hA
  set x : EuclideanSpace ℝ (Fin 1) := toLp 2 ![1] with hx
  have hxn : ‖x‖ = 1 := by
    rw [← Real.sqrt_one, EuclideanSpace.norm_eq]
    norm_num [hx]
  have hcoord : ∀ i : Fin 2, (clm A x) i = 1 := by
    intro i
    change (A *ᵥ ofLp x) i = 1
    simp [hA, hx, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hAx : ‖clm A x‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, hcoord 0, hcoord 1]
    norm_num
  intro hle
  have h1 : ‖clm A x‖ ≤ ‖A‖ * ‖x‖ :=
    (Matrix.l2_opNorm_def A) ▸ ContinuousLinearMap.le_opNorm _ _
  rw [hxn, mul_one] at h1
  nlinarith [norm_nonneg (clm A x), norm_nonneg A]
end Checks
end Lean4LPD


