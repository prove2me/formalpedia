-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
-- name    : OAI_Analysis_HyperbolicCones_CongruenceMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:39:42.881443+00:00
-- url     : https://prove2.me/theorems/1853b4be-b12b-4f89-9d92-2d7a43101f70
-- title:
--   Congruence maps $X\mapsto S^{\mathsf T}XS$ and invariance of block positive semidefiniteness
-- statement:
--   Let $\mathrm{Sym}_n$ be the real symmetric $n\times n$ matrices. Write $M\succeq0$ when $M$ is positive semidefinite and $M\succ0$ when it is positive definite. For $H\in\mathrm{Sym}_n$ with spectral decomposition $H=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)U^{\mathsf T}$ ($U$ orthogonal), let $H^{-1/2}=U\operatorname{diag}(\mu_1,\dots,\mu_n)U^{\mathsf T}$ with $\mu_i=\lambda_i^{-1/2}$ for $\lambda_i>0$ and $\mu_i=0$ otherwise. Block matrices below have an upper-left $m\times m$ block and a lower-right $n\times n$ block.
--
--   The file defines two congruence maps and records their basic properties.
--
--   1. **Congruence on symmetric matrices.** For a real $n\times n$ matrix $S$, the linear map $\Gamma_S:\mathrm{Sym}_n\to\mathrm{Sym}_n$, $\Gamma_S(X)=S^{\mathsf T}XS$.
--   2. **Two-sided congruence on rectangular matrices.** For real matrices $S\in\mathbb{R}^{m\times m}$ and $T\in\mathbb{R}^{n\times n}$, the linear map $\Gamma_{S,T}:\mathbb{R}^{m\times n}\to\mathbb{R}^{m\times n}$, $\Gamma_{S,T}(A)=S^{\mathsf T}AT$.
--   3. **Positivity.** If $X\in\mathrm{Sym}_n$ and $X\succeq0$, then $\Gamma_S(X)\succeq0$.
--   4. **Normalization.** If $H\in\mathrm{Sym}_n$ and $H\succ0$, then $\Gamma_{H^{-1/2}}(H)=I_n$.
--   5. **Block identity.** For all real matrices $S\in\mathbb{R}^{m\times m}$, $T\in\mathbb{R}^{n\times n}$, $A\in\mathbb{R}^{m\times m}$, $B\in\mathbb{R}^{m\times n}$ and $D\in\mathbb{R}^{n\times n}$,
--   $$
--   \begin{pmatrix}S&0\\0&T\end{pmatrix}^{\mathsf T}\begin{pmatrix}A&B\\B^{\mathsf T}&D\end{pmatrix}\begin{pmatrix}S&0\\0&T\end{pmatrix}=\begin{pmatrix}S^{\mathsf T}AS&S^{\mathsf T}BT\\ (S^{\mathsf T}BT)^{\mathsf T}&T^{\mathsf T}DT\end{pmatrix}.
--   $$
--   6. **Invariance of positive semidefiniteness.** If moreover $S$ and $T$ are invertible, then
--   $$
--   \begin{pmatrix}S^{\mathsf T}AS&S^{\mathsf T}BT\\ (S^{\mathsf T}BT)^{\mathsf T}&T^{\mathsf T}DT\end{pmatrix}\succeq0\iff\begin{pmatrix}A&B\\B^{\mathsf T}&D\end{pmatrix}\succeq0 .
--   $$
--
--   Applying $\Gamma_S$ to the upper-left blocks, $\Gamma_T$ to the lower-right blocks and $\Gamma_{S,T}$ to the off-diagonal blocks of a two-block linear matrix pencil keeps the diagonal maps positive. It also leaves unchanged the set on which the block matrix is positive semidefinite. When the diagonal maps $D,E$ satisfy $D(I)\succ0$ and $E(I)\succ0$, the choice $S=D(I)^{-1/2}$ and $T=E(I)^{-1/2}$ makes both diagonal maps unital.
--
--   **Formalization Note** The maps are `congruenceSym S` and `congruenceRect S T`, with the simp lemmas `congruenceSym_val` and `congruenceRect_apply`. Items 3 to 6 are `congruenceSym_positive`, `congruenceSym_inverseSquareRoot_self`, `block_congruence_identity` and `block_congruence_posSemidef_iff`. Mathlib's `PosSemidef` includes symmetry, so item 6 also transfers the symmetry of $A$ and $D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/CongruenceMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/CongruenceMaps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame

namespace OAI

/-! Linear congruence maps and preservation of a two-block matrix pencil. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

def congruenceSym {n : ℕ} (S : Mat n ℝ) : Sym n →ₗ[ℝ] Sym n where
  toFun X := ⟨Sᵀ * (X : Mat n ℝ) * S, by
    change (Sᵀ * (X : Mat n ℝ) * S).IsHermitian
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul S (show (X : Mat n ℝ).IsHermitian from X.property)⟩
  map_add' X Y := by
    apply Subtype.ext
    change Sᵀ * ((X : Mat n ℝ) + (Y : Mat n ℝ)) * S =
      Sᵀ * (X : Mat n ℝ) * S + Sᵀ * (Y : Mat n ℝ) * S
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by
    apply Subtype.ext
    simp only [selfAdjoint.val_smul, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem congruenceSym_val {n : ℕ} (S : Mat n ℝ) (X : Sym n) :
    (congruenceSym S X : Mat n ℝ) = Sᵀ * (X : Mat n ℝ) * S := rfl

def congruenceRect {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ) :
    Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun A := Sᵀ * A * T
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem congruenceRect_apply {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : congruenceRect S T A = Sᵀ * A * T := rfl

theorem congruenceSym_positive {n : ℕ} (S : Mat n ℝ) (X : Sym n)
    (hX : (X : Mat n ℝ).PosSemidef) : (congruenceSym S X : Mat n ℝ).PosSemidef := by
  simpa only [congruenceSym_val, conjTranspose_eq_transpose_of_trivial] using
    hX.conjTranspose_mul_mul_same S

theorem congruenceSym_inverseSquareRoot_self {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) : congruenceSym (inverseSquareRoot H) H = 1 := by
  apply Subtype.ext
  exact inverseSquareRoot_conjugate H hH

theorem block_congruence_identity {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ)
    (A : Mat m ℝ) (B : Matrix (Fin m) (Fin n) ℝ) (D : Mat n ℝ) :
    (Matrix.fromBlocks S 0 0 T)ᵀ * Matrix.fromBlocks A B Bᵀ D *
        Matrix.fromBlocks S 0 0 T =
      Matrix.fromBlocks (Sᵀ * A * S) (Sᵀ * B * T)
        (Sᵀ * B * T)ᵀ (Tᵀ * D * T) := by
  simp only [Matrix.fromBlocks_transpose, transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_mul,
    transpose_transpose, Matrix.mul_assoc]

theorem block_congruence_posSemidef_iff {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ)
    (hS : IsUnit S) (hT : IsUnit T)
    (A : Mat m ℝ) (B : Matrix (Fin m) (Fin n) ℝ) (D : Mat n ℝ) :
    (Matrix.fromBlocks (Sᵀ * A * S) (Sᵀ * B * T)
      (Sᵀ * B * T)ᵀ (Tᵀ * D * T)).PosSemidef ↔
      (Matrix.fromBlocks A B Bᵀ D).PosSemidef := by
  have hU : IsUnit (Matrix.fromBlocks S (0 : Matrix (Fin m) (Fin n) ℝ) 0 T) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hS, hT⟩
  rw [← block_congruence_identity S T A B D]
  simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    hU.posSemidef_star_left_conjugate_iff (x := Matrix.fromBlocks A B Bᵀ D)

end Paper256

end

end OAI


