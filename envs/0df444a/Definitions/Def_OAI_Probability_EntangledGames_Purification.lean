-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_Purification
-- name    : OAI_Probability_EntangledGames_Purification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:51:22.621837+00:00
-- url     : https://prove2.me/theorems/b214d361-e806-42dd-8731-141b8c0d2dd4
-- title:
--   Finite purification of a family of positive semidefinite matrices via a common resolvent Gram matrix
-- statement:
--   Let $n$ and $J$ be finite index sets and $(A_j)_{j\in J}$ a family of complex $n\times n$ matrices. For a matrix $A$ and $s\in\mathbb{R}$ let $K_A(s)=A(A+sI)^{-1}$ be its purification kernel, and for a positive semidefinite matrix $\Gamma$ let $\Gamma^{1/2}$ be its positive semidefinite square root. Integrals are over $s\in(0,\infty)$ with respect to Lebesgue measure.
--
--   1. **Common kernel.** $\mathcal K(s)\in\mathbb{C}^{n\times(J\times n)}$ is the horizontal concatenation of the kernels of all $A_j$:
--   $$\mathcal K(s)_{r,(j,i)}=K_{A_j}(s)_{r,i},\qquad\text{i.e.}\qquad\mathcal K(s)=\bigl[\,K_{A_j}(s)\,\bigr]_{j\in J}.$$
--   2. **Common Gram matrix.** $\Gamma=\int_0^\infty\mathcal K(s)^*\mathcal K(s)\,ds\in\mathbb{C}^{(J\times n)\times(J\times n)}$.
--   3. **Finite purification.** For $j\in J$, $V_j\in\mathbb{C}^{(J\times n)\times n}$ is the block of columns of $\Gamma^{1/2}$ indexed by $\{j\}\times n$: $(V_j)_{(k,i'),i}=(\Gamma^{1/2})_{(k,i'),(j,i)}$.
--
--   The file proves that $\Gamma$ is always positive semidefinite, and that if every $A_j$ is positive semidefinite, then $s\mapsto\mathcal K(s)^*\mathcal K(s)$ is integrable on $(0,\infty)$, the $(j,k)$ block of $\Gamma$ is $\int_0^\infty K_{A_j}(s)^*K_{A_k}(s)\,ds$, and for all $j,k\in J$
--   $$V_j^*V_k=\int_0^\infty K_{A_j}(s)^*K_{A_k}(s)\,ds,\qquad V_j^*V_j=A_j .$$
--   An auxiliary lemma states that each entry of the integral of an integrable rectangular-matrix-valued function is the integral of that entry.
--
--   Every positive semidefinite $A_j$ is thus written as $V_j^*V_j$ with maps $V_j:\mathbb{C}^n\to\mathbb{C}^{J\times n}$ into one common finite-dimensional space, and the mutual overlaps $V_j^*V_k$ are the resolvent-kernel integrals. This finite-dimensional replacement of the continuous family $(K_{A_j}(s))_{s>0}$ lets differences between effects be measured as differences $V_j-V_k$ of maps into one space, which the entropy estimates then control by an operator-entropy gap.
--
--   **Formalization Note** The objects are `commonKernel`, `commonGram` and `finitePurification`; the square root is `CFC.sqrt`. `commonGram` is a Bochner integral, which Lean sets to $0$ for a non-integrable integrand; positivity of `commonGram` needs no hypothesis, while `commonGram_integrable`, `commonGram_block`, `finitePurification_product` and `finitePurification_self` assume that every `A j` is positive semidefinite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Purification.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Purification.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy

namespace OAI

universe u_n u_α u_m u_p u_J u_R

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci rectContinuousENorm
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma integral_matrix_apply {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] {f : α → Matrix m p ℂ}
    (hf : Integrable f μ) (i : m) (j : p) :
    (∫ s, f s ∂μ) i j = ∫ s, f s i j ∂μ := by
  erw [eval_integral (fun i => hf.eval i), eval_integral (fun j => (hf.eval i).eval j)]

variable {J : Type u_J} [Fintype J] [DecidableEq J]

def commonKernel (A : J → Matrix n n ℂ) (s : ℝ) : Matrix n (J × n) ℂ :=
  fun r v => purificationKernel (A v.1) s r v.2

def commonGram (A : J → Matrix n n ℂ) : Matrix (J × n) (J × n) ℂ :=
  ∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s

omit [DecidableEq J] in
lemma commonGram_integrable (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) :
    IntegrableOn (fun s : ℝ => (commonKernel A s)ᴴ * commonKernel A s) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;> exact kernel_entry_memLp (hA j.1) i j.2

lemma commonGram_posSemidef (A : J → Matrix n n ℂ) : (commonGram A).PosSemidef := by
  apply integral_matrix_nonneg
  exact Filter.Eventually.of_forall fun s => posSemidef_conjTranspose_mul_self (commonKernel A s)

omit [DecidableEq J] in
lemma commonGram_block (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (commonGram A).submatrix (fun i => (j, i)) (fun i => (k, i)) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  ext i l
  change (∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s) (j, i) (k, l) = _
  rw [integral_matrix_apply (commonGram_integrable A hA),
    integral_matrix_apply (kernel_cross_integrable (hA j) (hA k))]
  rfl

def finitePurification (A : J → Matrix n n ℂ) (j : J) : Matrix (J × n) n ℂ :=
  (CFC.sqrt (commonGram A)).submatrix id (fun i => (j, i))

lemma finitePurification_product (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j)ᴴ * finitePurification A k =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  have hh := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (commonGram A))).isHermitian.eq
  unfold finitePurification
  rw [Matrix.conjTranspose_submatrix]
  change (CFC.sqrt (commonGram A))ᴴ.submatrix (fun i => (j, i)) (Equiv.refl (J × n)) *
      (CFC.sqrt (commonGram A)).submatrix (Equiv.refl (J × n)) (fun i => (k, i)) = _
  rw [Matrix.submatrix_mul_equiv, hh,
    CFC.sqrt_mul_sqrt_self (commonGram A) (commonGram_posSemidef A).nonneg]
  exact commonGram_block A hA j k

lemma finitePurification_self (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j : J) :
    (finitePurification A j)ᴴ * finitePurification A j = A j := by
  rw [finitePurification_product A hA, kernel_square_integral (hA j)]

end ThresholdParallelRepetition.Resolvent

end

end OAI


