-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
-- name    : OAI_Probability_EntangledGames_CoherentFilters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:56:42.265773+00:00
-- url     : https://prove2.me/theorems/410b1745-38ff-43ac-ac4d-7e456137fac8
-- title:
--   Polar parts, binned coherent filters, and Born weights of bipartite states encoded as matrices
-- statement:
--   Let $m,n$ be finite index sets and $\|\cdot\|_2$ the Hilbert–Schmidt (Frobenius) norm. For a positive semidefinite matrix $T$, $T^{1/2}$ is its positive semidefinite square root and $T^{+}$ its support (Moore–Penrose) inverse, obtained by inverting the nonzero eigenvalues. Fix a bin width $\varepsilon$, a shift $s$ and a finite set $L\subset\mathbb{Z}$ of bin labels. For $\ell\in\mathbb{Z}$ let $\sigma(\ell)=e^{\varepsilon(\ell-s)}$; for a real $a$ let $w(a)=e^{\varepsilon(\lfloor\log a/\varepsilon+s\rfloor-s)}$ if $a>0$ and $w(a)=0$ otherwise (the value of $a$ rounded down to the grid $\{\sigma(\ell)\}$); and for a Hermitian matrix $A$ let $P_\ell(A)$ be the orthogonal projection onto the eigenvectors of $A$ with positive eigenvalues $a$ satisfying $\lfloor\log a/\varepsilon+s\rfloor=\ell$.
--
--   1. **Right absolute value and polar part.** For $M\in\mathbb{C}^{m\times n}$: $|M|=(M^*M)^{1/2}\in\mathbb{C}^{n\times n}$ and $\operatorname{pol}(M)=M\,|M|^{+}\in\mathbb{C}^{m\times n}$, the partial isometry in the polar decomposition $M=\operatorname{pol}(M)\,|M|$.
--   2. **Binned filter.** For a square $M\in\mathbb{C}^{n\times n}$, $\Phi_L(M)\in\mathbb{C}^{n\times(n\times L)}$ is the horizontal concatenation of the blocks $\operatorname{pol}(M)\,P_\ell(|M|)$, $\ell\in L$:
--   $$\Phi_L(M)_{i,(j,\ell)}=\bigl(\operatorname{pol}(M)\,P_\ell(|M|)\bigr)_{ij}.$$
--   3. **Rounded matrix.** For $A\in\mathbb{C}^{n\times n}$, $\widetilde A=w(A)$ (functional calculus): every eigenvalue is rounded down to the grid.
--   4. **Bin coverage.** $L$ covers the bins of $A$ if $\lfloor\log a/\varepsilon+s\rfloor\in L$ for every positive real number $a$ in the spectrum of $A$.
--   5. **Cross-binned product and bin mismatch.** For $A,B\in\mathbb{C}^{n\times n}$,
--   $$X_L(A,B)=\sum_{\ell\in L}\sigma(\ell)\,P_\ell(A)\,P_\ell(B),\qquad\Delta_L(A,B)=\sum_{\ell\in L}\sigma(\ell)^2\,\bigl\|P_\ell(A)-P_\ell(B)\bigr\|_2^2 .$$
--   6. **Born weights of a matrix-encoded state.** A matrix $C\in\mathbb{C}^{m\times n}$ is identified with the vector $\operatorname{vec}(C)\in\mathbb{C}^m\otimes\mathbb{C}^n$, $\operatorname{vec}(C)_{(i,j)}=C_{ij}$. For $A\in\mathbb{C}^{m\times m}$ and $B\in\mathbb{C}^{n\times n}$,
--   $$\operatorname{ev}(C;A,B)=\bigl\langle\operatorname{vec}(C),(A\otimes B)\operatorname{vec}(C)\bigr\rangle=\sum_{i,k\in m}\sum_{j,l\in n}\overline{C_{ij}}\,A_{ik}B_{jl}\,C_{kl},\qquad\operatorname{pr}(C;A,B)=\operatorname{Re}\operatorname{ev}(C;A,B).$$
--
--   For the Born weights the file proves the sum formula above; $\operatorname{ev}(C;A,B)=\operatorname{tr}\bigl(C^*A\,C\,B^{\mathsf T}\bigr)$; $\operatorname{pr}(C;A,B)\ge 0$ when $A$ and $B$ are positive semidefinite; additivity of $\operatorname{ev}$ and $\operatorname{pr}$ in $A$ and in $B$; and $\operatorname{ev}(C;I,I)=\operatorname{pr}(C;I,I)=\|C\|_2^2$.
--
--   An unnormalized bipartite pure state is thus a matrix $C$, and $\operatorname{pr}(C;A,B)$ is the probability weight of the product effect $A\otimes B$. The binned filter splits $M$ along the spectral bins of $|M|$. When $\varepsilon>0$ and $L$ covers the bins of $|M|$, the matrix $\operatorname{pol}(M)\,X_L(|M|,|N|)$, assembled from bin projections of two different matrices, approximates $M$ with $\|M-\operatorname{pol}(M)X_L(|M|,|N|)\|_2^2\le 2\varepsilon^2\|M\|_2^2+2\Delta_L(|M|,|N|)$; these are the coherent filters through which the two players approximate their operators.
--
--   **Formalization Note** The definitions are `rightAbs` (via `CFC.sqrt`), `polar` (via the support inverse `supportInverse`), `binFilter`, `roundedAbs`, `CoversBins` (quantifying over `spectrum ℝ A`), `crossBins`, `binMismatch`, `vec`, `eval` and `prob`; labels are elements of a `Finset ℤ`. The approximation bound in the last paragraph is proved separately and is not part of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CoherentFilters.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CoherentFilters.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_m u_n u_p u_ι u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

def rightAbs (M : Matrix m n ℂ) : Matrix n n ℂ := CFC.sqrt (Mᴴ*M)
def polar (M : Matrix m n ℂ) : Matrix m n ℂ := M * supportInverse (rightAbs M)

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def binFilter (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) : Matrix n (n × L) ℂ :=
  fun i jl => (polar M * binProjection (rightAbs M) ε s jl.2) i jl.1

def roundedAbs (A : Matrix n n ℂ) (ε s : ℝ) : Matrix n n ℂ := cfc (fun a => binWeight a ε s) A

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m]
end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def CoversBins (L : Finset ℤ) (A : Matrix n n ℂ) (ε s : ℝ) : Prop :=
  ∀ a ∈ spectrum ℝ A, 0 < a → ⌊Real.log a/ε+s⌋ ∈ L

def crossBins (L : Finset ℤ) (A B : Matrix n n ℂ) (ε s : ℝ) : Matrix n n ℂ :=
  ∑ l : L, binScale ε s l • (binProjection A ε s l * binProjection B ε s l)

def binMismatch (L : Finset ℤ) (A B : Matrix n n ℂ) (ε s : ℝ) : ℝ :=
  ∑ l : L, (binScale ε s l)^2 * hsSq (binProjection A ε s l-binProjection B ε s l)

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

def vec (C : Matrix m n ℂ) : m × n → ℂ := fun i => C i.1 i.2

def eval (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ℂ :=
  star (vec C) ⬝ᵥ ((A ⊗ₖ B) *ᵥ vec C)

def prob (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ℝ :=
  (eval C A B).re

lemma eval_eq_sum (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C A B = ∑ i, ∑ j, ∑ k, ∑ l, star (C i j) * (A i k * B j l) * C k l := by
  simp only [eval, vec, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

lemma prob_nonneg {C : Matrix m n ℂ} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ prob C A B :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg _)).1

lemma eval_add_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C (A+A') B = eval C A B + eval C A' B := by
  simp [eval, Matrix.add_kronecker, Matrix.add_mulVec, dotProduct_add]
lemma eval_add_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    eval C A (B+B') = eval C A B + eval C A B' := by
  simp [eval, Matrix.kronecker_add, Matrix.add_mulVec, dotProduct_add]
lemma prob_add_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (A+A') B = prob C A B + prob C A' B := by
  simp [prob, eval_add_left]
lemma prob_add_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B+B') = prob C A B + prob C A B' := by
  simp [prob, eval_add_right]

lemma eval_one [DecidableEq m] [DecidableEq n] (C : Matrix m n ℂ) :
    eval C 1 1 = (hsSq C : ℂ) := by
  simp only [eval, Matrix.one_kronecker_one, Matrix.one_mulVec, dotProduct,
    Pi.star_apply, Fintype.sum_prod_type, vec, hsSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact Complex.normSq_eq_conj_mul_self.symm

lemma prob_one [DecidableEq m] [DecidableEq n] (C : Matrix m n ℂ) :
    prob C 1 1 = hsSq C := by simp [prob, eval_one]

lemma eval_eq_trace (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C A B = Matrix.trace (Cᴴ * (A * (C * Bᵀ))) := by
  simp only [eval_eq_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  simp only [star, mul_assoc, mul_comm (B j l)]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI


