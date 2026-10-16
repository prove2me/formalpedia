-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
-- name    : OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:52:45.572968+00:00
-- url     : https://prove2.me/theorems/81818e3e-a4bc-48a8-b159-19e207cd2ebc
-- title:
--   Spectral projections and the typical subspace of a product of qubit states
-- statement:
--   Let $\iota$ be a finite index set and write $\mathcal U(\iota)$ for the group of unitary $\iota\times\iota$ complex matrices. On $n$ qubits the computational basis is indexed by bit strings $x\in\{0,1\}^n$, and operators are $2^n\times2^n$ matrices. The file defines:
--
--   1. **Tensor product of qubit unitaries.** For $U_1,\dots,U_n\in\mathcal U(\{0,1\})$, the $n$-qubit unitary
--   $$\mathbf U=U_1\otimes\cdots\otimes U_n,\qquad \mathbf U_{x,y}=\prod_{k=1}^{n}(U_k)_{x_k,y_k} .$$
--
--   2. **Spectral matrix.** For $U\in\mathcal U(\iota)$ and real weights $q:\iota\to\mathbb{R}$, the Hermitian matrix whose eigenvectors are the columns $u_i=Ue_i$ of $U$, with eigenvalues $q(i)$:
--   $$\operatorname{Spec}(U,q)=U\operatorname{diag}(q)\,U^{*}=\sum_{i\in\iota}q(i)\,u_iu_i^{*} .$$
--
--   3. **Spectral mask.** For a subset $s\subseteq\iota$, the orthogonal projection onto the span of the columns $u_i$ with $i\in s$:
--   $$\Pi_U(s)=\operatorname{Spec}(U,\mathbf 1_s)=\sum_{i\in s}u_iu_i^{*} .$$
--
--   4. **Typical projection.** For qubit unitaries $U_1,\dots,U_n$, a weight vector $q=(q_0,q_1)$ and $\delta\in\mathbb{R}$, the projection onto the span of the product eigenvectors indexed by $\delta$-typical strings:
--   $$\Pi^{n}_{q,\delta}=\Pi_{\mathbf U}\bigl(T^{n}_{q,\delta}\bigr)=\sum_{x\in T^{n}_{q,\delta}}\psi_x\psi_x^{*},\qquad \psi_x=u^{(1)}_{x_1}\otimes\cdots\otimes u^{(n)}_{x_n},$$
--   where $u^{(k)}_b$ is the $b$-th column of $U_k$, and $T^{n}_{q,\delta}$ is the set of strings $x\in\{0,1\}^n$ with $\prod_kq_{x_k}>0$ and $\bigl|\sum_{k=1}^{n}(-\log q_{x_k}-H(q))\bigr|\le n\delta$, with $H(q)=-q_0\log q_0-q_1\log q_1$ (natural logarithms, $0\log0=0$).
--
--   If the $k$-th qubit carries the state $\sigma_k=\operatorname{Spec}(U_k,q)$, all with the same spectrum $q$, then $\Pi^{n}_{q,\delta}$ is the typical-subspace projection of $\sigma_1\otimes\cdots\otimes\sigma_n$. For a probability vector $q$, $\delta>0$ and $n\ge1$, its rank is at most $e^{n(H(q)+\delta)}$, it misses at most $V(q)/(n\delta^2)$ of the trace of the product state, where $V(q)=\sum_bq_b(-\log q_b-H(q))^2$, and it compresses the product state below $e^{-n(H(q)-\delta)}\Pi^{n}_{q,\delta}$. This is the quantum typical-subspace ingredient of the coding (achievability) part of the capacity theorem.
--
--   **Formalization Note** $\mathbf U$ is `tensorEigenUnitary U`. Its unitarity is derived from four auxiliary identities, included in the file, for the entrywise tensor product `tensorMatrix` of $2\times2$ matrices: $(\bigotimes_kA_k)(\bigotimes_kB_k)=\bigotimes_kA_kB_k$, $(\bigotimes_kA_k)^{*}=\bigotimes_kA_k^{*}$, a tensor product of diagonal matrices is diagonal with product entries, and $\bigotimes_kI=I$. `spectralMatrix U q` is `Unitary.conjStarAlgAut ℂ _ U (diagonal q)`, i.e. $U\operatorname{diag}(q)U^{*}$; `spectralMask U s` uses the weights `if i ∈ s then 1 else 0`; and `typicalProjection n U q δ : QMatrix n` is the mask of `typicalSet q δ n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TypicalProjectors.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TypicalProjectors.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensorMatrix_mul {n : ℕ} (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix n A * tensorMatrix n B = tensorMatrix n (fun k ↦ A k*B k) := by
  ext i j
  simp only [tensorMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k l ↦ A k (i k) l*B k l (j k))).symm

theorem tensorMatrix_conjTranspose {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorMatrix n A)ᴴ=tensorMatrix n (fun k ↦ (A k)ᴴ) := by
  ext i j
  simp [tensorMatrix,Matrix.conjTranspose_apply]

theorem tensorMatrix_diagonal {n : ℕ} (a : Fin n → Fin 2 → ℂ) :
    tensorMatrix n (fun k ↦ Matrix.diagonal (a k))=Matrix.diagonal (fun i ↦ ∏ k, a k (i k)) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [tensorMatrix]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hx : ∃ k, i k ≠ j k := by simpa only [not_forall,funext_iff] using hij
    obtain ⟨k,hk⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.diagonal_apply_ne _ hk

theorem tensorMatrix_one {n : ℕ} : tensorMatrix n (fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ))=1 := by
  have h := tensorMatrix_diagonal (fun _ : Fin n ↦ fun _ : Fin 2 ↦ (1:ℂ))
  simpa using h

def tensorEigenUnitary {n : ℕ} (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix.unitaryGroup (Basis n) ℂ :=
  ⟨tensorMatrix n (fun k ↦ U k), by
    constructor
    · change (tensorMatrix n _)ᴴ*tensorMatrix n _=1
      rw [tensorMatrix_conjTranspose,tensorMatrix_mul]
      simp only [← Matrix.star_eq_conjTranspose,Unitary.coe_star_mul_self]
      exact tensorMatrix_one
    · change tensorMatrix n _*(tensorMatrix n _)ᴴ=1
      rw [tensorMatrix_conjTranspose,tensorMatrix_mul]
      simp only [← Matrix.star_eq_conjTranspose,← Unitary.coe_star,Unitary.coe_mul_star_self]
      exact tensorMatrix_one⟩

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

def spectralMatrix (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i ↦ (q i:ℂ)))

def spectralMask (U : Matrix.unitaryGroup ι ℂ) (s : Finset ι) : Matrix ι ι ℂ :=
  spectralMatrix U (fun i ↦ if i ∈ s then 1 else 0)

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_4} [Fintype ι] [DecidableEq ι]

def typicalProjection (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 2 → ℝ) (δ : ℝ) : QMatrix n :=
  spectralMask (tensorEigenUnitary U) (typicalSet q δ n)

end GAD

end

end OAI


