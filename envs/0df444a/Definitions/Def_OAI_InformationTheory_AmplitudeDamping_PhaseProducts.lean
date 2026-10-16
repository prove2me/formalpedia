-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
-- name    : OAI_InformationTheory_AmplitudeDamping_PhaseProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:23:15.570396+00:00
-- url     : https://prove2.me/theorems/2b533875-f073-48bb-8cc2-c92bee33f58a
-- title:
--   Tensor products of qubit matrices and the equiprobable ensemble of product phase states
-- statement:
--   An $n$-qubit matrix is a complex matrix indexed by bit strings $i=(i_0,\dots,i_{n-1})\in\{0,1\}^n$; a density matrix is a positive semidefinite matrix of trace $1$.
--
--   1. **Tensor product of qubit matrices.** For $2\times2$ complex matrices $A_0,\dots,A_{n-1}$,
--   $$\Bigl(\bigotimes_{k=0}^{n-1}A_k\Bigr)_{ij}=\prod_{k=0}^{n-1}(A_k)_{i_kj_k}.$$
--   The file proves that, under the bijection $\{0,1\}^{n+1}\to\{0,1\}\times\{0,1\}^n$, $i\mapsto(i_0,(i_1,\dots,i_n))$, the product $\bigotimes_{k=0}^{n}A_k$ becomes the Kronecker product $A_0\otimes\bigotimes_{k=1}^{n}A_k$; that $\operatorname{tr}\bigotimes_kA_k=\prod_k\operatorname{tr}A_k$; that the empty product ($n=0$) is the $1\times1$ identity; and that a tensor product of positive semidefinite matrices (resp. of density matrices) is positive semidefinite (resp. a density matrix).
--   2. **Product phase states.** For $p\in\mathbb{R}$ and a sign string $s\in\{0,1\}^n$, let $\varphi_b(p)=\sqrt{1-p}\,|0\rangle+(-1)^b\sqrt p\,|1\rangle$ and let $\Phi_s$ be the product vector with amplitudes $\Phi_s(i)=\prod_k\varphi_{s_k}(p)_{i_k}$. The file proves $\Phi_s\Phi_s^*=\bigotimes_k\varphi_{s_k}(p)\varphi_{s_k}(p)^*$, which is a density matrix when $p\in[0,1]$.
--   3. **Uniform weights.** $|\{0,1\}^n|=2^n$ and $\sum_{s\in\{0,1\}^n}2^{-n}=1$.
--   4. **Phase ensemble.** For $p\in[0,1]$, the ensemble of $n$-qubit states consisting of the $2^n$ signals $\Phi_s\Phi_s^*$, $s\in\{0,1\}^n$, each with weight $2^{-n}$ (listed along a fixed enumeration of $\{0,1\}^n$).
--
--   The memoryless generalized amplitude-damping channel maps tensor products to tensor products of single-qubit outputs, so for $\gamma,\nu,p\in[0,1]$ the Holevo quantity of the phase ensemble, $\bigl[S(\sum_s2^{-n}\mathcal N_n(\Phi_s\Phi_s^*))-\sum_s2^{-n}S(\mathcal N_n(\Phi_s\Phi_s^*))\bigr]/\log2$ with $S$ the von Neumann entropy and $\mathcal N_n$ the $n$-qubit channel, equals
--   $$\frac{n}{\log2}\Bigl[h\bigl((1-\gamma)p+\gamma\nu\bigr)-g\bigl(v(\gamma,\nu,p)\bigr)\Bigr],$$
--   where $h$ is the binary entropy in nats, $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$ and $v(\gamma,\nu,p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2$. This ensemble therefore attains $n$ times the single-qubit objective at $p$, the lower-bound side of the formula for the $n$-use Holevo quantity.
--
--   **Formalization Note** The definitions are `tensorMatrix`, `tensorSplit` and `phaseEnsemble n p hp`, a term of the structure `Ensemble n` with size `Fintype.card (Basis n)`, weights $2^{-n}$ and signals enumerated by `Fintype.equivFin`. The listed facts are `tensorMatrix_split`, `tensorMatrix_trace`, `tensorMatrix_zero`, `tensorMatrix_posSemidef`, `tensorMatrix_state`, `phaseState_tensor`, `phaseState_state`, `basis_card` and `phase_weights_sum`; density matrices are `IsState`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PhaseProducts.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PhaseProducts.lean by skeleton subtraction
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

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD

def tensorMatrix (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : QMatrix n :=
  fun i j ↦ ∏ k, A k (i k) (j k)

def tensorSplit (n : ℕ) : Basis (n+1) ≃ Fin 2 × Basis n :=
  (Fin.consEquiv (fun _ : Fin (n+1) ↦ Fin 2)).symm

theorem tensorMatrix_split {n : ℕ} (A : Fin (n+1) → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (tensorSplit n) (tensorSplit n) (tensorMatrix (n+1) A) =
      A 0 ⊗ₖ tensorMatrix n (fun k ↦ A k.succ) := by
  ext i j
  simp [Matrix.reindex_apply,Matrix.submatrix_apply,tensorSplit,tensorMatrix,
    Fin.prod_univ_succ]

theorem tensorMatrix_trace (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorMatrix n A).trace = ∏ k, (A k).trace := by
  exact (Fintype.prod_sum (fun k i ↦ A k i i)).symm

theorem tensorMatrix_zero (A : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix 0 A = 1 := by
  ext i j
  simp [tensorMatrix,Matrix.one_apply,Subsingleton.elim i j]

theorem tensorMatrix_posSemidef (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (tensorMatrix n A).PosSemidef := by
  induction n with
  | zero => rw [tensorMatrix_zero]; exact Matrix.PosSemidef.one
  | succ n ih =>
      have h := (hA 0).kronecker (ih (fun k ↦ A k.succ) (fun k ↦ hA k.succ))
      rw [← tensorMatrix_split A] at h
      have h' := h.submatrix (tensorSplit n)
      simpa only [Matrix.reindex_apply,Matrix.submatrix_submatrix,Equiv.symm_comp_self,
        Matrix.submatrix_id_id] using h'

theorem tensorMatrix_state (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, IsState (A k)) : IsState (tensorMatrix n A) := by
  refine ⟨tensorMatrix_posSemidef n A (fun k ↦ (hA k).1), ?_⟩
  rw [tensorMatrix_trace]
  simp only [(hA _).2,Finset.prod_const_one]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem phaseState_tensor {n : ℕ} (p : ℝ) (s : Basis n) :
    phaseState p s = tensorMatrix n (fun k ↦ pure (phaseSignal p (s k))) := by
  ext i j
  simp only [phaseState,phaseProduct,pure,tensorMatrix,star_prod,Finset.prod_mul_distrib]

theorem phaseState_state {n : ℕ} {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Basis n) :
    IsState (phaseState p s) := by
  rw [phaseState_tensor]
  exact tensorMatrix_state n _ (fun k ↦ pure_state (phaseSignal_mass hp (s k)))

theorem basis_card (n : ℕ) : Fintype.card (Basis n) = 2^n := by
  simp [Basis]

theorem phase_weights_sum (n : ℕ) : (∑ _s : Basis n, ((2:ℝ)^n)⁻¹) = 1 := by
  simp only [Finset.sum_const,Finset.card_univ,basis_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact mul_inv_cancel₀ (pow_ne_zero n (by norm_num))

def phaseEnsemble (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : Ensemble n where
  size := Fintype.card (Basis n)
  weight := fun _ ↦ ((2:ℝ)^n)⁻¹
  weight_nonneg := fun _ ↦ inv_nonneg.mpr (pow_nonneg (by norm_num) n)
  weight_sum := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      phase_weights_sum n
  signal := fun a ↦ phaseState p ((Fintype.equivFin (Basis n)).symm a)
  signal_state := fun a ↦ phaseState_state hp _

end GAD

end

end OAI


