-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
-- name    : OAI_Probability_EntangledGames_SpectralEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:49:50.499121+00:00
-- url     : https://prove2.me/theorems/bcd7d9e1-b80c-49f3-8388-d96c3ddf7395
-- title:
--   Integrating matrix functions: $\int_0^\infty K_A(s)^*K_A(s)\,ds=A$ and the operator entropy $A\log A$
-- statement:
--   Throughout, $n$ is a finite index set and $\mathbb{C}^{n\times n}$ carries its usual (entrywise) topology. For a Hermitian matrix $A=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)\,U^*$ ($U$ unitary, its columns eigenvectors of $A$) and a function $f:\mathbb{R}\to\mathbb{R}$, $f(A)=U\operatorname{diag}(f(\lambda_1),\dots,f(\lambda_n))\,U^*$ is the continuous functional calculus. For $s\in\mathbb{R}$, $K_A(s)=A(A+sI)^{-1}$ is the purification kernel. Integrals over $s\in(0,\infty)$ are taken with respect to Lebesgue measure.
--
--   The file introduces three objects.
--
--   1. **Spectral synthesis map.** For a fixed $U\in\mathbb{C}^{n\times n}$, the continuous $\mathbb{R}$-linear map $\Sigma_U:\mathbb{R}^n\to\mathbb{C}^{n\times n}$, $\Sigma_U(v)=U\operatorname{diag}(v)\,U^*$. For Hermitian $A$ with eigenvector matrix $U$ and eigenvalues $\lambda$, $f(A)=\Sigma_U\bigl((f(\lambda_i))_i\bigr)$.
--   2. **Operator entropy function.** $\eta(A)=A\log A$, the functional calculus of $t\mapsto t\log t$ (with $0\log 0=0$).
--   3. **Entropy integrand.** For $s\in\mathbb{R}$,
--   $$E_A(s)=\frac{1}{1+s}\,A-K_A(s)=\frac{1}{1+s}\,A-A(A+sI)^{-1}.$$
--   For positive semidefinite $A$ and $s>0$ this is $f_s(A)$ with $f_s(t)=\frac{t}{1+s}-\frac{t}{t+s}$; since $\int_0^\infty f_s(t)\,ds=t\log t$ for $t\ge 0$, the integrand $E_A$ is an integral representation of $\eta(A)$.
--
--   The file also proves the analytic facts needed to integrate matrix-valued functions:
--
--   - the cone of positive semidefinite matrices is closed, and the Bochner integral of a matrix-valued function that is positive semidefinite almost everywhere is positive semidefinite;
--   - integration commutes with the functional calculus: if $A$ is Hermitian, $\mu$ is a measure and $s\mapsto f(s,\lambda_i)$ is $\mu$-integrable for every eigenvalue $\lambda_i$ of $A$, then $\int f(s,A)\,d\mu(s)=g(A)$ with $g(t)=\int f(s,t)\,d\mu(s)$;
--   - the spectrum of a positive semidefinite matrix lies in $[0,\infty)$, and for positive semidefinite $A$ and $s>0$ the matrices $(A+sI)^{-1}$, $K_A(s)$ and $K_A(s)^*K_A(s)$ are the functional calculi of $t\mapsto(t+s)^{-1}$, $t\mapsto t/(t+s)$ and $t\mapsto t^2/(t+s)^2$;
--   - for every positive semidefinite $A$,
--   $$\int_0^\infty K_A(s)^*K_A(s)\,ds=A ;$$
--   - square integrability: for $t\ge 0$ the function $s\mapsto t/(t+s)$ lies in $L^2(0,\infty)$; for positive semidefinite $A$ every entry of $s\mapsto K_A(s)$ lies in $L^2(0,\infty)$; if all entries of $F(s)\in\mathbb{C}^{r\times m}$ and $G(s)\in\mathbb{C}^{r\times p}$ lie in $L^2(\mu)$, then $s\mapsto F(s)^*G(s)$ is $\mu$-integrable; consequently $s\mapsto K_A(s)^*K_B(s)$ is integrable on $(0,\infty)$ for positive semidefinite $A,B$.
--
--   These tools turn scalar integral identities into matrix identities. They make the resolvent kernels usable as continuous Gram factorizations of positive semidefinite matrices, and the operator entropy $\eta$ with its integrand $E_A$ is the quantity through which measurement effects are compared in entropy estimates.
--
--   **Formalization Note** Matrices carry the elementwise norm; the local instances `matrixContinuousENorm`, `matrixPreorder`, `matrixClosedIci` and `rectContinuousENorm` only provide the norm, order and closedness needed for Bochner integrals. The definitions are `spectralLinear`, `effectEntropy` (that is, `cfc (fun t => t * Real.log t) A`) and `entropyIntegrand`, none with hypotheses; Mathlib's `cfc` returns $0$ for a non-Hermitian argument and `Real.log 0 = 0`. The displayed identity is `kernel_square_integral`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SpectralEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SpectralEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent

namespace OAI

universe u_n u_α u_m u_p u_r u_J

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
namespace ThresholdParallelRepetition.Resolvent
variable {n : Type u_n} [Fintype n] [DecidableEq n]

local instance matrixContinuousENorm : ContinuousENorm (Matrix n n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

local instance matrixPreorder : Preorder (Matrix n n ℂ) :=
  (Matrix.instPartialOrder : PartialOrder (Matrix n n ℂ)).toPreorder

omit [DecidableEq n] in
lemma isClosed_posSemidef : IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · have heq : {A : Matrix n n ℂ | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)} =
        ⋂ x : n → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by ext; simp
    change IsClosed {A : Matrix n n ℂ | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)}
    rw [heq]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

local instance matrixClosedIci : ClosedIciTopology (Matrix n n ℂ) where
  isClosed_Ici A := by
    exact isClosed_posSemidef.preimage (continuous_id.sub continuous_const)

lemma integral_matrix_nonneg {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {f : α → Matrix n n ℂ} (hf : ∀ᵐ s ∂μ, (f s).PosSemidef) :
    (∫ s, f s ∂μ).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact @integral_nonneg_of_ae α (Matrix n n ℂ) _ _ _ μ _ _ _
    matrixClosedIci f (hf.mono fun _ h => h.nonneg)

def spectralLinear (U : Matrix n n ℂ) : (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => U * diagonal (fun i => (v i : ℂ)) * Uᴴ
      map_add' := by
        intro v w
        simp only [Pi.add_apply, Complex.ofReal_add]
        change U * diagonal ((fun i => (v i : ℂ)) + (fun i => (w i : ℂ))) * Uᴴ = _
        erw [← Matrix.diagonal_add]
        rw [mul_add, add_mul]
      map_smul' := by
        intro c v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have hd : diagonal (fun i => ((c * v i : ℝ) : ℂ)) =
            c • diagonal (fun i => (v i : ℂ)) := by
          ext i j
          simp only [Matrix.diagonal_apply, Matrix.smul_apply, Complex.ofReal_mul,
            Complex.real_smul]
          split_ifs <;> simp
        rw [hd, Matrix.mul_smul, Matrix.smul_mul] }

lemma cfc_eq_spectralLinear {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = spectralLinear (hA.eigenvectorUnitary : Matrix n n ℂ)
      (fun i => f (hA.eigenvalues i)) := by
  rw [hA.cfc_eq]
  rfl

lemma integral_cfc {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : α → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun s => f s (hA.eigenvalues i)) μ) :
    (∫ s, cfc (f s) A ∂μ) = cfc (fun t => ∫ s, f s t ∂μ) A := by
  simp_rw [cfc_eq_spectralLinear hA]
  erw [(spectralLinear _).integral_comp_comm (Integrable.of_eval hf)]
  congr 1
  ext i
  exact eval_integral hf i

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma spectrum_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : t ∈ spectrum ℝ A) : 0 ≤ t := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hA.eigenvalues_nonneg i

lemma resolvent_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    resolvent A s = cfc (fun t : ℝ => (t + s)⁻¹) A := by
  erw [cfc_inv (fun t : ℝ => t + s) A
    (fun t ht => ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hA ht) hs))
    (ha := hA.isHermitian)]
  erw [cfc_add A (fun t : ℝ => t) (fun _ : ℝ => s),
    cfc_id' ℝ A hA.isHermitian, cfc_const s A hA.isHermitian,
    Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse]
  rfl

lemma purificationKernel_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    purificationKernel A s = cfc (fun t : ℝ => t / (t + s)) A := by
  rw [purificationKernel, resolvent_cfc hA hs]
  calc
    A * cfc (fun t : ℝ => (t + s)⁻¹) A =
        cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => (t + s)⁻¹) A := by
      erw [cfc_id' ℝ A hA.isHermitian]
    _ = _ := by
      rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + s)⁻¹) A
        (hg := A.finite_real_spectrum.continuousOn _)]
      rfl

lemma purificationKernel_square_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (purificationKernel A s)ᴴ * purificationKernel A s =
      cfc (fun t : ℝ => t ^ 2 / (t + s) ^ 2) A := by
  rw [purificationKernel_cfc hA hs,
    (cfc_predicate (fun t : ℝ => t / (t + s)) A).isHermitian.eq,
    ← cfc_mul (fun t : ℝ => t / (t + s)) (fun t : ℝ => t / (t + s)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  change t / (t + s) * (t / (t + s)) = t ^ 2 / (t + s) ^ 2
  rw [← pow_two, div_pow]

lemma kernel_square_integral {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (∫ s : ℝ in Ioi 0, (purificationKernel A s)ᴴ * purificationKernel A s) = A := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfc (fun t : ℝ => t ^ 2 / (t + s) ^ 2) A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact purificationKernel_square_cfc hA hs
    _ = cfc (fun t : ℝ => ∫ s : ℝ in Ioi 0, t ^ 2 / (t + s) ^ 2) A :=
      integral_cfc hA.isHermitian _ (fun i => (scalar_square_integral (hA.eigenvalues_nonneg i)).1)
    _ = cfc (fun t : ℝ => t) A := by
      apply cfc_congr
      intro t ht
      exact (scalar_square_integral (spectrum_nonneg hA ht)).2
    _ = A := cfc_id' ℝ A hA.isHermitian

def effectEntropy (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun t : ℝ => t * Real.log t) A

def entropyIntegrand (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (1 / (1 + s) : ℝ) • A - purificationKernel A s

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]
local instance rectContinuousENorm {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] :
    ContinuousENorm (Matrix m p ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

lemma scalar_kernel_memLp {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun s : ℝ => t / (t + s)) 2 (volume.restrict (Ioi 0)) := by
  have hm : Measurable (fun s : ℝ => t / (t + s)) := by fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  simpa only [IntegrableOn, div_pow] using (scalar_square_integral ht).1

lemma kernel_entry_memLp {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : n) :
    MemLp (fun s : ℝ => purificationKernel A s i j) 2 (volume.restrict (Ioi 0)) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let t : n → ℝ := hA.isHermitian.eigenvalues
  have hf (k : n) : MemLp (fun s : ℝ => U i k * (t k / (t k + s) : ℝ) * star (U j k))
      2 (volume.restrict (Ioi 0)) :=
    (((scalar_kernel_memLp (hA.eigenvalues_nonneg k)).ofReal (K := ℂ)).const_mul
      (U i k)).mul_const (star (U j k))
  have hi := memLp_finsetSum Finset.univ (fun k _ => hf k)
  apply hi.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [purificationKernel_cfc hA hs, hA.isHermitian.cfc_eq]
  change (∑ k, U i k * (t k / (t k + s) : ℝ) * star (U j k)) =
    (U * diagonal (fun k => ((t k / (t k + s) : ℝ) : ℂ)) * Uᴴ) i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma integrable_gram {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} {r : Type u_r} [Fintype m] [Fintype p] [Fintype r]
    {f : α → Matrix r m ℂ} {g : α → Matrix r p ℂ}
    (hf : ∀ i j, MemLp (fun s => f s i j) 2 μ)
    (hg : ∀ i j, MemLp (fun s => g s i j) 2 μ) :
    Integrable (fun s => (f s)ᴴ * g s) μ := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  change Integrable (fun s => ∑ k, star (f s k i) * g s k j) μ
  apply integrable_finsetSum
  intro k _
  exact memLp_one_iff_integrable.mp ((hg k j).mul (hf k i).star)

lemma kernel_cross_integrable {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s)ᴴ * purificationKernel B s) (Ioi 0) :=
  integrable_gram (kernel_entry_memLp hA) (kernel_entry_memLp hB)

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.Resolvent

end
end
end
end

end OAI


