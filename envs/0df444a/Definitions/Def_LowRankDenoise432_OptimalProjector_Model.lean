-- Prove2me | Definitions.Def_LowRankDenoise432_OptimalProjector_Model
-- name    : LowRankDenoise432_OptimalProjector_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:01.355184+00:00
-- url     : https://prove2.me/theorems/c219bce4-a58e-4209-94e1-8b1efc5f92ae
-- title:
--   §2 — noisy replication model, projection estimator, its mean squared error, and spectral projectors
-- statement:
--   These are the objects of Section 2 and Theorem 3.3 of the paper.
--
--   **Model.** On a probability space $(\Omega,\mathcal F,\mathbb P)$, a random true cost vector $c\in\mathbb R^d$ is measurable and each coordinate is square integrable, so that it has a mean $\bar c=\mathbb E[c]$ and a covariance matrix
--   $$(\Sigma_c)_{ef}=\operatorname{Cov}(c_e,c_f).$$
--   There are $m\ge1$ replications $\varepsilon^{(1)},\dots,\varepsilon^{(m)}\in\mathbb R^d$ of measurable noise with $|\varepsilon^{(r)}_e|\le b$ almost surely. Write $\mathcal G=\sigma(c)$. Given $c$, the noise has mean zero, distinct entries are uncorrelated, and the conditional variance of a coordinate does not depend on the replication:
--   1. $\mathbb E[\varepsilon^{(r)}_e\mid\mathcal G]=0$ a.s. for all $r,e$;
--   2. $\mathbb E[\varepsilon^{(r)}_e\varepsilon^{(s)}_f\mid\mathcal G]=0$ a.s. whenever $(r,e)\ne(s,f)$;
--   3. $\operatorname{Var}(\varepsilon^{(r)}_e\mid\mathcal G)=\operatorname{Var}(\varepsilon^{(s)}_e\mid\mathcal G)$ a.s. for all $r,s,e$.
--
--   The noise matrix is $D=\mathbb E[\operatorname{diag}(\operatorname{Var}(\varepsilon_e\mid c))]$, a diagonal matrix with entries $D_{ee}=\mathbb E[\operatorname{Var}(\varepsilon^{(1)}_e\mid\mathcal G)]$. The averages are $\bar\varepsilon=\frac1m\sum_r\varepsilon^{(r)}$ and $\bar y_m=c+\bar\varepsilon$.
--
--   **Estimator and error.** An orthogonal projector is a real $d\times d$ matrix with $\Pi^\top=\Pi$ and $\Pi^2=\Pi$. For a centre $\bar c'$ and an observation $y$, the projection estimate is $\hat c=\bar c'+\Pi(y-\bar c')$; with $\bar c'=\bar c$ and $y=\bar y_m$ this is equation (1). Its error is the genuine expectation
--   $$\operatorname{err}(\Pi)=\mathbb E\,\|\bar c+\Pi(\bar y_m-\bar c)-c\|^2,$$
--   with $\|v\|^2=\sum_e v_e^2$.
--
--   **Spectral objects.** For $n\in\mathbb N$ put $A_n=\Sigma_c-D/n$, a symmetric matrix, with eigenvalues $\lambda_1(A_n)\ge\dots\ge\lambda_d(A_n)$ listed with multiplicity, and $k^*(n)=\#\{j:\lambda_j(A_n)>0\}$. For a real symmetric $A$ and threshold $t$, let $W_t(A)$ be the span of all eigenvectors of $A$ with eigenvalue greater than $t$; $\Pi^+(A)$ is the matrix of the orthogonal projection onto $W_0(A)$, the positive eigenspace. For vectors $u_1,\dots,u_d$, $P_k=\sum_{j\le k}u_ju_j^\top$.
--
--   These definitions carry the paper's estimator, its risk and the spectral rule shared by Lemma 3.2 and Theorem 3.3.
--
--   **Formalization Note.** Vectors are functions `Fin d → ℝ`; $\Pi^+$ is built from Mathlib's `starProjection` on `EuclideanSpace ℝ (Fin d)`, so it does not depend on a choice of eigenbasis. The conditional independence of the paper's model enters only through the conditional second moments 1–3, which it implies (see the Differences lists of the theorems). $\Sigma_c$ uses Mathlib's `covariance`, $D$ uses `condVar` with respect to $\sigma(c)$, and the eigenvalues are `Matrix.IsHermitian.eigenvalues₀`, sorted non-increasingly. The bound $b$ is kept as part of the model although Theorem 3.3 does not use it.
-- source:
--   Henry Aldridge-Krawciw, Irene Aldridge, Low-Rank Denoising for Predict-then-Optimize, STOC 2027 submission #432 (October 2026), source.pdf SHA-256 8d92579f841e1b4853ee9eecd477b739374858db635a23defcc3fb767b137889, PDF p.2, Section 2 (Instances and noise; Estimators, eq. (1)) and Theorem 3.3 (k*(m), positive eigenspace)

import Mathlib
open MeasureTheory ProbabilityTheory Matrix

namespace LowRankDenoise432.OptimalProjector

/-! Section 2 (PDF p.2) of Aldridge-Krawciw–Aldridge, *Low-Rank Denoising for Predict-then-Optimize*:
the noisy replication model, the projection estimator (1), its mean squared error, and the
spectral objects of Theorem 3.3. -/

/-- Squared Euclidean norm `‖v‖² = ∑ₑ vₑ²` of a vector of `ℝ^d`. -/
def sqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ e, v e ^ 2

/-- A (deterministic) orthogonal projector: a symmetric idempotent real matrix. -/
def IsOrthProjector {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Qᵀ = Q ∧ Q * Q = Q

/-- The projection estimator (1) with centre `c'`: `ĉ = c' + Π (y − c')`. -/
def projEstimate {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (c' y : Fin d → ℝ) : Fin d → ℝ :=
  c' + Q *ᵥ (y - c')

/-- The model of Section 2. A random true cost `c ∈ ℝ^d` with square-integrable coordinates,
and `m ≥ 1` replications of noise `ε⁽ʳ⁾ ∈ ℝ^d`, bounded by `b`, which given `c` have mean zero,
are uncorrelated across replications and coordinates (second-moment form of "independent, with
independent coordinates"), and have a conditional variance `Var(ε_e | c)` common to all
replications. `𝒢 = σ(c)` is the σ-algebra generated by `c`. -/
structure NoisyCostModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (d m : ℕ) where
  /-- At least one replication. -/
  m_pos : 0 < m
  /-- The random true cost vector. -/
  c : Ω → Fin d → ℝ
  c_meas : Measurable c
  /-- `c` has a covariance: every coordinate is square integrable. -/
  c_memLp : ∀ e, MemLp (fun ω => c ω e) 2 P
  /-- The replication noises `ε⁽ʳ⁾`, `r = 1, …, m`. -/
  ε : Fin m → Ω → Fin d → ℝ
  ε_meas : ∀ r, Measurable (ε r)
  /-- The noise bound `b`. -/
  b : ℝ
  ε_bdd : ∀ r e, ∀ᵐ ω ∂P, |ε r ω e| ≤ b
  /-- Zero conditional mean given `c`. -/
  cond_mean_zero : ∀ r e,
    P[fun ω => ε r ω e | MeasurableSpace.comap c inferInstance] =ᵐ[P] 0
  /-- Conditionally uncorrelated across replications and coordinates given `c`. -/
  cond_uncorr : ∀ r s e f, (r, e) ≠ (s, f) →
    P[fun ω => ε r ω e * ε s ω f | MeasurableSpace.comap c inferInstance] =ᵐ[P] 0
  /-- `Var(ε_e | c)` does not depend on the replication index. -/
  cond_var_common : ∀ r s e,
    Var[fun ω => ε r ω e; P | MeasurableSpace.comap c inferInstance] =ᵐ[P]
      Var[fun ω => ε s ω e; P | MeasurableSpace.comap c inferInstance]

namespace NoisyCostModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d m : ℕ} (M : NoisyCostModel P d m)

/-- The mean cost `c̄ = 𝔼[c]`. -/
noncomputable def costMean : Fin d → ℝ := fun e => ∫ ω, M.c ω e ∂P

/-- The covariance matrix `Σ_c`, `(Σ_c)_{ef} = Cov(c_e, c_f)`. -/
noncomputable def costCov : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun e f => covariance (fun ω => M.c ω e) (fun ω => M.c ω f) P

/-- `D = 𝔼[diag(Var(ε_e | c))]`, computed from the first replication (all agree by
`cond_var_common`). -/
noncomputable def noiseVar : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal fun e =>
    ∫ ω, Var[fun ω => M.ε ⟨0, M.m_pos⟩ ω e; P | MeasurableSpace.comap M.c inferInstance] ω ∂P

/-- The averaged noise `ε̄ = (1/m) ∑ᵣ ε⁽ʳ⁾`. -/
noncomputable def noiseAvg (ω : Ω) : Fin d → ℝ := ((m : ℝ)⁻¹) • ∑ r, M.ε r ω

/-- The replication average `ȳ_m = c + ε̄`. -/
noncomputable def obsAvg (ω : Ω) : Fin d → ℝ := M.c ω + M.noiseAvg ω

/-- The mean squared error `𝔼‖ĉ_Π − c‖²` of the estimator `ĉ_Π = c̄ + Π(ȳ_m − c̄)` (genuine
Bochner integral). -/
noncomputable def err (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∫ ω, sqNorm (projEstimate Q M.costMean (M.obsAvg ω) - M.c ω) ∂P

/-- The matrix `Σ_c − D/n` for a replication count `n`. -/
noncomputable def adjCov (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  M.costCov - ((n : ℝ)⁻¹) • M.noiseVar

lemma costCov_isHermitian : M.costCov.IsHermitian := by
  ext e f
  simp [costCov, covariance_comm]

lemma noiseVar_isHermitian : M.noiseVar.IsHermitian :=
  isHermitian_diagonal _

lemma adjCov_isHermitian (n : ℕ) : (M.adjCov n).IsHermitian :=
  M.costCov_isHermitian.sub (M.noiseVar_isHermitian.smul (IsSelfAdjoint.all _))

/-- The eigenvalues `λ_j(Σ_c − D/n)`, in non-increasing order. -/
noncomputable def eigs (n : ℕ) : Fin (Fintype.card (Fin d)) → ℝ :=
  (M.adjCov_isHermitian n).eigenvalues₀

/-- `k*(n) = #{j : λ_j(Σ_c − D/n) > 0}`, counted with multiplicity. -/
noncomputable def optRank (n : ℕ) : ℕ :=
  (Finset.univ.filter fun j => 0 < M.eigs n j).card

end NoisyCostModel

/-- The span of the eigenvectors of `A` whose eigenvalue exceeds `t`. -/
noncomputable def eigSpanAbove {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ {v | ∃ μ : ℝ, t < μ ∧ A *ᵥ (WithLp.ofLp v) = μ • WithLp.ofLp v}

/-- The matrix of the orthogonal projection of `ℝ^d` onto a subspace `W`: its `j`-th column is
the projection of the `j`-th standard basis vector. -/
noncomputable def orthProjMatrix {d : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => W.starProjection (EuclideanSpace.single j 1) i

/-- `Π⁺(A)`: the orthogonal projector onto the positive eigenspace of `A`. -/
noncomputable def posProj {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  orthProjMatrix (eigSpanAbove A 0)

/-- `∑_{j<k} u_j u_jᵀ` for a family `u` of vectors: for an orthonormal eigenbasis ordered by
non-increasing eigenvalue, the projector onto a top-`k` eigenspace. -/
def topProj {d : ℕ} (u : Fin d → Fin d → ℝ) (k : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℕ) < k), vecMulVec (u j) (u j)

end LowRankDenoise432.OptimalProjector


