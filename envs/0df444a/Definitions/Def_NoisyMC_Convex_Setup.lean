-- Prove2me | Definitions.Def_NoisyMC_Convex_Setup
-- name    : NoisyMC_Convex_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:01.580042+00:00
-- url     : https://prove2.me/theorems/7cacc6f7-36f2-4ea4-a1fb-7595ef1a9ec3
-- title:
--   Noisy matrix completion: sub-Gaussian norm, Assumption 1, program (3), ℓ2,∞ norm, objective (17), Conditions 1–2, Algorithm 1 and alignment (28)
-- statement:
--   This module fixes the model and the auxiliary objects of Chen, Chi, Fan, Ma and Yan's analysis of noisy matrix completion. All matrices are real; the unknown matrix is square, $M^\star\in\mathbb R^{n\times n}$, and low-rank factors live in $\mathbb R^{n\times r}$.
--
--   **Singular values of $M^\star$.** $M^\star$ is given with a rank-$r$ singular value decomposition $M^\star=\sum_{k=1}^r\sigma^\star_k u_k v_k^\top$ with $\sigma^\star_k>0$ and orthonormal $u_1,\dots,u_r$ and $v_1,\dots,v_r$ (the published `MatrixCompletion.SVD`). We write $\sigma_{\max}=\max_k\sigma^\star_k$, $\sigma_{\min}=\min_k\sigma^\star_k$ and $\kappa=\sigma_{\max}/\sigma_{\min}$, and
--
--   $$X^\star=U^\star(\Sigma^\star)^{1/2},\qquad Y^\star=V^\star(\Sigma^\star)^{1/2}\qquad(16)$$
--
--   for the balanced factors, whose $k$-th columns are $\sqrt{\sigma^\star_k}\,u_k$ and $\sqrt{\sigma^\star_k}\,v_k$. For an SVD $U\Sigma V^\top$ of any matrix we also name the matrices $U$, $V$ and $\Sigma^{1/2}$. The norm $\|A\|_{2,\infty}$ is the largest Euclidean norm of a row of $A$. An $n\times r$ matrix $X$ has all its singular values in $[\sqrt a,\sqrt b]$ when $a\|v\|_2^2\le\|Xv\|_2^2\le b\|v\|_2^2$ for every $v\in\mathbb R^r$.
--
--   **Assumption 1.** On a probability space $(\Omega_p,P)$:
--
--   1. (random sampling) the indicators $\delta_{ij}=\mathbb 1\{(i,j)\in\Omega\}$, $1\le i,j\le n$, are measurable, mutually independent, and $P(\delta_{ij}=1)=p$;
--   2. (random noise) the entries $E_{ij}$ of the noise matrix are measurable, mutually independent, identically distributed, have mean zero and sub-Gaussian norm at most $\sigma$, where, following [Ver12, Definition 5.7],
--   $$\|X\|_{\psi_2}=\sup_{q\ge1}q^{-1/2}\big(\mathbb E|X|^q\big)^{1/q},$$
--   so that $\|X\|_{\psi_2}\le\sigma$ means $X\in L^q$ and $(\mathbb E|X|^q)^{1/q}\le\sigma\sqrt q$ for every real $q\ge1$;
--   3. the sampling pattern $(\delta_{ij})$ is independent of the noise $(E_{ij})$.
--
--   The observed index set is $\Omega=\{(i,j):\delta_{ij}=1\}$ and the data are $M=M^\star+E$; only $M_{ij}$, $(i,j)\in\Omega$, enter the programs below.
--
--   **The convex program.** With $\mathcal P_\Omega$ the projection keeping the entries in $\Omega$ and zeroing the others (13), the estimator is any minimizer of
--
--   $$\operatorname*{minimize}_{Z\in\mathbb R^{n\times n}}\ g(Z)=\tfrac12\|\mathcal P_\Omega(Z-M)\|_F^2+\lambda\|Z\|_*,\qquad(3)$$
--
--   where $\|Z\|_*$ is the nuclear norm. A best rank-$r$ approximation of $Z$ is any $Z_r$ of rank at most $r$ minimizing $\|Z_r-Z\|_F$ among such matrices.
--
--   **The nonconvex problem.** For $X,Y\in\mathbb R^{n\times r}$,
--
--   $$f(X,Y)=\frac1{2p}\|\mathcal P_\Omega(XY^\top-M)\|_F^2+\frac\lambda{2p}\|X\|_F^2+\frac\lambda{2p}\|Y\|_F^2,\qquad(17)$$
--
--   with gradient $\nabla_Xf=\frac1p\big(\mathcal P_\Omega(XY^\top-M)Y+\lambda X\big)$, $\nabla_Yf=\frac1p\big([\mathcal P_\Omega(XY^\top-M)]^\top X+\lambda Y\big)$ and $\|\nabla f\|_F^2=\|\nabla_Xf\|_F^2+\|\nabla_Yf\|_F^2$.
--
--   - *Condition 1:* (a) $\|\mathcal P_\Omega(E)\|<\lambda/8$ and (b) $\|\mathcal P_\Omega(XY^\top-M^\star)-p(XY^\top-M^\star)\|<\lambda/8$ (spectral norms).
--   - *Condition 2* with constant $c_{\rm inj}$: $p^{-1}\|\mathcal P_\Omega(H)\|_F^2\ge c_{\rm inj}\|H\|_F^2$ for every $H=XA^\top+BY^\top$, $A,B\in\mathbb R^{n\times r}$ (the tangent space of $XY^\top$).
--   - *Algorithm 1:* gradient descent $X^{t+1}=X^t-\eta\nabla_Xf(X^t,Y^t)$, $Y^{t+1}=Y^t-\eta\nabla_Yf(X^t,Y^t)$ from a given start.
--   - *Alignment (28):* $H$ is an $r\times r$ orthogonal matrix minimizing $\|X R-X^\star\|_F^2+\|YR-Y^\star\|_F^2$ over all orthogonal $R$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Matrices are `MatrixCompletion.RealMatrix` and the norms, $\mathcal P_\Omega$, $\mathcal P_T$, $\mathcal P_{T^\perp}$ and the SVD structure come from the published `matrix_completion_*` definitions. The sub-Gaussian bound is the moment form of [Ver12, Definition 5.7], not Mathlib's `HasSubgaussianMGF` and not the Orlicz norm $\inf\{t:\mathbb E e^{X^2/t^2}\le2\}$; the three agree only up to absolute constants. Item 3 of Assumption 1 is added: the paper states independence within each family, and its proofs use joint independence. The singular-value condition is written with squared Euclidean norms. The tangent space of $XY^\top$ is written as $\{XA^\top+BY^\top\}$, which is the paper's description (80). The square root in (28) is dropped, which does not change the minimizers. $\sigma_{\min}$ is the infimum over the $r$ recorded singular values; theorems assume $r\ge1$.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), (1), (3) pp. 2–3; Assumption 1, Definition 1 p. 5; p. 6 notation; Condition 1 p. 11; Condition 2 p. 12; (13)–(17) p. 10; Algorithm 1 p. 13; (28) p. 14; gradient p. 26

import Mathlib
import Definitions.Def_matrix_completion_tangent

/-!
Chen, Chi, Fan, Ma, Yan, *Noisy Matrix Completion: Understanding Statistical Guarantees for Convex
Relaxation via Nonconvex Optimization*, authors' preprint (Sep. 2019; arXiv:1902.07698).

The model of the paper: the sub-Gaussian norm bound of [Ver12, Definition 5.7], Assumption 1
(p. 5), the convex program (3) (p. 3), the ℓ_{2,∞} norm (p. 6), the singular-value summaries of the
SVD of `M⋆` (p. 5), the balanced factors (16), the nonconvex objective (17) and its gradient
(p. 26), Conditions 1 and 2 (pp. 11–12), Algorithm 1 (p. 13) and the alignment (28) (p. 14).
Square `n × n` matrices, rank-`r` factors in `ℝ^{n×r}`.
-/

namespace NoisyMC.Convex

open MatrixCompletion MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ### Norms and singular-value summaries -/

/-- `‖X‖_{2,∞}`: the largest Euclidean norm of a row of `X` (p. 6). -/
noncomputable def twoInfNorm {m k : ℕ} (X : RealMatrix m k) : ℝ :=
  ⨆ i : Fin m, Real.sqrt (∑ j : Fin k, X i j ^ 2)

/-- `σ_max = max_k σ⋆_k`, the largest singular value recorded by the SVD `S` (p. 5). -/
noncomputable def sigmaMax {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : ℝ :=
  ⨆ k : Fin r, S.sigma k

/-- `σ_min = min_k σ⋆_k`, the smallest singular value recorded by the SVD `S` (p. 5). -/
noncomputable def sigmaMin {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : ℝ :=
  ⨅ k : Fin r, S.sigma k

/-- The condition number `κ = σ_max / σ_min` (p. 5). -/
noncomputable def condNum {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : ℝ :=
  sigmaMax S / sigmaMin S

/-- The `n1 × r` matrix `U` whose `k`-th column is the left singular vector `u_k` of `S`. -/
def svdU {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : RealMatrix n1 r :=
  fun i k => S.u k i

/-- The `n2 × r` matrix `V` whose `k`-th column is the right singular vector `v_k` of `S`. -/
def svdV {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : RealMatrix n2 r :=
  fun j k => S.v k j

/-- `Σ^{1/2} = diag(√σ_1, …, √σ_r)`. -/
noncomputable def svdSigmaSqrt {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal fun k => Real.sqrt (S.sigma k)

/-- The balanced factor `X⋆ = U⋆ (Σ⋆)^{1/2}` of (16): column `k` is `√σ_k · u_k`. -/
noncomputable def Xstar {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : RealMatrix n1 r :=
  fun i k => S.u k i * Real.sqrt (S.sigma k)

/-- The balanced factor `Y⋆ = V⋆ (Σ⋆)^{1/2}` of (16): column `k` is `√σ_k · v_k`. -/
noncomputable def Ystar {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) : RealMatrix n2 r :=
  fun j k => S.v k j * Real.sqrt (S.sigma k)

/-- Every singular value of the `n × r` matrix `X` lies in `[√a, √b]`, i.e.
`a ‖v‖² ≤ ‖X v‖² ≤ b ‖v‖²` for every `v ∈ ℝ^r` (Euclidean norms written out). -/
def SingularValuesIn {n r : ℕ} (X : RealMatrix n r) (a b : ℝ) : Prop :=
  ∀ v : Fin r → ℝ,
    a * ∑ k, v k ^ 2 ≤ ∑ i, (X.mulVec v i) ^ 2 ∧ ∑ i, (X.mulVec v i) ^ 2 ≤ b * ∑ k, v k ^ 2

/-! ### Probability model (Assumption 1) -/

/-- `‖X‖_{ψ₂} ≤ σ` for the sub-Gaussian norm of [Ver12, Definition 5.7],
`‖X‖_{ψ₂} = sup_{q ≥ 1} q^{-1/2} (E|X|^q)^{1/q}`: for every real `q ≥ 1`, `X ∈ L^q(P)` and
`(E|X|^q)^{1/q} ≤ σ √q`. -/
def Psi2NormLE {Ωp : Type*} [MeasurableSpace Ωp] (P : Measure Ωp) (X : Ωp → ℝ) (σ : ℝ) :
    Prop :=
  ∀ q : ℝ, 1 ≤ q →
    MemLp X (ENNReal.ofReal q) P ∧ (∫ ω, |X ω| ^ q ∂P) ^ (1 / q) ≤ σ * Real.sqrt q

/-- Assumption 1(a) (random sampling): the indicators `δ_{ij} = 1{(i,j) ∈ Ω}` are measurable,
mutually independent, and each equals `true` with probability `p`. -/
def SamplingModel {n : ℕ} {Ωp : Type*} [MeasurableSpace Ωp] (P : Measure Ωp) (p : ℝ)
    (δ : Fin n × Fin n → Ωp → Bool) : Prop :=
  (∀ ij, Measurable (δ ij)) ∧
    (∀ ij, P {ω | δ ij ω = true} = ENNReal.ofReal p) ∧
    iIndepFun δ P

/-- Assumption 1(b) (random noise): the entries `E_{ij}` are measurable, mutually independent,
identically distributed, zero-mean, with `‖E_{ij}‖_{ψ₂} ≤ σ`. -/
def NoiseModel {n : ℕ} {Ωp : Type*} [MeasurableSpace Ωp] (P : Measure Ωp) (σ : ℝ)
    (E : Fin n × Fin n → Ωp → ℝ) : Prop :=
  (∀ ij, Measurable (E ij)) ∧
    (∀ ij kl, IdentDistrib (E ij) (E kl) P P) ∧
    (∀ ij, ∫ ω, E ij ω ∂P = 0) ∧
    (∀ ij, Psi2NormLE P (E ij) σ) ∧
    iIndepFun E P

/-- Assumption 1, with the independence of the sampling pattern from the noise made explicit
(added hypothesis, used in the proofs): (a), (b), and the vector of indicators
`(δ_{ij})` is independent of the noise matrix `(E_{ij})`. Together these make the `2n²`
variables `{δ_{ij}} ∪ {E_{ij}}` mutually independent. -/
def Assumption1 {n : ℕ} {Ωp : Type*} [MeasurableSpace Ωp] (P : Measure Ωp) (p σ : ℝ)
    (δ : Fin n × Fin n → Ωp → Bool) (E : Fin n × Fin n → Ωp → ℝ) : Prop :=
  SamplingModel P p δ ∧ NoiseModel P σ E ∧
    IndepFun (fun ω ij => δ ij ω) (fun ω ij => E ij ω) P

/-- The random index set `Ω = {(i,j) : δ_{ij} = 1}`. -/
def obsSet {n : ℕ} {Ωp : Type*} (δ : Fin n × Fin n → Ωp → Bool) (ω : Ωp) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => δ ij ω = true

/-- The noise matrix `E = [E_{ij}]`. -/
def noiseMatrix {n : ℕ} {Ωp : Type*} (E : Fin n × Fin n → Ωp → ℝ) (ω : Ωp) : RealMatrix n n :=
  fun i j => E (i, j) ω

/-- The data matrix `M = M⋆ + E` of (1); only its entries on `Ω` enter the programs. -/
def dataMatrix {n : ℕ} {Ωp : Type*} (Mstar : RealMatrix n n) (E : Fin n × Fin n → Ωp → ℝ)
    (ω : Ωp) : RealMatrix n n :=
  Mstar + noiseMatrix E ω

/-! ### The convex program (3) -/

/-- The objective of (3): `g(Z) = ½ ‖P_Ω(Z − M)‖_F² + λ ‖Z‖_*`. -/
noncomputable def cvxObjective {n : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n)
    (lam : ℝ) (Z : RealMatrix n n) : ℝ :=
  (1 / 2) * frobeniusNorm (samplingProjection Ω (Z - M)) ^ 2 + lam * nuclearNorm Z

/-- `Z` is a (global) minimizer of (3). -/
def IsCvxMinimizer {n : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n) (lam : ℝ)
    (Z : RealMatrix n n) : Prop :=
  ∀ Z' : RealMatrix n n, cvxObjective Ω M lam Z ≤ cvxObjective Ω M lam Z'

/-- `Zr` is a best rank-`r` approximation of `Z` in Frobenius norm:
`Zr ∈ argmin_{W : rank W ≤ r} ‖W − Z‖_F`. -/
def IsBestRankApprox {n : ℕ} (r : ℕ) (Z Zr : RealMatrix n n) : Prop :=
  Zr.rank ≤ r ∧ ∀ W : RealMatrix n n, W.rank ≤ r → frobeniusNorm (Zr - Z) ≤ frobeniusNorm (W - Z)

/-! ### The nonconvex problem (17), its gradient, Conditions 1–2, Algorithm 1 and (28) -/

/-- The nonconvex objective (17):
`f(X, Y) = (1/2p) ‖P_Ω(X Yᵀ − M)‖_F² + (λ/2p) ‖X‖_F² + (λ/2p) ‖Y‖_F²`. -/
noncomputable def ncvxObjective {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n)
    (lam p : ℝ) (X Y : RealMatrix n r) : ℝ :=
  1 / (2 * p) * frobeniusNorm (samplingProjection Ω (X * Y.transpose - M)) ^ 2 +
    lam / (2 * p) * frobeniusNorm X ^ 2 + lam / (2 * p) * frobeniusNorm Y ^ 2

/-- `∇_X f(X, Y) = (1/p) (P_Ω(X Yᵀ − M) Y + λ X)` (p. 26). -/
noncomputable def gradX {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n)
    (lam p : ℝ) (X Y : RealMatrix n r) : RealMatrix n r :=
  (1 / p) • (samplingProjection Ω (X * Y.transpose - M) * Y + lam • X)

/-- `∇_Y f(X, Y) = (1/p) ([P_Ω(X Yᵀ − M)]ᵀ X + λ Y)` (p. 26). -/
noncomputable def gradY {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n)
    (lam p : ℝ) (X Y : RealMatrix n r) : RealMatrix n r :=
  (1 / p) • ((samplingProjection Ω (X * Y.transpose - M)).transpose * X + lam • Y)

/-- `‖∇f(X, Y)‖_F = (‖∇_X f‖_F² + ‖∇_Y f‖_F²)^{1/2}`, the Frobenius norm of the stacked gradient. -/
noncomputable def gradNorm {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n)
    (lam p : ℝ) (X Y : RealMatrix n r) : ℝ :=
  Real.sqrt (frobeniusNorm (gradX Ω M lam p X Y) ^ 2 + frobeniusNorm (gradY Ω M lam p X Y) ^ 2)

/-- Condition 1 (p. 11): (a) `‖P_Ω(E)‖ < λ/8`, and
(b) `‖P_Ω(X Yᵀ − M⋆) − p (X Yᵀ − M⋆)‖ < λ/8` (spectral norms). -/
def Condition1 {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (Mstar Emat : RealMatrix n n)
    (p lam : ℝ) (X Y : RealMatrix n r) : Prop :=
  spectralNorm (samplingProjection Ω Emat) < lam / 8 ∧
    spectralNorm (samplingProjection Ω (X * Y.transpose - Mstar) -
      p • (X * Y.transpose - Mstar)) < lam / 8

/-- Condition 2 (p. 12) with constant `c_inj`: `p⁻¹ ‖P_Ω(H)‖_F² ≥ c_inj ‖H‖_F²` for every `H` in
the tangent space `T = {X Aᵀ + B Yᵀ : A, B ∈ ℝ^{n×r}}` of `X Yᵀ`. -/
def Condition2 {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (p cinj : ℝ) (X Y : RealMatrix n r) :
    Prop :=
  ∀ A B : RealMatrix n r,
    cinj * frobeniusNorm (X * A.transpose + B * Y.transpose) ^ 2 ≤
      (1 / p) * frobeniusNorm (samplingProjection Ω (X * A.transpose + B * Y.transpose)) ^ 2

/-- Algorithm 1 (p. 13): gradient descent (27a)–(27b) on (17) with step size `η`, started at
`(X⁰, Y⁰)`; `gdIter … t = (Xᵗ, Yᵗ)`. -/
noncomputable def gdIter {n r : ℕ} (Ω : Finset (Fin n × Fin n)) (M : RealMatrix n n)
    (lam p η : ℝ) (X0 Y0 : RealMatrix n r) : ℕ → RealMatrix n r × RealMatrix n r
  | 0 => (X0, Y0)
  | t + 1 =>
    let XY := gdIter Ω M lam p η X0 Y0 t
    (XY.1 - η • gradX Ω M lam p XY.1 XY.2, XY.2 - η • gradY Ω M lam p XY.1 XY.2)

/-- `H` is a minimizer in (28): `H ∈ O^{r×r}` minimizes
`(‖X R − X⋆‖_F² + ‖Y R − Y⋆‖_F²)^{1/2}` over the orthogonal `r × r` matrices `R`
(equivalently, its square). -/
def IsAlignment {n r : ℕ} (Xs Ys X Y : RealMatrix n r) (H : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  H ∈ Matrix.orthogonalGroup (Fin r) ℝ ∧
    ∀ R ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      frobeniusNorm (X * H - Xs) ^ 2 + frobeniusNorm (Y * H - Ys) ^ 2 ≤
        frobeniusNorm (X * R - Xs) ^ 2 + frobeniusNorm (Y * R - Ys) ^ 2

end NoisyMC.Convex


