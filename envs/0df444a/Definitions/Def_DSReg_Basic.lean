-- Prove2me | Definitions.Def_DSReg_Basic
-- name    : DSReg_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T04:26:39.258931+00:00
-- url     : https://prove2.me/theorems/c7ab982f-f4cb-4c2b-ae3b-3540506bf4a7
-- title:
--   Dependency supports, Structural Diversity and the DSReg support criterion
-- statement:
--   Objects of Sections 2-3 and Appendix A of Zheng, Klindt, Balestriero and Schölkopf (2026).
--
--   1. **Latents, observations, law.** The world latent is $z\in\mathbb{R}^d$ with law $\mu$, a probability measure on $\mathbb{R}^d$ (the standard Gaussian $N(0,I_d)$ under Theorem 1). An observation is $x=g(z)\in\mathbb{R}^p$. The standard Gaussian is $\mu=\bigotimes_{i=1}^d N(0,1)$.
--   2. **Signed permutations and recovery (Definition 1).** A $d\times d$ matrix $U$ is a signed permutation if there are a permutation $\pi$ and signs $s_i\in\{\pm1\}$ with $U_{ij}=s_i$ for $j=\pi(i)$ and $U_{ij}=0$ otherwise. A representation $\hat z=\hat h(z)$ recovers the individual world latents if, for some such $\pi,s$, $\hat z_i=s_iz_{\pi(i)}$ $\mu$-almost surely for every $i$.
--   3. **Dependency Jacobian and supports (Section 3.2).** $D(z)=\partial x/\partial z$ is the $p\times d$ Jacobian of $g$. A scalar function is active if it is nonzero on a set of positive $\mu$ measure. The a.e. support of a vector function $v$ is $\operatorname{supp}_\mu(v)=\{r: v_r\text{ active}\}$. The footprint of latent $z_i$ is $\mathcal S_i=\{r: D_{ri}\text{ active}\}$, the active set of row $r$ is $I_r=\{i: r\in\mathcal S_i\}$, and the support count of a matrix function $M$ is $\|M(\cdot)\|_{0,\mu}=|\{(r,i): M_{ri}\text{ active}\}|$.
--   4. **Assumptions 1 and 2.** Structural Diversity: $\mathcal S_i\ne\mathcal S_j$ for $i\ne j$. Functional no-cancellation: for every row $r$, $\sum_{i\in I_r}c_iD_{ri}=0$ $\mu$-a.e. forces $c_i=0$ for all $i\in I_r$.
--   5. **DSReg criterion (eq. 3).** Under the premise $h(z)=Qz$ with $Q\in O(d)$, the candidate latents $\tilde z=Rh(z)$, $R\in O(d)$, determine $z=Q^\top R^\top\tilde z$. The candidate Jacobian $\partial x/\partial\tilde z$ is the Jacobian of $\tilde z\mapsto g(Q^\top R^\top\tilde z)$ at $\tilde z=RQz$, viewed as a function of $z$. $R$ is a support minimizer if $R\in O(d)$ minimizes $\|\partial x/\partial\tilde z\|_{0,\mu}$ over $O(d)$.
--   6. **Structural conditions (Proposition 1)**, on sets $\mathcal S_1,\dots,\mathcal S_d\subseteq[p]$. Intersection form: every $k$ has a nonempty $\mathcal C_k\subseteq[p]$ with $\bigcap_{r\in\mathcal C_k}\{i:r\in\mathcal S_i\}=\{k\}$. Overlap-rank form: $|\bigcup_{j\in\mathcal C}\mathcal S_j|-\operatorname{rank}(M^{\mathcal C})>|\mathcal S_k|$ for all $\mathcal C\subseteq[d]$ with $|\mathcal C|\ge2$ and all $k\in\mathcal C$, where $M^{\mathcal C}_{rj}=1$ exactly when $j\in\mathcal C$, $r\in\mathcal S_j$ and $r\in\mathcal S_{j'}$ for some other $j'\in\mathcal C$. Non-Inclusion: $\mathcal S_i\not\subseteq\mathcal S_j$ for $i\ne j$. Structural Variability: $|\mathcal S_i\triangle\mathcal S_j|\ge2$ for $i\ne j$.
--   7. **Whitening (Lemma 4).** $\operatorname{Cov}(h)_{ij}=E[(h_i-Eh_i)(h_j-Eh_j)]$, and $S^{-1/2}$ is the inverse square root of a symmetric matrix by spectral calculus.
--   8. **Constants of Theorem 3 (Appendix A.4).** $\|\cdot\|_2$ is the Euclidean norm and $\|\cdot\|_F$ the Frobenius norm. $G_r=[\langle D_{ri},D_{ri'}\rangle_{L^2(\mu)}]_{i,i'\in I_r}$, $\sigma_r=\lambda_{\min}(G_r)^{1/2}$, $\sigma=\min\{\sigma_r:I_r\ne\emptyset\}$. $v_{rj}(U)=\|U_{I_r,j}\|_2$, $s^*=\sum_i|\mathcal S_i|$, $\rho^*(U)$ is the $(s^*{+}1)$-th largest of the $pd$ values $v_{rj}(U)$, $K_\delta=\{U\in O(d):\min_{P\in SP(d)}\|U-P\|_F\ge\delta\}$, and $\rho^*(\delta)=\min_{U\in K_\delta}\rho^*(U)$, which is $+\infty$ when $K_\delta=\emptyset$. For an estimated Jacobian $\widehat D$ and threshold $\tau$, $\widehat N_\tau(R)=|\{(r,j):\mu(|(\widehat D(z)Q^\top R^\top)_{rj}|>\tau)>0\}|$.
--
--   **Formalization Note** Vectors in $\mathbb{R}^n$ are functions $\mathrm{Fin}\,n\to\mathbb{R}$ and rotations are elements of Mathlib's orthogonal group. $D_{ri}(z)$ is the Fréchet derivative of $g$ at $z$ applied to the $i$-th basis vector, read at coordinate $r$. The paper assumes $g$ differentiable $\mu$-a.e. with measurable Jacobian, and each statement carries these as hypotheses. Functional no-cancellation quantifies over coefficient vectors on all of $[d]$ that vanish off $I_r$. $\lambda_{\min}(G_r)$ is written as the minimum of $c^\top G_rc$ over unit vectors $c$ supported on $I_r$. $\rho^*(\delta)$ is an infimum in the extended reals, so it equals $+\infty$ on an empty $K_\delta$. The inverse square root uses Mathlib's continuous functional calculus with $x\mapsto x^{-1/2}$.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Section 2 (Definition 1), Section 3.2 (Assumptions 1-2, eq. (3), Proposition 1), Section 3.3 (Theorem 3), Appendix A.2-A.4 (Lemmas 2 and 4, constants of the support pattern), pp. 2-7, 17-23

import Mathlib

/-!
Zheng, Klindt, Balestriero and Schölkopf, *DSReg: Provably Recovering Individual World Latents
without Reconstruction*, arXiv:2610.09457v1 (2026): signed-permutation identifiability
(Section 2), dependency Jacobians, dependency supports and footprints, Structural Diversity,
Functional no-cancellation and the DSReg support criterion (Section 3.2), the structural
conditions of Proposition 1 (Section 3.2), and the constants of the support pattern used by
Theorem 3 (Section 3.3 and Appendix A.4).

Latents `z` live in `ℝ^d`, written `Fin d → ℝ`, observations `x = g(z)` in `ℝ^p`, written
`Fin p → ℝ`; `μ` is the law of `z`. Matrices are `Matrix (Fin a) (Fin b) ℝ` and rotations are
elements of `Matrix.orthogonalGroup (Fin d) ℝ`.
-/

open MeasureTheory

noncomputable section

namespace DSReg

/-- Theorem 1 and Lemma 4 (Section 2, p. 3; Appendix A.4, p. 21): the standard Gaussian law
`N(0, I_d)` of the world latent `z`, with independent standard normal coordinates. -/
def stdGaussian (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

/-- Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` of a vector (used for rows `D_{r,:}`, `E_{r,:}` and
coefficient vectors in Theorem 3 and Lemma 5, Section 3.3 and Appendix A.4). -/
def vecNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- Frobenius norm `‖A‖_F = (∑ᵢⱼ Aᵢⱼ²)^{1/2}` (Theorem 3, Section 3.3, p. 7). -/
def frobNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- Definition 1 and Theorem 2 (Sections 2-3.2): `U` is a signed permutation matrix, i.e. there
are a permutation `π` and signs `sᵢ ∈ {±1}` with `U_{ij} = sᵢ` if `j = π(i)` and `0` otherwise,
so that `(U z)ᵢ = sᵢ z_{π(i)}`. -/
def IsSignedPerm {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
    ∀ i j, U i j = if j = σ i then s i else 0

/-- Definition 1 (Section 2, p. 2): the representation `ẑ = zhat(z)` recovers the individual
world latents (is signed-permutation identifiable): for some permutation `π` of `[d]` and signs
`s₁, …, s_d ∈ {±1}`, `ẑᵢ = sᵢ z_{π(i)}` `μ`-almost surely for every `i ∈ [d]`. -/
def RecoversLatents {d : ℕ} (μ : Measure (Fin d → ℝ)) (zhat : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
    ∀ i, ∀ᵐ z ∂μ, zhat z i = s i * z (σ i)

/-- Section 3.2, p. 4: the dependency Jacobian `D(z) = ∂x/∂z` of `x = g(z)`, the `p × d` matrix
with entries `D_{ri}(z) = ∂g_r/∂z_i (z)` (Mathlib's Fréchet derivative applied to the `i`-th basis
vector; the paper assumes `g` differentiable `μ`-a.e.). -/
def depJac {d p : ℕ} (g : (Fin d → ℝ) → Fin p → ℝ) (z : Fin d → ℝ) : Matrix (Fin p) (Fin d) ℝ :=
  fun r i => fderiv ℝ g z (Pi.single i 1) r

/-- Section 3.2, p. 4: a scalar function of the latent is *active* when it is nonzero on a set of
positive `μ` measure. -/
def IsActive {d : ℕ} (μ : Measure (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) : Prop :=
  0 < μ {z | f z ≠ 0}

/-- Lemma 2 (Appendix A.2, p. 17): the a.e. support
`supp_μ(v) = {r : v_r(z) ≠ 0 on a set of positive μ measure}` of a vector-valued function. -/
def aeSupport {d p : ℕ} (μ : Measure (Fin d → ℝ)) (v : (Fin d → ℝ) → Fin p → ℝ) : Set (Fin p) :=
  {r | IsActive μ (fun z => v z r)}

/-- Section 3.2, p. 4: the dependency footprint
`S_i = {r : D_{ri}(z) ≠ 0 on a set of positive μ measure}` of latent `zᵢ`, for a matrix-valued
function `D` (in the paper, the dependency Jacobian). -/
def footprint {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (i : Fin d) : Set (Fin p) :=
  aeSupport μ (fun z r => D z r i)

/-- Assumption 2 (Section 3.2, p. 5): the active set `I_r = {i : D_{ri}(z) ≠ 0 on a set of
positive μ measure}` of observation row `r`, i.e. `{i : r ∈ S_i}`. -/
def activeRow {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (r : Fin p) : Set (Fin d) :=
  {i | r ∈ footprint μ D i}

/-- Section 3.2, p. 4: the support count `‖M(·)‖_{0,μ} = |{(r,i) : M_{ri}(z) ≠ 0 on a set of
positive μ measure}|` of a matrix-valued function `M`. -/
def supportCount {d p : ℕ} (μ : Measure (Fin d → ℝ))
    (M : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ) : ℕ :=
  Set.ncard {x : Fin p × Fin d | IsActive μ (fun z => M z x.1 x.2)}

/-- Assumption 1 (Structural Diversity, Section 3.2, p. 4), stated on footprints
`S_1, …, S_d`: they are pairwise distinct, `S_i ≠ S_j` for all `i ≠ j`. -/
def StructuralDiversity {d p : ℕ} (S : Fin d → Set (Fin p)) : Prop :=
  ∀ i j, i ≠ j → S i ≠ S j

/-- Assumption 2 (Functional no-cancellation, Section 3.2, p. 5): for each row `r`, if
`∑_{i ∈ I_r} cᵢ D_{ri}(z) = 0` for `μ`-a.e. `z` then `cᵢ = 0` for all `i ∈ I_r`. Coefficient
vectors are indexed by `[d]` and required to vanish off `I_r`. -/
def FunctionalNoCancellation {d p : ℕ} (μ : Measure (Fin d → ℝ))
    (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ) : Prop :=
  ∀ (r : Fin p) (c : Fin d → ℝ), (∀ i, i ∉ activeRow μ D r → c i = 0) →
    (∀ᵐ z ∂μ, ∑ i, c i * D z r i = 0) → ∀ i, c i = 0

/-- Lemma 1 and eq. (3) (Section 3.2, p. 5): the Jacobian `∂x/∂z̃` of the observation with
respect to the candidate latents `z̃ = R h(z) = R Q z`, evaluated at the point corresponding to
`z`. Under the premise `h(z) = Q z`, the candidate latents determine `z = Qᵀ Rᵀ z̃`, so `x` as a
function of `z̃` is `z̃ ↦ g(Qᵀ Rᵀ z̃)`, differentiated at `z̃ = R Q z`. -/
def candJac {d p : ℕ} (g : (Fin d → ℝ) → Fin p → ℝ) (Q R : Matrix (Fin d) (Fin d) ℝ)
    (z : Fin d → ℝ) : Matrix (Fin p) (Fin d) ℝ :=
  depJac (fun w => g ((Q.transpose * R.transpose).mulVec w)) ((R * Q).mulVec z)

/-- Eq. (3) (Section 3.2, p. 5): `R` minimizes the DSReg support criterion
`min_{R ∈ O(d)} ‖∂x/∂z̃‖_{0,μ}`, `z̃ = R h(z)`, over the orthogonal group. -/
def IsSupportMinimizer {d p : ℕ} (μ : Measure (Fin d → ℝ)) (g : (Fin d → ℝ) → Fin p → ℝ)
    (Q R : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  R ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
    ∀ R' ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      supportCount μ (candJac g Q R) ≤ supportCount μ (candJac g Q R')

/-- Proposition 1 (1), Structural Sparsity, intersection form (Section 3.2, p. 6): for every
`k ∈ [d]` there is a nonempty set `C_k` of observed variables with
`⋂_{r ∈ C_k} {i ∈ [d] : r ∈ S_i} = {k}`. -/
def SSIntersection {d p : ℕ} (S : Fin d → Set (Fin p)) : Prop :=
  ∀ k : Fin d, ∃ C : Set (Fin p), C.Nonempty ∧ (⋂ r ∈ C, {i : Fin d | r ∈ S i}) = {k}

open Classical in
/-- Proposition 1 (2) (Section 3.2, p. 6): the binary matrix `M^C` with `M^C_{rj} = 1` exactly
when `j ∈ C`, `r ∈ S_j` and `r ∈ S_{j'}` for some other `j' ∈ C`, and `0` otherwise. -/
def overlapMat {d p : ℕ} (S : Fin d → Set (Fin p)) (C : Finset (Fin d)) :
    Matrix (Fin p) (Fin d) ℝ :=
  fun r j => if j ∈ C ∧ r ∈ S j ∧ ∃ j' ∈ C, j' ≠ j ∧ r ∈ S j' then 1 else 0

/-- Proposition 1 (2), Structural Sparsity, overlap-rank form (Section 3.2, p. 6): for every
`C ⊆ [d]` with `|C| ≥ 2` and every `k ∈ C`, `|⋃_{j ∈ C} S_j| - rank(M^C) > |S_k|` (computed in
the integers; the rank is the rank over `ℝ`). -/
def SSOverlapRank {d p : ℕ} (S : Fin d → Set (Fin p)) : Prop :=
  ∀ C : Finset (Fin d), 2 ≤ C.card → ∀ k ∈ C,
    (((⋃ j ∈ C, S j).ncard : ℤ) - ((overlapMat S C).rank : ℤ)) > ((S k).ncard : ℤ)

/-- Proposition 1 (3), Non-Inclusion (Section 3.2, p. 6): `S_i ⊄ S_j` for all `i ≠ j`. -/
def NonInclusion {d p : ℕ} (S : Fin d → Set (Fin p)) : Prop :=
  ∀ i j, i ≠ j → ¬ S i ⊆ S j

/-- Proposition 1 (4), Structural Variability (Section 3.2, p. 6): `|S_i △ S_j| ≥ 2` for all
`i ≠ j`. -/
def StructuralVariability {d p : ℕ} (S : Fin d → Set (Fin p)) : Prop :=
  ∀ i j, i ≠ j → 2 ≤ (symmDiff (S i) (S j)).ncard

/-- Lemma 4 (Appendix A.4, p. 21): the covariance matrix `Cov(h)` of `h(z)` under `μ`,
`Cov(h)_{ij} = E[(hᵢ - E hᵢ)(hⱼ - E hⱼ)]`. -/
def covMat {d : ℕ} (μ : Measure (Fin d → ℝ)) (h : (Fin d → ℝ) → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ z, (h z i - ∫ y, h y i ∂μ) * (h z j - ∫ y, h y j ∂μ) ∂μ

/-- Lemma 4 (Appendix A.4, p. 21): the inverse square root `S^{-1/2}` of a symmetric matrix,
by the continuous functional calculus `x ↦ x^{-1/2}` on its spectrum. -/
def invSqrt {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S

/-- Appendix A.4, p. 22 ("Constants of the support pattern"): the row Gram matrix
`G_r = [⟨D_{ri}, D_{ri'}⟩_{L²(μ)}]`, written on all of `[d] × [d]`; the paper uses its
`I_r × I_r` block. -/
def rowGram {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (r : Fin p) : Matrix (Fin d) (Fin d) ℝ :=
  fun i i' => ∫ z, D z r i * D z r i' ∂μ

/-- Appendix A.4, p. 22: `σ_r = λ_min(G_r)^{1/2}`, the square root of the smallest eigenvalue of
the `I_r × I_r` Gram block, written as the minimum of the Rayleigh quotient `cᵀ G_r c` over unit
vectors `c` supported on `I_r`. -/
def sigmaRow {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (r : Fin p) : ℝ :=
  Real.sqrt (⨅ c : {c : Fin d → ℝ // (∀ i, i ∉ activeRow μ D r → c i = 0) ∧ vecNorm c = 1},
    ∑ i, ∑ i', c.1 i * rowGram μ D r i i' * c.1 i')

/-- Section 3.3, p. 7 and Appendix A.4, p. 22: `σ = min{σ_r : I_r ≠ ∅}`. -/
def sigmaMin {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ) :
    ℝ :=
  ⨅ r : {r : Fin p // (activeRow μ D r).Nonempty}, sigmaRow μ D r.1

/-- Appendix A.4, p. 22: `v_{rj}(U) = ‖U_{I_r, j}‖₂`, the norm of the part of column `j` of `U`
in the rows `I_r` (zero when `I_r = ∅`). -/
def colMass {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℝ) (r : Fin p) (j : Fin d) : ℝ :=
  Real.sqrt (∑ i, (activeRow μ D r).indicator (fun i => U i j ^ 2) i)

/-- Section 3.3, p. 7 and Appendix A.4, p. 22: the population minimum `s* = ∑ᵢ |S_i|`. -/
def sStar {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ) : ℕ :=
  ∑ i, (footprint μ D i).ncard

/-- Theorem 3 and Appendix A.4, p. 22: the distance `min_{P ∈ SP(d)} ‖U - P‖_F` from `U` to the
set `SP(d)` of signed permutation matrices. -/
def distSP {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨅ P : {P : Matrix (Fin d) (Fin d) ℝ // IsSignedPerm P}, frobNorm (U - P.1)

/-- Appendix A.4, p. 22: `ρ*(U)`, the `(s*+1)`-th largest of the `pd` values `v_{rj}(U)`
(the values sorted in decreasing order with multiplicity, read at index `s*`; `0` if `s*+1 > pd`,
which the paper's hypotheses exclude). -/
def rhoStarU {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin p × Fin d)).val.map (fun x => colMass μ D U x.1 x.2)).sort
    (· ≥ ·)).getD (sStar μ D) 0

/-- Section 3.3, p. 7 and Appendix A.4, p. 22: the pattern margin
`ρ*(δ) = min_{U ∈ K_δ} ρ*(U)` over `K_δ = {U ∈ O(d) : min_{P ∈ SP(d)} ‖U - P‖_F ≥ δ}`, with
`ρ*(δ) = +∞` when `K_δ = ∅` (an infimum in the extended reals). -/
def rhoStar {d p : ℕ} (μ : Measure (Fin d → ℝ)) (D : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ)
    (δ : ℝ) : EReal :=
  ⨅ (U : Matrix (Fin d) (Fin d) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧ δ ≤ distSP U),
    (rhoStarU μ D U : EReal)

/-- Theorem 3 (Section 3.3, p. 7): the thresholded count
`N̂_τ(R) = |{(r,j) : μ(|(D̂(z) Qᵀ Rᵀ)_{rj}| > τ) > 0}|` for an estimated Jacobian `D̂`. -/
def threshCount {d p : ℕ} (μ : Measure (Fin d → ℝ))
    (Dhat : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ)
    (R : Matrix (Fin d) (Fin d) ℝ) : ℕ :=
  Set.ncard {x : Fin p × Fin d |
    0 < μ {z | τ < |(Dhat z * Q.transpose * R.transpose) x.1 x.2|}}

end DSReg


