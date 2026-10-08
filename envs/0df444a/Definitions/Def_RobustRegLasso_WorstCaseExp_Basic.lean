-- Prove2me | Definitions.Def_RobustRegLasso_WorstCaseExp_Basic
-- name    : RobustRegLasso_WorstCaseExp_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:15.535283+00:00
-- url     : https://prove2.me/theorems/cc731787-6b8b-4a26-b5d0-e352345e055e
-- title:
--   The regularized loss of (8), admissible perturbations, the boxes $\mathcal Z_i$, the classes $\mathcal P_n(A,\Delta,b,\sigma)$ and $\hat{\mathcal P}(n)$, and $\sqrt{n\int(b'-r'^\top x)^2\,d\mu}$
-- statement:
--   Fix integers $n$ (the number of samples) and $m$ (the number of features). The data are a response vector $b\in\mathbb R^n$ and an observation matrix $A=(a_{ij})\in\mathbb R^{n\times m}$, whose $i$-th row $r_i^\top=(a_{i1},\dots,a_{im})$ is the feature vector of sample $i$. A coefficient vector is $x\in\mathbb R^m$, and $c$ is a real constant (the paper's $c_n$). Write $\|v\|_2=\sqrt{\sum_i v_i^2}$ and $\|x\|_1=\sum_j|x_j|$.
--
--   1. The **regularized loss** (left-hand side of (8)) is
--   $$\|b-Ax\|_2+\sqrt n\,c\,\|x\|_1+\sqrt n\,c .$$
--   2. A pair $(\sigma,\Delta)$ with $\sigma\in\mathbb R^n$ and $\Delta=(\delta_{ij})\in\mathbb R^{n\times m}$, with columns $\delta_1,\dots,\delta_m\in\mathbb R^n$, is **admissible** if
--   $$\|\sigma\|_2\le\sqrt n\,c\quad\text{and}\quad\|\delta_j\|_2\le\sqrt n\,c\ \text{ for every column } j .$$
--   No sign condition is imposed on $\sigma$ or $\Delta$.
--   3. Points of $\mathbb R^{m+1}$ are pairs $(b',r')$ of a response $b'\in\mathbb R$ and a feature vector $r'\in\mathbb R^m$. The **box** of sample $i$ is
--   $$\mathcal Z_i=[b_i-\sigma_i,\,b_i+\sigma_i]\times\prod_{j=1}^m[a_{ij}-\delta_{ij},\,a_{ij}+\delta_{ij}]\subseteq\mathbb R^{m+1};$$
--   it is empty when some $\sigma_i<0$ or $\delta_{ij}<0$.
--   4. The class $\mathcal P_n(A,\Delta,b,\sigma)$ consists of the Borel probability measures $\mu$ on $\mathbb R^{m+1}$ such that
--   $$\mu\Big(\bigcup_{i\in S}\mathcal Z_i\Big)\ge\frac{|S|}{n}\qquad\text{for every } S\subseteq\{1,\dots,n\},$$
--   the subsets $S=\emptyset$ and $S=\{1,\dots,n\}$ included.
--   5. The class $\hat{\mathcal P}(n)$ is the union of $\mathcal P_n(A,\Delta,b,\sigma)$ over all admissible $(\sigma,\Delta)$.
--   6. The **squared loss** at $(b',r')$ is $(b'-r'^\top x)^2$, and for a measure $\mu$ the quantity of (8) is
--   $$\sqrt{\,n\int_{\mathbb R^{m+1}}(b'-r'^\top x)^2\,d\mu(r',b')\,}\ \in[0,\infty].$$
--
--   These are the objects of Corollary 3 and its proof: the corollary says that the regularized loss is the supremum of the last quantity over $\hat{\mathcal P}(n)$.
--
--   **Formalization Note** $\mathbb R^{m+1}$ is `Fin (m+1) → ℝ` with its product (= Borel) σ-algebra, with the **response first**: $z_0=b'$ and $z_{j+1}=r'_j$. This matches the boxes $\mathcal Z_i$ of p. 11; the integrals of the paper write $d\mu(r',b')$ with the features first, which is notation only. Indices $1,\dots,n$ and $1,\dots,m$ are `Fin n` and `Fin m`; $A$ is a `Matrix (Fin n) (Fin m) ℝ` and $Ax$ is `Matrix.mulVec A x`. The bound $|S|/n$ is `ENNReal.ofReal (|S| / n)`. The integral is the Lebesgue integral of the nonnegative integrand with values in $[0,\infty]$ (`lintegral`), not the Bochner integral, so no integrability hypothesis is needed and no junk value $0$ can occur; the square root is $t\mapsto t^{1/2}$ on $[0,\infty]$. Every $\mu\in\mathcal P_n$ is carried by the bounded set $\bigcup_i\mathcal Z_i$ (take $S=\{1,\dots,n\}$), so the integral is finite there anyway. The class $\mathcal P_n$ duplicates the published set `DistInterpRO.Equivalence.distSet` with weights $c_i=1/n$, whose module was not available to import.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 11, Corollary 3, Eq. (8) and the definitions of P̂(n) and Pn(A, ∆, b, σ); p. 3, Notation

import Mathlib

namespace RobustRegLasso.WorstCaseExp

open MeasureTheory

/-- The Euclidean norm `‖v‖₂ = √(∑ᵢ vᵢ²)` of a vector `v ∈ ℝᵏ`. -/
noncomputable def l2norm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The `ℓ¹` norm `‖x‖₁ = ∑ⱼ |xⱼ|` of a coefficient vector `x ∈ ℝᵐ`. -/
noncomputable def l1norm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∑ j, |x j|

/-- The left-hand side of (8) (arXiv:0811.1790v1, p. 11, Corollary 3):
`‖b − Ax‖₂ + √n c ‖x‖₁ + √n c`, for `A ∈ ℝ^{n×m}`, `b ∈ ℝⁿ`, `x ∈ ℝᵐ` and the constant `c`
(the paper's `cₙ`). -/
noncomputable def regularizedLoss {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (c : ℝ) (x : Fin m → ℝ) : ℝ :=
  l2norm (b - Matrix.mulVec A x) + Real.sqrt n * c * l1norm x + Real.sqrt n * c

/-- The perturbation parameters `(σ, Δ)` are **admissible** (the index set of the union defining
`P̂(n)`, p. 11): `‖σ‖₂ ≤ √n c` and every column `δⱼ = (δ₁ⱼ, …, δₙⱼ)` of `Δ` has
`‖δⱼ‖₂ ≤ √n c`. No sign condition is imposed on `σ` or `Δ`. -/
def Admissible {n m : ℕ} (c : ℝ) (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  l2norm σ ≤ Real.sqrt n * c ∧ ∀ j : Fin m, l2norm (fun i => Δ i j) ≤ Real.sqrt n * c

/-- The box `𝒵ᵢ = [bᵢ − σᵢ, bᵢ + σᵢ] × ∏ⱼ [aᵢⱼ − δᵢⱼ, aᵢⱼ + δᵢⱼ] ⊆ ℝ^{m+1}` of sample `i` (p. 11).
A point of `ℝ^{m+1}` is `z : Fin (m+1) → ℝ` with the **response first**: `z 0 = b'` and
`z (j+1) = r'ⱼ`. The box is empty if some `σᵢ < 0` or `δᵢⱼ < 0`. -/
def box {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) : Set (Fin (m + 1) → ℝ) :=
  {z | z 0 ∈ Set.Icc (b i - σ i) (b i + σ i) ∧
    ∀ j : Fin m, z j.succ ∈ Set.Icc (A i j - Δ i j) (A i j + Δ i j)}

/-- The class `𝒫ₙ(A, Δ, b, σ)` (p. 11): the Borel probability measures `μ` on `ℝ^{m+1}` with
`μ(⋃_{i ∈ S} 𝒵ᵢ) ≥ |S|/n` for **every** `S ⊆ {1, …, n}` (`S = ∅` and `S = {1, …, n}` included). -/
def distClass {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) : Set (Measure (Fin (m + 1) → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧
    ∀ S : Finset (Fin n),
      ENNReal.ofReal ((S.card : ℝ) / n) ≤ μ (⋃ i ∈ S, box A b σ Δ i)}

/-- The class `P̂(n) = ⋃_{‖σ‖₂ ≤ √n c; ∀j: ‖δⱼ‖₂ ≤ √n c} 𝒫ₙ(A, Δ, b, σ)` (p. 11). -/
def hatP {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (c : ℝ) :
    Set (Measure (Fin (m + 1) → ℝ)) :=
  {μ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
    Admissible c σ Δ ∧ μ ∈ distClass A b σ Δ}

/-- The squared loss `(b' − r'ᵀx)²` at the point `z = (b', r') ∈ ℝ^{m+1}` (response first). -/
noncomputable def sqLoss {m : ℕ} (x : Fin m → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  (z 0 - ∑ j : Fin m, z j.succ * x j) ^ 2

/-- The quantity `√(n ∫_{ℝ^{m+1}} (b' − r'ᵀx)² dμ(r', b'))` of (8), computed in `[0, ∞]`: the
integral is the Lebesgue (lower) integral of the nonnegative integrand, so it needs no
integrability hypothesis and is never replaced by a junk value; the square root is `t ↦ t^{1/2}`
on `[0, ∞]`. -/
noncomputable def rootScaledRisk {m : ℕ} (n : ℕ) (x : Fin m → ℝ)
    (μ : Measure (Fin (m + 1) → ℝ)) : ENNReal :=
  ((n : ENNReal) * ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ) ^ (1 / 2 : ℝ)

end RobustRegLasso.WorstCaseExp


