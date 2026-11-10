-- Prove2me | Definitions.Def_TruncLowDeg_Recovery_Basic
-- name    : TruncLowDeg_Recovery_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:23:51.333892+00:00
-- url     : https://prove2.me/theorems/fb4fcdef-b282-4914-ae17-cd5268aabf60
-- title:
--   Truncated Gaussians $\mathcal N(\mu,\Sigma)|_S$, the boundary vanishing degree, and polynomial norms on the cube
-- statement:
--   Points of $\mathbb R^d$ are elements of $\mathrm{Vec}\,d=$ `EuclideanSpace ℝ (Fin d)` with coordinates indexed $0,\dots,d-1$, and $d\times d$ real matrices form $\mathrm{Mat}\,d$. For $\mu\in\mathbb R^d$ and a symmetric positive definite $\Sigma$ ($\Sigma\succ0$), $\mathcal N(\mu,\Sigma)$ is the Gaussian measure, and for a set $S\subseteq\mathbb R^d$ the **truncated Gaussian** is $\mathcal N(\mu,\Sigma)$ conditioned on $S$:
--   $$\mathcal N(\mu,\Sigma)|_S(A)=\frac{\mathcal N(\mu,\Sigma)(A\cap S)}{\mathcal N(\mu,\Sigma)(S)} ,$$
--   with density $\phi_{\mu,\Sigma}(x)\,\mathbf 1_{x\in S}/\mathcal N(\mu,\Sigma)(S)$ when $\mathcal N(\mu,\Sigma)(S)>0$.
--
--   A real polynomial $g$ in $d$ variables is **boundary vanishing** for $S$ if $g(x)=0$ for every $x$ in the topological boundary $\partial S$. The **boundary vanishing degree** $\mathrm{BVD}(S)\in\mathbb N\cup\{\infty\}$ is the minimum total degree of a non-zero boundary vanishing polynomial, and $\infty$ if there is none; `BVDLe S k` says some non-zero polynomial of total degree at most $k$ vanishes on $\partial S$, so $\mathrm{BVD}(S)\le k$ exactly when `BVDLe S k`. For example a halfspace has BVD $1$, and a set with empty boundary has BVD $0$.
--
--   $\mathbb R[x]_{\le k}$ is the space of polynomials of total degree at most $k$; $\partial_j$ is the formal partial derivative. For $\rho>0$, $U=\mathrm{Unif}([-\rho,\rho]^d)$ is Lebesgue measure conditioned on the cube and $\|f\|_{L^2(U)}=(\mathbb E_{X\sim U}f(X)^2)^{1/2}$. For a finite list $\hat{\mathcal D}$ of points, $\mathbb E_{\hat{\mathcal D}}[f]=\frac1{|\hat{\mathcal D}|}\sum_{x\in\hat{\mathcal D}}f(x)$. Also defined: $Mx$, the positive semidefinite square root $\Sigma^{1/2}$ and $\Sigma^{-1/2}=(\Sigma^{1/2})^{-1}$, the Loewner order $A\preceq B$ ($B-A$ positive semidefinite), the Frobenius norm $\|A\|_F$, $\sup_{y\in A}|p(y)|$, and the affine polynomial $s_j(x)=(\Sigma^{-1}(x-\mu))_j$.
--
--   **Formalization Note.** The Gaussian is Mathlib's `multivariateGaussian`, conditioning is `ProbabilityTheory.cond` (no measurability of $S$ is required), $\Sigma^{1/2}$ is `CFC.sqrt`, polynomials are `MvPolynomial (Fin d) ℝ` with `totalDegree` and `pderiv`, and $\partial S$ is `frontier S`. `BVD` is an infimum in `ℕ∞`, equal to `⊤` when no polynomial exists. Lean division gives $x/0=0$, so the empirical average of the empty list is $0$.
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 2, Definition 1.3; p. 19, §5.1; pp. 22–24, §5.4; p. 26, Algorithm 1 (line 5)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-!
# Truncated Gaussians, the boundary vanishing degree, and polynomial norms on a cube

Vári-Kakas, Wiedmer, *A General Approach to Polynomial-Time Truncated Learning via Low-Degree
Moments*, STOC 2027 submission (manuscript sha256 613f0e39…): p. 2 Definition 1.3; p. 19 §5.1;
pp. 22–24 §5.4; p. 26 Algorithm 1 (line 5).

* `ℝ^d` is `Vec d = EuclideanSpace ℝ (Fin d)`; coordinates are `0`-based (`Fin d`).
* `Σ ≻ 0` is `Matrix.PosDef` (symmetric positive definite); `A ⪯ B` is `LoewnerLE A B`, i.e.
  `B − A` positive semidefinite.
* `N(µ, Σ)` is Mathlib's `multivariateGaussian`; `N(µ, Σ)|S` is `ProbabilityTheory.cond`,
  i.e. `N(µ, Σ)(S)⁻¹ • N(µ, Σ).restrict S`.
* Polynomials in `d` variables are `MvPolynomial (Fin d) ℝ`; `ℝ[x]_{≤k}` is
  `totalDegree ≤ k`; the formal partial derivative is `MvPolynomial.pderiv`.
* `U = Unif([−ρ, ρ]^d)` is Lebesgue measure conditioned on the cube, and
  `‖f‖_{L²(U)} = (E_{X∼U} f(X)²)^{1/2}`.
-/

/-- Points of `ℝ^d`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `d × d` real matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Matrix–vector product `M x` on `ℝ^d`. -/
noncomputable def mulV {d : ℕ} (M : Mat d) (x : Vec d) : Vec d :=
  WithLp.toLp 2 (M.mulVec (WithLp.ofLp x))

/-- The positive semidefinite square root `Σ^{1/2}` (Mathlib's continuous functional calculus;
the same square root `multivariateGaussian` uses). -/
noncomputable def sqrtM {d : ℕ} (M : Mat d) : Mat d := CFC.sqrt M

/-- `Σ^{−1/2} = (Σ^{1/2})⁻¹`. -/
noncomputable def invSqrt {d : ℕ} (M : Mat d) : Mat d := (sqrtM M)⁻¹

/-- Loewner order `A ⪯ B`: `B − A` is positive semidefinite. -/
def LoewnerLE {d : ℕ} (A B : Mat d) : Prop := (B - A).PosSemidef

/-- Frobenius norm `‖A‖_F = (∑_{i,j} A_{ij}²)^{1/2}`. -/
noncomputable def frob {d : ℕ} (A : Mat d) : ℝ := Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The Gaussian `N(µ, Σ)` on `ℝ^d`. -/
noncomputable def gaussian {d : ℕ} (μ : Vec d) (Sig : Mat d) : Measure (Vec d) :=
  multivariateGaussian μ Sig

/-- The truncated Gaussian `N(µ, Σ)|S`: `N(µ, Σ)` conditioned on `x ∈ S` (§5.1, p. 19). -/
noncomputable def truncGaussian {d : ℕ} (μ : Vec d) (Sig : Mat d) (S : Set (Vec d)) :
    Measure (Vec d) :=
  cond (gaussian μ Sig) S

/-- Evaluation of a polynomial in `d` variables at a point of `ℝ^d`. -/
noncomputable def peval {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (x : Vec d) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

/-- `BVD(S) ≤ k` (Definition 1.3, p. 2): some non-zero real polynomial of total degree at most
`k` vanishes at every point of the topological boundary `∂S`. -/
def BVDLe {d : ℕ} (S : Set (Vec d)) (k : ℕ) : Prop :=
  ∃ g : MvPolynomial (Fin d) ℝ, g ≠ 0 ∧ g.totalDegree ≤ k ∧ ∀ x ∈ frontier S, peval g x = 0

/-- The boundary vanishing degree `BVD(S) ∈ ℕ ∪ {∞}` (Definition 1.3, p. 2): the minimum degree
of a non-zero polynomial vanishing on `∂S`, and `∞` (`⊤`) if there is none. -/
noncomputable def BVD {d : ℕ} (S : Set (Vec d)) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : BVDLe S k), (k : ℕ∞)

/-- The cube `[−ρ, ρ]^d`. -/
def cube (d : ℕ) (ρ : ℝ) : Set (Vec d) := {x | ∀ i, |x i| ≤ ρ}

/-- `U = Unif([−ρ, ρ]^d)`: Lebesgue measure conditioned on the cube. -/
noncomputable def cubeUnif (d : ℕ) (ρ : ℝ) : Measure (Vec d) :=
  cond (volume : Measure (Vec d)) (cube d ρ)

/-- `‖f‖_{L²(U)} = (E_{X∼U} f(X)²)^{1/2}` for a polynomial `f`, `U = Unif([−ρ, ρ]^d)`. -/
noncomputable def L2U {d : ℕ} (ρ : ℝ) (f : MvPolynomial (Fin d) ℝ) : ℝ :=
  Real.sqrt (∫ x, peval f x ^ 2 ∂(cubeUnif d ρ))

/-- `sup_{y ∈ A} |p(y)|` (used for compact non-empty `A`, where it is a maximum). -/
noncomputable def supAbs {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (A : Set (Vec d)) : ℝ :=
  sSup ((fun y => |peval p y|) '' A)

/-- Empirical average `E_D[f] = (1/|D|) ∑_{x ∈ D} f(x)` over a finite list of points
(with multiplicity). -/
noncomputable def empAvg {d : ℕ} (D : List (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (D.map f).sum / D.length

/-- The affine polynomial `s_j(x) = (Σ⁻¹(x − µ))_j` (Lemma 5.2, p. 20; Lemma 6.3, p. 27). -/
noncomputable def sPoly {d : ℕ} (μ : Vec d) (Sig : Mat d) (j : Fin d) : MvPolynomial (Fin d) ℝ :=
  (∑ i, MvPolynomial.C (Sig⁻¹ j i) * MvPolynomial.X i) - MvPolynomial.C ((mulV Sig⁻¹ μ) j)

end TruncLowDeg.Recovery


