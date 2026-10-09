-- Prove2me | Definitions.Def_SphereSOS_Rate_Setting
-- name    : SphereSOS_Rate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:51.804407+00:00
-- url     : https://prove2.me/theorems/bc8ac7ca-6976-4834-b379-91b491951299
-- title:
--   §1.2, §2, App. A — matrix polynomials, $\ell$-sos on $S^{d-1}$, the Laplacian, harmonic decompositions, and the bound defining $B_{2n}$
-- statement:
--   Let $\mathbb R[x]=\mathbb R[x_1,\dots,x_d]$. A **$k\times k$ matrix polynomial** is a matrix $F=(F_{ab})$ with entries in $\mathbb R[x]$; its value at $x\in\mathbb R^d$ is the real matrix $F(x)=(F_{ab}(x))$.
--
--   1. **$\ell$-sos on the sphere.** A $k\times k$ matrix polynomial $G$ is *$\ell$-sos on $S^{d-1}$* if there are finitely many $k\times k$ matrix polynomials $U_1,\dots,U_m$, every entry of which has total degree at most $\ell$, such that
--   $$G(x)=\sum_{j=1}^m U_j(x)U_j(x)^{\mathsf T}\qquad\text{for all }x\in S^{d-1}.$$
--   2. **Laplacian.** $\Delta f=\sum_{i=1}^d \partial^2 f/\partial x_i^2$, and $\|x\|^2=\sum_i x_i^2$ as a polynomial.
--   3. **Harmonic decomposition.** For a polynomial $f$ and $n\ge0$, a family $h_0,\dots,h_n$ is a *harmonic decomposition of $f$ of half-degree $n$* if each $h_k$ is homogeneous of degree $2k$, $\Delta h_k=0$, and
--   $$f(x)=\sum_{k=0}^n\|x\|^{2(n-k)}h_k(x)\qquad(x\in\mathbb R^d).$$
--   On the sphere $h_k$ is the spherical harmonic component $f_{2k}\in\mathcal H^d_{2k}$ of a homogeneous $f$ of degree $2n$; such a decomposition exists and is unique.
--   4. **The bound defining $B_{2n}$.** A real number $B$ is a *Proposition 5 bound in dimension $d$* if for every homogeneous $f$ of degree $2n$ in $d$ variables, every harmonic decomposition $(h_k)$ of $f$, and every $M$ with $|f|\le M$ on $S^{d-1}$, one has $|h_k|\le BM$ on $S^{d-1}$ for all $k=0,\dots,n$. The paper's $B_{2n}$ is the smallest $B$ that works in every dimension.
--
--   These are the objects of the main theorem: the level $\ell$ of the hierarchy is the degree bound on the factors $U_j$, and $B_{2n}$ controls harmonic projections in the sup norm on the sphere.
--
--   **Formalization Note** Variables are indexed by `Fin d` (0-based). The degree bound is imposed on every entry of every $U_j$, which is the paper's $\deg U_j\le\ell$; the identity is required on the sphere only, as in "agrees with a sum-of-squares polynomial on the sphere". The constant $B_{2n}$ itself is not defined (it would be a real infimum); statements quantify over every Proposition 5 bound $B$, which $B_{2n}$ is.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, pp. 2, 5, 7, 15, §1.2 (definition of ℓ-sos on S^{d−1}), §2 (spherical harmonics, (7)), Proposition 5 and the definition of B_{2n} on p. 7, Appendix A (f(x) = Σ_k ‖x‖^{2(n−k)} f_{2k}(x))

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere

namespace SphereSOS.Rate

noncomputable def evalM {d k : ℕ} (x : Fin d → ℝ)
    (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)) : Matrix (Fin k) (Fin k) ℝ :=
  F.map (MvPolynomial.eval x)

def IsSosOnSphere {d k : ℕ} (ℓ : ℕ)
    (G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)) : Prop :=
  ∃ (m : ℕ) (U : Fin m → Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)),
    (∀ j a b, (U j a b).totalDegree ≤ ℓ) ∧
    ∀ x ∈ sphere d, evalM x G = ∑ j, evalM x (U j) * (evalM x (U j)).transpose

noncomputable def laplacian {d : ℕ} (f : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i f)

noncomputable def normSqPoly (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, MvPolynomial.X i ^ 2

def IsHarmonicDecomp {d : ℕ} (n : ℕ) (f : MvPolynomial (Fin d) ℝ)
    (h : Fin (n + 1) → MvPolynomial (Fin d) ℝ) : Prop :=
  (∀ k, (h k).IsHomogeneous (2 * (k : ℕ))) ∧
  (∀ k, laplacian (h k) = 0) ∧
  f = ∑ k : Fin (n + 1), normSqPoly d ^ (n - (k : ℕ)) * h k

def PropFiveBound (n d : ℕ) (B : ℝ) : Prop :=
  ∀ (f : MvPolynomial (Fin d) ℝ)
    (h : Fin (n + 1) → MvPolynomial (Fin d) ℝ),
    f.IsHomogeneous (2 * n) → IsHarmonicDecomp n f h →
    ∀ M : ℝ, (∀ x ∈ sphere d, |MvPolynomial.eval x f| ≤ M) →
    ∀ k x, x ∈ sphere d → |MvPolynomial.eval x (h k)| ≤ B * M

end SphereSOS.Rate


