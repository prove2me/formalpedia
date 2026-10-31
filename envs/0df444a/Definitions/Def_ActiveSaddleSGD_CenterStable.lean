-- Prove2me | Definitions.Def_ActiveSaddleSGD_CenterStable
-- name    : ActiveSaddleSGD_CenterStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:24.821981+00:00
-- url     : https://prove2.me/theorems/00cdfa7d-8867-463a-9b21-867d4269193c
-- title:
--   The block system (20), its center-stable graphs, and the map $F$ of p.26
-- statement:
--   In the basis of the columns of $P$, the ODE $\dot{\mathrm y}=-D(\mathrm y)$ reads
--   $$
--   \dot{\mathrm y}=-\tilde D(\mathrm y)=-\begin{pmatrix}J^+\mathrm y^+\\J^-\mathrm y^-\end{pmatrix}+R(\mathrm y),
--   $$
--   where the eigenvalues of $J^+$ have nonnegative real parts, those of $J^-$ have negative real parts, and $R$ is $C^3$ near $0$ with $R(0)=0$, $J_R(0)=0$.
--
--   A **center-stable graph** is an open neighbourhood $\mathcal U$ of $0$ in $\mathbb R^{d^+}$ with a $C^2$ function $G:\mathcal U\to\mathbb R^{d^-}$, $G(0)=0$, $J_G(0)=0$, such that $\mathcal V=\{(y^+,y^-):y^+\in\mathcal U,\ y^-=G(y^+)\}$ is invariant: any solution starting on $\mathcal V$ stays on $\mathcal V$ for $t\in(-t_0,t_0)$, for some $t_0>0$. For such $G$ define
--   $$
--   F(w)=-\tilde D^-((w^+,w^-+G(w^+)))+J_G(w^+)\tilde D^+((w^+,w^-+G(w^+))).
--   $$
--
--   The coordinate $w^-=y^--G(y^+)$ measures the distance to the graph, along which the dynamics are repulsive.
--
--   **Formalization Note** $\mathbb R^d$ is identified with $\mathbb R^{d^+}\times\mathbb R^{d^-}$ with the max norm of the product; only neighbourhoods and finiteness of constants are used. `matCLM` is a matrix acting on Euclidean space, and matrix norms are operator norms. Eigenvalues are in $\mathbb C$. A solution is a curve on an interval $(-a,a)$, $a>0$.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, §6.1, p.16, and §7.1, pp.25–26

import Mathlib

open Topology

namespace ActiveSaddleSGD

/-- `A` as a continuous linear operator on `ℝᵐ` with the Euclidean norm. -/
noncomputable def matCLM {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.16: all (complex) eigenvalues of the real
matrix `J` have negative real parts. -/
def HasNegRealParts {m : ℕ} (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), z.re < 0

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.16: all (complex) eigenvalues of the real
matrix `J` have nonnegative real parts. -/
def HasNonnegRealParts {m : ℕ} (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 ≤ z.re

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, equation (20), p.25: the field
`D̃(y) = (J⁺y⁺, J⁻y⁻) − R(y)` in the basis of the columns of `P`, so that the ODE is `ẏ = −D̃(y)`.

**Formalization Note** `ℝᵈ` is identified with `ℝ^{d⁺} × ℝ^{d⁻}` through `P⁻¹`. The product norm is
the max norm; only neighbourhoods and finiteness of constants are used, so the choice of norm does
not matter. -/
noncomputable def blockField {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm))
    (y : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)) :
    EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) :=
  (matCLM Jp y.1, matCLM Jm y.2) - R y

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.25: the data of (20): `J⁺` has eigenvalues
with nonnegative real parts, `J⁻` with negative real parts, and `R` is `C³` on a neighbourhood of
zero with `R(0) = 0`, `J_R(0) = 0` (`R(0) = 0` is `D(0) = 0`, p.16). -/
structure IsBlockSystem {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)) : Prop where
  nonneg : HasNonnegRealParts Jp
  neg : HasNegRealParts Jm
  contDiffOn : ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)),
    ContDiffOn ℝ 3 R V
  map_zero : R 0 = 0
  fderiv_zero : HasFDerivAt R (0 : _ →L[ℝ] _) 0

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Proposition 6, p.25: `𝒰` is an open neighbourhood
of `0` in `ℝ^{d⁺}` and `G` is `C²` on it with `G(0) = 0`, `J_G(0) = 0`, such that the graph
`𝒱 = {(y⁺, y⁻) : y⁺ ∈ 𝒰, y⁻ = G(y⁺)}` is invariant for (20): any solution starting on `𝒱` stays on
`𝒱` for `t ∈ (−t₀, t₀)`, for some `t₀ > 0`.

**Formalization Note** A solution is a curve `y` on an interval `(−a, a)`, `a > 0`, with
`ẏ(t) = −D̃(y(t))` there; the page's "any solution" is local. -/
structure IsCenterStableGraph {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm))
    (𝒰 : Set (EuclideanSpace ℝ (Fin dp)))
    (G : EuclideanSpace ℝ (Fin dp) → EuclideanSpace ℝ (Fin dm)) : Prop where
  isOpen : IsOpen 𝒰
  zero_mem : (0 : EuclideanSpace ℝ (Fin dp)) ∈ 𝒰
  contDiffOn : ContDiffOn ℝ 2 G 𝒰
  map_zero : G 0 = 0
  fderiv_zero : fderiv ℝ G 0 = 0
  invariant : ∀ (y : ℝ → EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)) (a : ℝ), 0 < a →
    (∀ t ∈ Set.Ioo (-a) a, HasDerivAt y (-blockField Jp Jm R (y t)) t) →
    ((y 0).1 ∈ 𝒰 ∧ (y 0).2 = G (y 0).1) →
    ∃ t₀ > 0, ∀ t ∈ Set.Ioo (-t₀) t₀, (y t).1 ∈ 𝒰 ∧ (y t).2 = G (y t).1

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.26: the map
`F(w) = −D̃⁻((w⁺, w⁻ + G(w⁺))) + J_G(w⁺) D̃⁺((w⁺, w⁻ + G(w⁺)))`. -/
noncomputable def graphDefect {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm))
    (G : EuclideanSpace ℝ (Fin dp) → EuclideanSpace ℝ (Fin dm))
    (w : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)) : EuclideanSpace ℝ (Fin dm) :=
  -(blockField Jp Jm R (w.1, w.2 + G w.1)).2 +
    fderiv ℝ G w.1 (blockField Jp Jm R (w.1, w.2 + G w.1)).1

end ActiveSaddleSGD


