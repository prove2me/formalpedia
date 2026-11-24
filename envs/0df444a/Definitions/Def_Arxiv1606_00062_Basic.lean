-- Prove2me | Definitions.Def_Arxiv1606_00062_Basic
-- name    : Arxiv1606_00062_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T22:07:12.257627+00:00
-- url     : https://prove2.me/theorems/0b876f63-8012-425b-a78d-766cbf6f5a3c
-- title:
--   Multiple scattering iterations, Krylov subspaces, ORTHODIR directions and the rate $\mathcal R_2$
-- statement:
--   Objects of Sections 2, 3 and 5 of Boubendir, Ecevit and Reitich (2016).
--
--   1. **Multiple scattering iterations (eq. 10).** Let $V$ be a complex inner product space, $\mathcal T:V\to V$ a bounded linear operator (in the paper, the iteration operator (7) on $L^2(\partial\Omega)$) and $g\in V$. The multiple scattering iterations are $\eta^0=g$ and $\eta^m=\mathcal T\eta^{m-1}$, that is $\eta^m=\mathcal T^m g$.
--   2. **Krylov subspace (Section 5).** For the equation $(\mathcal I-\mathcal T)\eta=g$ with initial guess $\mu^{(0)}=0$, the $m$-th Krylov subspace is
--   $$K_m=\operatorname{span}\{g,(\mathcal I-\mathcal T)g,\dots,(\mathcal I-\mathcal T)^{m-1}g\}.$$
--   3. **ORTHODIR directions (Section 5).** For a bounded operator $\mathcal A$ and $g\in V$, the ORTHODIR directions are $p^{(0)}=g$ and
--   $$p^{(j+1)}=\mathcal A p^{(j)}+\sum_{i=0}^{j}\beta_{ij}\,p^{(i)},\qquad \beta_{ij}=-\frac{\langle \mathcal A^2p^{(j)},\mathcal A p^{(i)}\rangle}{\langle \mathcal A p^{(i)},\mathcal A p^{(i)}\rangle},$$
--   with $\langle\cdot,\cdot\rangle$ linear in its first argument. The residuals, step sizes and iterates of steps 2.1-2.3 do not enter the directions.
--   4. **The rate $\mathcal R_2$ (Theorem 3, two dimensions).** For a wavenumber $k$, a distance $d$ and curvatures $\kappa_1,\kappa_2$,
--   $$\mathcal R_2=e^{2ikd}\Big(\sqrt{(1+d\kappa_1)(1+d\kappa_2)}\,\Big[1+\sqrt{1-[(1+d\kappa_1)(1+d\kappa_2)]^{-1}}\Big]\Big)^{-1}.$$
--
--   **Formalization Note** The concrete operator $\mathcal T$ of eq. (7), built from Helmholtz boundary integral operators, is not constructed; it is a parameter. The directions $p^{(j)}$ are defined by recursion on the list $p^{(0)},\dots,p^{(j)}$. If $\mathcal Ap^{(i)}=0$ the algorithm breaks down; the formal $\beta_{ij}$ is then $0$. The real square roots in $\mathcal R_2$ are applied only to positive numbers when $d>0$ and $\kappa_1,\kappa_2>0$.
-- source:
--   Boubendir, Ecevit and Reitich, Acceleration of an iterative method for the evaluation of high-frequency multiple scattering effects, arXiv:1606.00062v1 (2016), https://arxiv.org/abs/1606.00062, Section 2 eq. (10), Section 3 Theorem 3 (2D formula for R_2, PDF p. 7), Section 5 (Krylov subspace and ORTHODIR, PDF pp. 11-12)

import Mathlib

/-!
Boubendir, Ecevit and Reitich, *Acceleration of an iterative method for the evaluation of
high-frequency multiple scattering effects*, arXiv:1606.00062v1 (2016): the multiple scattering
iterations of Section 2 (eq. (10)), the Krylov subspace and the ORTHODIR iteration of Section 5,
and the two-dimensional 2-periodic rate `R_2` of Theorem 3 (Section 3).

The iteration operator `T` of eq. (7) is built from the combined field integral operators on the
obstacle boundaries; it is not constructed here. The algebraic results of Sections 5 and 6 use
only that `T` is a bounded linear operator, so `T` is a parameter of every statement.
-/

noncomputable section

namespace Arxiv1606_00062

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Eq. (10), Section 2, PDF p. 5: the multiple scattering iterations `η^0 = g`,
`η^m = T η^{m-1}`, that is `η^m = T^m g`. -/
def msIter (T : V →L[ℂ] V) (g : V) (m : ℕ) : V := (T ^ m) g

/-- Section 5, PDF p. 11: the Krylov subspace
`K_m = span {g, (I - T) g, …, (I - T)^{m-1} g}` for the operator equation (6), `(I - T) η = g`, with initial guess `μ^(0) = 0`. -/
def krylovSpace (T : V →L[ℂ] V) (g : V) (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ ((fun n : ℕ => ((1 - T) ^ n) g) '' {n | n < m})

/-- ORTHODIR step 2.4, Section 5, PDF p. 12: for directions `u = p^(i)` and `v = p^(j)`,
`β_ij = -⟨A² p^(j), A p^(i)⟩ / ⟨A p^(i), A p^(i)⟩`, where the paper's `⟨x, y⟩` is linear in `x`;
Mathlib's `inner ℂ y x` is that inner product. -/
def orthodirCoeff (A : V →L[ℂ] V) (u v : V) : ℂ :=
  -(inner ℂ (A u) (A (A v)) / inner ℂ (A u) (A u))

/-- ORTHODIR steps 1 and 2.5, Section 5, PDF p. 12: `orthodirHist A g j i = p^(i)` for `i ≤ j`,
where `p^(0) = g` and `p^(j+1) = A p^(j) + ∑_{i=0}^{j} β_ij p^(i)`. The residuals `r^(j)`, the
step sizes `α_j` and the iterates `μ^(j)` (steps 2.1-2.3) do not enter the directions. -/
def orthodirHist (A : V →L[ℂ] V) (g : V) : ℕ → ℕ → V
  | 0 => fun _ => g
  | j + 1 => fun i =>
      if i ≤ j then orthodirHist A g j i
      else A (orthodirHist A g j j) + ∑ i' ∈ Finset.range (j + 1),
        orthodirCoeff A (orthodirHist A g j i') (orthodirHist A g j j) • orthodirHist A g j i'

/-- Section 5, PDF p. 12: the ORTHODIR direction `p^(j)` for the equation `A μ = g` with
`r^(0) = p^(0) = g`. -/
def orthodirDir (A : V →L[ℂ] V) (g : V) (j : ℕ) : V := orthodirHist A g j j

/-- ORTHODIR step 2.4, Section 5, PDF p. 12: the coefficient `β_ij` computed at step `j`
from the directions `p^(i)` and `p^(j)`. -/
def orthodirBeta (A : V →L[ℂ] V) (g : V) (i j : ℕ) : ℂ :=
  orthodirCoeff A (orthodirDir A g i) (orthodirDir A g j)

end Hilbert

/-- Theorem 3, Section 3, PDF p. 7 (two-dimensional configurations): the 2-periodic rate
`R_2 = e^{2ikd} (√((1 + dκ₁)(1 + dκ₂)) [1 + √(1 - [(1 + dκ₁)(1 + dκ₂)]⁻¹)])⁻¹`, where `k` is
the wavenumber, `d` the distance between the two obstacles and `κ_j` the curvature of
`∂Ω_j` at the point `a_j` realising that distance. -/
def rateR2 (k d κ₁ κ₂ : ℝ) : ℂ :=
  Complex.exp (2 * Complex.I * k * d) *
    ((Real.sqrt ((1 + d * κ₁) * (1 + d * κ₂)) *
      (1 + Real.sqrt (1 - ((1 + d * κ₁) * (1 + d * κ₂))⁻¹)) : ℝ) : ℂ)⁻¹

end Arxiv1606_00062


