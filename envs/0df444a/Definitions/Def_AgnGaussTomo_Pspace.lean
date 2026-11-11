-- Prove2me | Definitions.Def_AgnGaussTomo_Pspace
-- name    : AgnGaussTomo_Pspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:38.204237+00:00
-- url     : https://prove2.me/theorems/acd6ee11-ff2c-4051-9464-8d8c01bcb59a
-- title:
--   Bargmann parameter space $\mathcal P_n$ with $\|(b,A)\|_{\mathcal P}^2=\|b\|_2^2+\tfrac12\|A\|_F^2$
-- statement:
--   The **Bargmann parameter space** is
--
--   $$
--   \mathcal P_n=\{(b,A): b\in\mathbb C^n,\ A\in\mathbb C^{n\times n},\ A=A^\top\},
--   $$
--
--   viewed as a real Hilbert space of dimension $n^2+3n$ with inner product $\langle(b,A),(b',A')\rangle_{\mathcal P}=\operatorname{Re}\big(\langle b,b'\rangle+\tfrac12\operatorname{tr}(A^*A')\big)$, so that $\|(b,A)\|_{\mathcal P}^2=\|b\|_2^2+\tfrac12\|A\|_F^2$ (Eq. (12)).
--
--   A point $\theta$ is a real vector with coordinates $\operatorname{Re}b_i,\operatorname{Im}b_i$ and, for $i\le j$, the real and imaginary parts of $A_{ij}$, where the diagonal entries are stored divided by $\sqrt2$. With this scaling the Euclidean inner product of the coordinates is exactly $\langle\cdot,\cdot\rangle_{\mathcal P}$, so gradients, Hessians and balls are those of the paper.
--
--   **Formalization Note** `Pspace n = EuclideanSpace ℝ (PIdx n)`; `Pspace.b`, `Pspace.A` read off $b$ and $A$ ($A_{ii}=\sqrt2(\theta_{ii,0}+i\theta_{ii,1})$, $A_{ij}=A_{ji}=\theta_{ij,0}+i\theta_{ij,1}$ for $i<j$). The one-mode identity $\|\theta\|^2=|b|^2+\tfrac12|A_{11}|^2$ is checked in the verification file.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Fact 2.4, printed p. 11 (PDF p. 14); Eq. (12), p. 12 (PDF p. 15)

import Mathlib

namespace AgnGaussTomo

/-- Real coordinates of the Bargmann parameter space: `inl (i, c)` is the real (`c = 0`) or
imaginary (`c = 1`) part of `b_i`; `inr ((i, j), c)` with `i ≤ j` the real or imaginary part of
the (rescaled) entry `A_ij = A_ji`. -/
abbrev PIdx (n : ℕ) := (Fin n × Fin 2) ⊕ ({p : Fin n × Fin n // p.1 ≤ p.2} × Fin 2)

/-- **The Bargmann parameter space `P_n` as a real Hilbert space.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Fact 2.4,
printed p. 11 (PDF p. 14): "θ = (b, A) ∈ P_n = {(b, A) : b ∈ ℂⁿ, A ∈ ℂ^{n×n}, A = Aᵀ}"; and p. 12,
Eq. (12): "We will view P_n as a real Hilbert space with dimension n²+3n equipped with the inner
product ⟨(b, A), (b′, A′)⟩_{P_n} = Re(⟨b, b′⟩ + ½ tr(A*A′)) … such that ‖(b, A)‖²_P = ‖b‖²₂ + ½‖A‖²_F".

`Pspace n` is the Euclidean space on `2n + n(n+1) = n² + 3n` real coordinates; a point `θ` encodes
`(b, A)` through `Pspace.b θ` and `Pspace.A θ`.

**Formalization Note.** The diagonal entries of `A` are stored scaled by `1/√2` (see `Pspace.A`),
so that the Euclidean inner product and norm of `Pspace n` **are** the paper's `⟨·,·⟩_{P_n}` and
`‖·‖_P`: `‖θ‖² = ‖b‖²₂ + ½‖A‖²_F`. Hence Mathlib's `gradient`, `fderiv`, `iteratedFDeriv`,
operator norms and balls on `Pspace n` are the paper's. -/
abbrev Pspace (n : ℕ) := EuclideanSpace ℝ (PIdx n)

/-- The linear Bargmann parameter `b ∈ ℂⁿ` of `θ ∈ P_n` (Fact 2.4, p. 11):
`b_i = θ_{inl(i,0)} + i θ_{inl(i,1)}`. -/
noncomputable def Pspace.b {n : ℕ} (θ : Pspace n) : Fin n → ℂ :=
  fun i => (θ (Sum.inl (i, 0)) : ℂ) + (θ (Sum.inl (i, 1)) : ℂ) * Complex.I

/-- The quadratic Bargmann parameter `A ∈ ℂ^{n×n}`, `A = Aᵀ`, of `θ ∈ P_n` (Fact 2.4, p. 11):
with `(k, l) = (min i j, max i j)`, `A_ij = c_ij (θ_{inr((k,l),0)} + i θ_{inr((k,l),1)})`, where
`c_ij = 1` for `i ≠ j` and `c_ii = √2`; then `A` is symmetric and `½‖A‖²_F` is the sum of the
squares of the `inr` coordinates. -/
noncomputable def Pspace.A {n : ℕ} (θ : Pspace n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    ((if i = j then Real.sqrt 2 else 1 : ℝ) : ℂ) *
      ((θ (Sum.inr (⟨(min i j, max i j), min_le_max⟩, 0)) : ℂ) +
        (θ (Sum.inr (⟨(min i j, max i j), min_le_max⟩, 1)) : ℂ) * Complex.I)

end AgnGaussTomo


