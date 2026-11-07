-- Prove2me | Definitions.Def_GaussTesting_Gb
-- name    : GaussTesting_Gb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:40.995197+00:00
-- url     : https://prove2.me/theorems/179772ec-a04f-43b4-adfb-0ed59b3d822c
-- title:
--   Pure bosonic Gaussian states $G_b$
-- statement:
--   A **bosonic Gaussian unitary** $U$ is specified by $S\in\mathrm{Sp}(2n,\mathbb R)$ and a displacement $r\in\mathbb R^{2n}$ with $Uv_iU^\dagger=r_i+\sum_{j=1}^{2n}S_{ij}v_j$. The **pure bosonic Gaussian states** $G_b$ are the orbit of the vacuum $|0^n\rangle$ under all bosonic Gaussian unitaries. Equivalently, $G_b$ is the set of unit vectors $\psi$ for which there are $S\in\mathrm{Sp}(2n,\mathbb R)$ and $r\in\mathbb R^{2n}$ with
--
--   $$
--   \sum_{k=1}^{2n}\big(S_{jk}+iS_{n+j,k}\big)\,(v_k\psi)+\big(r_j+ir_{n+j}\big)\,\psi=0\qquad(j=1,\dots,n).
--   $$
--
--   **Formalization Note** The orbit is described through the transformed annihilators. If $\psi=U|0^n\rangle$ with $Uv_iU^\dagger=r_i+\sum_jS_{ij}v_j$, then $\psi$ is annihilated by $Ua_jU^\dagger$, and since $a_j=(v_j+iv_{n+j})/\sqrt2$,
--
--   $$
--   \sqrt2\,Ua_jU^\dagger=(r_j+ir_{n+j})+\sum_{k=1}^{2n}(S_{jk}+iS_{n+j,k})\,v_k .
--   $$
--
--   Conversely every $(S,r)$ with $S$ symplectic is realized by a Gaussian unitary, and these $n$ equations determine $\psi$ up to a scalar. The equations are imposed coefficientwise. Mathlib's symplectic group (defined by $SJS^{\mathsf T}=J$ with $J=-\Omega$, blocks ordered $(q,p)$) is the paper's $\mathrm{Sp}(2n,\mathbb R)$ of (2.1). States are unit vectors and the class is closed under global phase.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2.3, p.18; eq. (2.1), p.13

import Definitions.Def_GaussTesting_quadrature
import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The pure bosonic Gaussian states `G_b` on `n` modes: the orbit of the vacuum `|0ⁿ⟩` under all
bosonic Gaussian unitaries `U` (specified by `S ∈ Sp(2n, ℝ)`, `r ∈ ℝ²ⁿ` with `U vᵢ U† = rᵢ + ∑ⱼ Sᵢⱼ vⱼ`).

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2.3, p.18 ("A bosonic Gaussian unitary `U` is specified by a matrix
`S ∈ Sp(2n, ℝ)` and a vector `r ∈ ℝ²ⁿ` such that `UvᵢU† = rᵢ + ∑²ⁿⱼ₌₁ Sᵢⱼvⱼ`"; "the set of pure Bosonic
Gaussian states can also be defined as the orbit of `|0ⁿ⟩` under all bosonic Gaussian unitaries";
"The set of bosonic Gaussian states is denoted `G_b`").

**Formalization Note.**
* Reading of "orbit of `|0ⁿ⟩`": `ψ = U|0ⁿ⟩` iff `ψ` is annihilated by the transformed annihilators
  `U aⱼ U†`, `j = 1, …, n`. From `U vᵢ U† = rᵢ + ∑ⱼ Sᵢⱼ vⱼ` (p.18) and `aⱼ = (vⱼ + i v_{n+j})/√2`,
  `√2 · U aⱼ U† = (r_j + i r_{n+j}) + ∑_k (S_{jk} + i S_{n+j,k}) v_k`, which is the left-hand side
  below. Every `(S, r)` with `S` symplectic is realized by a Gaussian unitary, and the equations
  determine `ψ` up to a scalar (the coefficient block of the `a`'s is invertible), so the unit
  solutions are exactly the orbit, up to global phase.
* The equations are imposed pointwise on the coefficient function of `ψ` (see `quadrature`).
* `Matrix.symplecticGroup (Fin n) ℝ` is defined by `S J Sᵀ = J` with `J = [[0, −I], [I, 0]] = −Ω`, on
  `Fin n ⊕ Fin n` with `Sum.inl` the `q`-block and `Sum.inr` the `p`-block. It is the paper's
  `Sp(2n, ℝ)` (`SᵀΩS = Ω`, (2.1), p.13): the group is closed under transposition and `Ω = −J`.
* `ψ` is a unit vector; the class is closed under global phase. -/
noncomputable def Gb (n : ℕ) : Set (Ell2 (Fin n → ℕ)) :=
  {ψ | ‖ψ‖ = 1 ∧ ∃ S ∈ Matrix.symplecticGroup (Fin n) ℝ, ∃ r : Fin n ⊕ Fin n → ℝ,
    ∀ (j : Fin n) (x : Fin n → ℕ),
      ∑ m, ((S (Sum.inl j) m : ℂ) + Complex.I * (S (Sum.inr j) m : ℂ)) *
          quadrature m (fun y => ψ y) x +
        ((r (Sum.inl j) : ℂ) + Complex.I * (r (Sum.inr j) : ℂ)) * ψ x = 0}

end GaussTesting


