-- Prove2me | Definitions.Def_ProjFPOracle_Phi
-- name    : ProjFPOracle_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:25.692686+00:00
-- url     : https://prove2.me/theorems/7e8312f3-66ae-41ad-970a-0f32993228ca
-- title:
--   The coordinate map $\Phi_d:\mathbb X\to\mathbb R^d$ and its adjoint $\Phi_d^*$
-- statement:
--   Let $\mathbb X$ be a real inner product space and $\mathbb S\subseteq\mathbb X$ a subspace with an orthonormal basis $\varphi_1,\dots,\varphi_d$, so that $\mathbb S=\operatorname{span}\{\varphi_1,\dots,\varphi_d\}$. The **coordinate map** and its **adjoint** are
--   $$
--   \Phi_d(x):=\big(\langle x,\varphi_j\rangle\big)_{j=1}^d\in\mathbb R^d,\qquad \Phi_d^*(v):=\sum_{j=1}^d v_j\,\varphi_j\in\mathbb X .
--   $$
--   The range of $\Phi_d^*$ is $\mathbb S$, and $\Phi_d\Phi_d^*$ is the identity of $\mathbb R^d$.
--
--   These two maps translate every object of the mission between the space $\mathbb X$ and the $d$-dimensional coordinates in which the stochastic approximation algorithm runs.
--
--   **Formalization Note** The basis is an `OrthonormalBasis (Fin d) ℝ S`; the paper's index $j\in\{1,\dots,d\}$ is the `Fin d` index $j-1$, and vectors of $\mathbb R^d$ are functions `Fin d → ℝ`. The page says "orthogonal basis"; orthonormal is meant, since $\Phi_d^*$ is called the adjoint of $\Phi_d$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §2.1, p.7, Eq. (7)

import Mathlib

namespace ProjFPOracle

/-- **The coordinate map `Φ_d : 𝕏 → ℝ^d`** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, §2.1, p.7):
`Φ_d(x) := (⟨x, φ_j⟩)_{j=1}^d`, where `φ_1, …, φ_d` is an orthonormal basis of the subspace
`𝕊 = span{φ_1, …, φ_d}`.

**Formalization Note** `𝕏` is a real inner product space and `φ : OrthonormalBasis (Fin d) ℝ S`
an orthonormal basis of the subspace `S`; the index `j ∈ {1, …, d}` is the `Fin d` index `j − 1`.
Vectors of `ℝ^d` are functions `Fin d → ℝ`. The page calls the basis "orthogonal"; orthonormal is
meant (`Φ_d^*` is the adjoint of `Φ_d`). -/
noncomputable def Phi {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (x : X) : Fin d → ℝ :=
  fun j => inner ℝ ((φ j : S) : X) x

/-- **The adjoint `Φ_d^* : ℝ^d → 𝕏`** (arXiv:2012.05299v1, Eq. (7), p.7):
`Φ_d^*(v) := ∑_{j=1}^d v_j φ_j`. Its range is the subspace `𝕊`. -/
noncomputable def PhiStar {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (v : Fin d → ℝ) : X :=
  ∑ j, v j • ((φ j : S) : X)

end ProjFPOracle


