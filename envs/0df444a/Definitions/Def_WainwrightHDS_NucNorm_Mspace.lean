-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_Mspace
-- name    : WainwrightHDS_NucNorm_Mspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:27:50.32104+00:00
-- url     : https://prove2.me/theorems/270e7ece-e3da-455f-94ed-27915d257bdf
-- title:
--   Model subspace $\mathbb M(\mathbb U,\mathbb V)$ (10.12a)
-- statement:
--   Let $\mathbb U\subseteq\mathbb R^{d_1}$ and $\mathbb V\subseteq\mathbb R^{d_2}$ be linear subspaces. For $\Theta\in\mathbb R^{d_1\times d_2}$ write $\mathrm{colspan}(\Theta)\subseteq\mathbb R^{d_1}$ and $\mathrm{rowspan}(\Theta)\subseteq\mathbb R^{d_2}$ for its column and row spaces. The **model subspace** is
--
--   $$
--   \mathbb M(\mathbb U,\mathbb V) \;:=\; \{\Theta\in\mathbb R^{d_1\times d_2} \;:\; \mathrm{rowspan}(\Theta)\subseteq\mathbb V,\ \mathrm{colspan}(\Theta)\subseteq\mathbb U\}.
--   $$
--
--   When $\mathbb U,\mathbb V$ are spanned by the top $r$ left and right singular vectors of a target matrix, $\mathbb M$ consists of matrices of rank at most $r$ aligned with that target.
--
--   **Formalization Note** $\mathrm{colspan}(\Theta)$ is the range of $z\mapsto\Theta z$ and $\mathrm{rowspan}(\Theta)$ the range of $x\mapsto\Theta^\top x$. The subspaces are arbitrary; the book's "$r$-dimensional" is imposed by the theorems that need it.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.1, p. 317 (PDF p. 337), Eq. (10.12a)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **The model subspace** `𝕄(𝕌, 𝕍) := {Θ ∈ ℝ^{d₁×d₂} | rowspan(Θ) ⊆ 𝕍, colspan(Θ) ⊆ 𝕌}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.1, p. 317 (PDF p. 337), Eq. (10.12a).

`colspan Θ ⊆ ℝ^{d₁}` is the range of `z ↦ Θ z`, and `rowspan Θ ⊆ ℝ^{d₂}` is the range of
`x ↦ Θᵀ x`.

Formalization Note: `𝕌` and `𝕍` are arbitrary subspaces of `EuclideanSpace ℝ (Fin d₁)` and
`EuclideanSpace ℝ (Fin d₂)`; the book's choice of `r`-dimensional subspaces is imposed by the
theorems that need it. The set is returned as a `Set` (it is a linear subspace). -/
def Mspace {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) : Set (Matrix (Fin d₁) (Fin d₂) ℝ) :=
  {Θ | LinearMap.range (Matrix.toEuclideanLin Θ.transpose) ≤ V ∧
    LinearMap.range (Matrix.toEuclideanLin Θ) ≤ U}

end WainwrightHDS.NucNorm


