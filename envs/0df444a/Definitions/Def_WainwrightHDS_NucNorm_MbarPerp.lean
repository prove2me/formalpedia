-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_MbarPerp
-- name    : WainwrightHDS_NucNorm_MbarPerp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:28:07.94985+00:00
-- url     : https://prove2.me/theorems/fa50fbf3-885d-4479-9c4f-721ff1b38979
-- title:
--   Perturbation subspace $\overline{\mathbb M}^\perp(\mathbb U,\mathbb V)$ (10.12b)
-- statement:
--   Let $\mathbb U\subseteq\mathbb R^{d_1}$ and $\mathbb V\subseteq\mathbb R^{d_2}$ be linear subspaces with orthogonal complements $\mathbb U^\perp$ and $\mathbb V^\perp$. The **perturbation subspace** is
--
--   $$
--   \overline{\mathbb M}^\perp(\mathbb U,\mathbb V) \;:=\; \{\Theta\in\mathbb R^{d_1\times d_2} \;:\; \mathrm{rowspan}(\Theta)\subseteq\mathbb V^\perp,\ \mathrm{colspan}(\Theta)\subseteq\mathbb U^\perp\}.
--   $$
--
--   Together with $\mathbb M(\mathbb U,\mathbb V)$ it forms the pair of subspaces over which the nuclear norm decomposes.
--
--   **Formalization Note** Row and column spaces are ranges of $x\mapsto\Theta^\top x$ and $z\mapsto\Theta z$; complements are taken in the Euclidean inner product. The subspaces are arbitrary.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.1, p. 317 (PDF p. 337), Eq. (10.12b)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **The perturbation subspace** `𝕄̄⊥(𝕌, 𝕍) := {Θ ∈ ℝ^{d₁×d₂} | rowspan(Θ) ⊆ 𝕍⊥, colspan(Θ) ⊆ 𝕌⊥}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.1, p. 317 (PDF p. 337), Eq. (10.12b).

`𝕌⊥`, `𝕍⊥` are the orthogonal complements (`Submodule.orthogonal`) in the Euclidean spaces
`ℝ^{d₁}`, `ℝ^{d₂}`; `colspan` and `rowspan` are the ranges of `z ↦ Θ z` and `x ↦ Θᵀ x`.

Formalization Note: `𝕌`, `𝕍` are arbitrary subspaces (see `Mspace`). -/
def MbarPerp {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) : Set (Matrix (Fin d₁) (Fin d₂) ℝ) :=
  {Θ | LinearMap.range (Matrix.toEuclideanLin Θ.transpose) ≤ Vᗮ ∧
    LinearMap.range (Matrix.toEuclideanLin Θ) ≤ Uᗮ}

end WainwrightHDS.NucNorm


