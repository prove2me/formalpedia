-- Prove2me | Definitions.Def_ArgmaxDeFinetti_injNorm
-- name    : ArgmaxDeFinetti_injNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:55.574361+00:00
-- url     : https://prove2.me/theorems/db6b959a-3140-4a51-8a26-3d95b7e4abf3
-- title:
--   Injective tensor norm $\|z\|_\varepsilon$
-- statement:
--   For finite-dimensional Hilbert spaces $\mathcal X=\mathbb C^\iota$, $\mathcal Y=\mathbb C^\kappa$ and $z\in\mathcal X\otimes\mathcal Y$,
--   $$
--   \|z\|_\varepsilon=\sup_{\|x\|=1,\ \|y\|=1}|\langle x\otimes y,z\rangle| ,
--   $$
--   where $(x\otimes y)(i,j)=x_iy_j$.
--
--   **Formalization Note** $\mathcal X\otimes\mathcal Y$ is the coordinate space on $\iota\times\kappa$; norms are Euclidean; the supremum is a real `sSup`.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.21, eq. (2.13)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm

open Matrix

namespace ArgmaxDeFinetti

/-- The product vector `x ⊗ y ∈ X ⊗ Y`, `(x ⊗ y)(i, j) = xᵢ yⱼ`, for `X = ℂ^ι`, `Y = ℂ^κ`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.21. -/
def prodVec {ι κ : Type} (x : ι → ℂ) (y : κ → ℂ) : ι × κ → ℂ :=
  fun p => x p.1 * y p.2

/-- The injective tensor norm `∥z∥_ε = sup_{∥x∥=1, ∥y∥=1} |⟨x ⊗ y, z⟩|` of `z ∈ X ⊗ Y`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (2.13), p.21.

**Formalization Note** `X ⊗ Y` is `ι × κ → ℂ` with the standard orthonormal bases; norms are Euclidean
(`vnorm`); the supremum is a real `sSup` (bounded by Cauchy–Schwarz; `0` when `X` or `Y` is zero). -/
noncomputable def injNorm {ι κ : Type} [Fintype ι] [Fintype κ] (z : ι × κ → ℂ) : ℝ :=
  sSup {r | ∃ (x : ι → ℂ) (y : κ → ℂ), vnorm x = 1 ∧ vnorm y = 1 ∧ r = ‖vinner (prodVec x y) z‖}

end ArgmaxDeFinetti


