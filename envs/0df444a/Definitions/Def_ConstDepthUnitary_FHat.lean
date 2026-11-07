-- Prove2me | Definitions.Def_ConstDepthUnitary_FHat
-- name    : ConstDepthUnitary_FHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:36.036577+00:00
-- url     : https://prove2.me/theorems/a52e9473-d731-41d1-8466-8161e60d34e0
-- title:
--   The discrete Fourier transform $\hat F$
-- statement:
--   The Fourier transform on the grid, $\hat F_1=K^{-1/2}\sum_{u,w\in[K]}e^{-i\alpha(u)\alpha(w)}|w\rangle\langle u|$ (Eq. (52)), and its $N$-fold tensor power
--   $$\hat F=K^{-N/2}\sum_{u,w\in[K]^N}e^{-i\alpha(u)^{\mathsf T}\alpha(w)}|w\rangle\langle u|\qquad\text{(Eq. (54))}.$$
--
--   **Formalization Note** The statements use the explicit formula (54).
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.4, Eqs. (52), (54), p.24

import Mathlib
import Definitions.Def_ConstDepthUnitary_alpha

namespace ConstDepthUnitary

/-- The discrete Fourier transform on the grid `Λ`, `F̂₁ = K^{−1/2} Σ_{u,w} e^{−i α(u) α(w)} |w⟩⟨u|`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Eq. (52), p.24. -/
noncomputable def F1Hat (K : ℕ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.of fun w u =>
    ((Real.sqrt K)⁻¹ : ℝ) *
      Complex.exp (-Complex.I * ((alpha K ((u : ℕ) : ℤ) * alpha K ((w : ℕ) : ℤ) : ℝ) : ℂ))

/-- The `N`-dimensional discrete Fourier transform on `Λ^N`,
`F̂ = K^{−N/2} Σ_{u,w} e^{−i α(u)ᵀα(w)} |w⟩⟨u|`, Eq. (54), p.24. -/
noncomputable def FHat (N K : ℕ) : Matrix (Fin N → Fin K) (Fin N → Fin K) ℂ :=
  Matrix.of fun w u =>
    (((K : ℝ) ^ (-(N : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((alphaVec K u ⬝ᵥ alphaVec K w : ℝ) : ℂ))

end ConstDepthUnitary


