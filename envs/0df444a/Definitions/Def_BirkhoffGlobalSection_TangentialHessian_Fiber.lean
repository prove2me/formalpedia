-- Prove2me | Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
-- name    : BirkhoffGlobalSection_TangentialHessian_Fiber
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-29T22:33:30.319088+00:00
-- url     : https://prove2.me/theorems/3645e8d0-e21c-4a9d-81e8-9cf5b8082c08
-- title:
--   Fiber data of the Levi-Civita Hamiltonian: fiber radius, block Hessian and gate coefficients
-- statement:
--   Let $K_{\mu,c}(s) = P_{\mu,c}(s) - \mu Z/r$ be the Levi-Civita regularized Hamiltonian of the planar circular restricted three-body problem. Here $s = (z_1, z_2, w_1, w_2)$, $Z = |z|^2$, and $r > 0$ is treated as a free parameter; on the regular domain it is $r = |2z^2 - 1|$. Put
--   $$b(z) = \bigl(-(2Z + \mu)\,z_2,\; (2Z - \mu)\,z_1\bigr), \qquad u = w + b(z).$$
--   Then $K = \tfrac12 |u|^2 - \tfrac12 F$, so the energy fiber over $z$ is the circle $|u|^2 = F$. This module defines the data of that circle and of the bordered form of $\operatorname{Hess} K$ restricted to it.
--
--   - **$F$** (`fibF`) is the squared fiber radius:
--   $$F = 1 - \mu - 2cZ + (2Z-\mu)^2 z_1^2 + (2Z+\mu)^2 z_2^2 + \frac{2\mu Z}{r}.$$
--   - **$L_0 = -\tfrac12 \operatorname{Hess}_z F$** (`fibL00`, `fibL01`, `fibL11`) and **$v = -\tfrac12 \nabla_z F$** (`fibV0`, `fibV1`) are each written as an explicit polynomial minus the $\mu/r$ part of the Hessian of $K$ (`kBr`), in the same form as the Hessian `kHessR`.
--   - **The gate data on the fiber circle.** Put $M_1 = \operatorname{Hess} b_1$ and $M_2 = \operatorname{Hess} b_2$. Then
--   $$G = F \det L_0 + v^{\mathsf T} \operatorname{adj}(L_0)\, v - 16 F^2 Z, \qquad \beta_k = F \operatorname{tr}\bigl(\operatorname{adj}(L_0) M_k\bigr) + v^{\mathsf T} \operatorname{adj}(M_k)\, v .$$
--   $G$ is the constant term minus the second-harmonic amplitude of the bordered form $\nabla K^{\mathsf T} \operatorname{adj}(\operatorname{Hess} K) \nabla K$ on the circle $|u|^2 = F$ (`fibG`), and $(\beta_1, \beta_2)$ are its first-harmonic coefficients (`fibBeta1`, `fibBeta2`).
--
--   These are the quantities of Grisa's exact fiber elimination: his gate $\mathcal D$ is $4\times$ our bordered form, and his $F$ is ours. Positivity of the tangential-Hessian determinant (Joung–van Koert, Proposition 4.4) reduces to $G > 0$ and $F\,(\beta_1^2 + \beta_2^2) < G^2$.
-- source:
--   Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Lemmas 3.4–3.5, Theorem 3.7(b); Grisa, companion paper, Zenodo 21376299 (2026), §5 (block-diagonal Hessian); applied to Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

/-!
# The fiber data of the Levi-Civita Hamiltonian (structural reduction of the tangential-Hessian gate)

On the fiber over `z`, the Levi-Civita Hamiltonian is `K = |u|²/2 - F/2` with `u = w + b(z)`; its Hessian
factors as `Jᵀ diag(L, I) J` with `L = L₀ + u₁ M₁ + u₂ M₂`. This module defines `F` (`fibF`), `L₀ = -½ Hess F`
(`fibL00/01/11`), `v = -½ ∇F` (`fibV0/1`), the `μ / r` part `kBr` of `kHessR`, and the `φ`-free gate data
`fibG` (constant term minus second-harmonic amplitude) and `fibBeta1/2` (first-harmonic coefficients) of the
bordered form on the fiber circle.

Reference: Grisa, *Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted
three-body problem*, Zenodo 21270420 (2026), Lemmas 3.4–3.5 and Theorem 3.7(b) (his gate is `4 ×` ours, his `F`
is `fibF`); companion Zenodo 21376299, §5 (block-diagonal Hessian).
-/

namespace BirkhoffGlobalSection.TangentialHessian

open BirkhoffGlobalSection

noncomputable section

/-- The `μ / r` part of `kHessR` (so `kHessR = hP - kBr`). -/
def kBr (μ r : ℝ) (s : Phase) (i j : Fin 4) : ℝ :=
  μ * (hZ i j / r - (dZ s i * dD s j + dZ s j * dD s i) / (2 * r ^ 3)
    - zNormSq s * hD s i j / (2 * r ^ 3) + 3 * zNormSq s * dD s i * dD s j / (4 * r ^ 5))

/-- The squared fiber radius `F = R²` (the fiber over `z` is the circle `|w + b(z)|² = F`). -/
def fibF (μ c r : ℝ) (s : Phase) : ℝ :=
  1 - μ - 2 * c * zNormSq s + (2 * zNormSq s - μ) ^ 2 * s 0 ^ 2 + (2 * zNormSq s + μ) ^ 2 * s 1 ^ 2
    + 2 * μ * zNormSq s / r

/-- `L₀ = -½ Hess F` (entries `00`, `01`, `11`). -/
def fibL00 (μ c r : ℝ) (s : Phase) : ℝ :=
  2 * c - μ ^ 2 + 24 * μ * s 0 ^ 2 - 60 * s 0 ^ 4 - 72 * s 0 ^ 2 * s 1 ^ 2 - 12 * s 1 ^ 4 - kBr μ r s 0 0
def fibL01 (μ r : ℝ) (s : Phase) : ℝ :=
  -48 * s 0 * s 1 * (s 0 ^ 2 + s 1 ^ 2) - kBr μ r s 0 1
def fibL11 (μ c r : ℝ) (s : Phase) : ℝ :=
  2 * c - μ ^ 2 - 24 * μ * s 1 ^ 2 - 12 * s 0 ^ 4 - 72 * s 0 ^ 2 * s 1 ^ 2 - 60 * s 1 ^ 4 - kBr μ r s 1 1

/-- `v = -½ ∇F`. -/
def fibV0 (μ c r : ℝ) (s : Phase) : ℝ :=
  s 0 * (2 * c - μ ^ 2 + 8 * μ * s 0 ^ 2 - 12 * zNormSq s ^ 2)
    - μ * (dZ s 0 / r - zNormSq s * dD s 0 / (2 * r ^ 3))
def fibV1 (μ c r : ℝ) (s : Phase) : ℝ :=
  s 1 * (2 * c - μ ^ 2 - 8 * μ * s 1 ^ 2 - 12 * zNormSq s ^ 2)
    - μ * (dZ s 1 / r - zNormSq s * dD s 1 / (2 * r ^ 3))

/-- Constant term minus second-harmonic amplitude: `G = F det L₀ + vᵀ adj(L₀) v - 16 F² Z`. -/
def fibG (μ c r : ℝ) (s : Phase) : ℝ :=
  fibF μ c r s * (fibL00 μ c r s * fibL11 μ c r s - fibL01 μ r s ^ 2)
    + (fibL11 μ c r s * fibV0 μ c r s ^ 2 - 2 * fibL01 μ r s * fibV0 μ c r s * fibV1 μ c r s
      + fibL00 μ c r s * fibV1 μ c r s ^ 2)
    - 16 * fibF μ c r s ^ 2 * zNormSq s

/-- First-harmonic coefficients `βₖ = F tr(adj(L₀) Mₖ) + vᵀ adj(Mₖ) v`. -/
def fibBeta1 (μ c r : ℝ) (s : Phase) : ℝ :=
  fibF μ c r s * (fibL11 μ c r s * (-4 * s 1) - 2 * fibL01 μ r s * (-4 * s 0)
      + fibL00 μ c r s * (-12 * s 1))
    + ((-12 * s 1) * fibV0 μ c r s ^ 2 - 2 * (-4 * s 0) * fibV0 μ c r s * fibV1 μ c r s
      + (-4 * s 1) * fibV1 μ c r s ^ 2)
def fibBeta2 (μ c r : ℝ) (s : Phase) : ℝ :=
  fibF μ c r s * (fibL11 μ c r s * (12 * s 0) - 2 * fibL01 μ r s * (4 * s 1)
      + fibL00 μ c r s * (4 * s 0))
    + ((4 * s 0) * fibV0 μ c r s ^ 2 - 2 * (4 * s 1) * fibV0 μ c r s * fibV1 μ c r s
      + (12 * s 0) * fibV1 μ c r s ^ 2)

end

end BirkhoffGlobalSection.TangentialHessian


