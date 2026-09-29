-- Prove2me | Definitions.Def_MetodosNumericos_ajusteDefs
-- name    : MetodosNumericos_ajusteDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:34:22.426786+00:00
-- url     : https://prove2.me/theorems/ceca63ac-19d2-4d2b-b635-92075586e145
-- title:
--   Least-squares functional, normal system and Gram matrix
-- statement:
--   The sum of squared residuals $S(c) = \\sum_i (\\sum_k c_k\\varphi_k(x_i) - f_i)^2$, the normal system of $n+1$ equations $\\sum_i \\varphi_k(x_i)(\\sum_j c_j\\varphi_j(x_i)) = \\sum_i \\varphi_k(x_i)f_i$, and the Gram matrix $a_{kj} = \\sum_i \\varphi_k(x_i)\\varphi_j(x_i)$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 6, §6.2–6.3, pp. 121–124.

import Mathlib

namespace MetodosNumericos

/-- The least-squares functional of the MMQ (Método dos Mínimos Quadrados):
for data `(xᵢ, fᵢ)`, `i = 0, …, m`, a family of base functions `φ₀, …, φₙ` and
coefficients `c₀, …, cₙ`,
`S(c) = ∑ᵢ (c₀φ₀(xᵢ) + ⋯ + cₙφₙ(xᵢ) - fᵢ)²`. -/
noncomputable def sqError {m n : ℕ} (phi : Fin (n + 1) → ℝ → ℝ)
    (x f : Fin (m + 1) → ℝ) (c : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (m + 1), (∑ k : Fin (n + 1), c k * phi k (x i) - f i) ^ 2

/-- The normal system (sistema normal) of the MMQ: the `n + 1` equations
`∑ᵢ φₖ(xᵢ)(c₀φ₀(xᵢ) + ⋯ + cₙφₙ(xᵢ)) = ∑ᵢ φₖ(xᵢ) fᵢ`, `k = 0, …, n`. -/
def NormalSystem {m n : ℕ} (phi : Fin (n + 1) → ℝ → ℝ)
    (x f : Fin (m + 1) → ℝ) (c : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin (n + 1),
    ∑ i : Fin (m + 1), phi k (x i) * (∑ j : Fin (n + 1), c j * phi j (x i)) =
      ∑ i : Fin (m + 1), phi k (x i) * f i

/-- The Gram matrix `A = (a_{kj})` of the normal system, `a_{kj} = ∑ᵢ φₖ(xᵢ) φⱼ(xᵢ)`. -/
noncomputable def gramMatrix {m n : ℕ} (phi : Fin (n + 1) → ℝ → ℝ) (x : Fin (m + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j => ∑ i : Fin (m + 1), phi k (x i) * phi j (x i)

end MetodosNumericos


