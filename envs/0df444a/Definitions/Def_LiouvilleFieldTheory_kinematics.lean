-- Prove2me | Definitions.Def_LiouvilleFieldTheory_kinematics
-- name    : LiouvilleFieldTheory_kinematics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T09:40:40.695414+00:00
-- url     : https://prove2.me/theorems/50e50bda-1d82-4c01-875f-5ec4bd179a30
-- title:
--   Liouville field theory: background charge, central charge, conformal dimension, reflection coefficient
-- statement:
--   Kinematic data of Liouville field theory as functions of the complex **coupling constant** $b$.
--
--   1. The **background charge** is $Q = b + \dfrac{1}{b}$.
--   2. The **central charge** is $c = 1 + 6Q^2$.
--   3. The **conformal dimension** of the primary field with momentum $\alpha \in \mathbb{C}$ is
--   $$\Delta(\alpha) = \alpha\,(Q - \alpha).$$
--   4. The **reflection coefficient** with normalization parameter $\lambda$ and momentum $P$ is
--   $$R_P = \pm\,\lambda^{-2iP}\,\frac{\Gamma(2ibP)\,\Gamma(2ib^{-1}P)}{\Gamma(-2ibP)\,\Gamma(-2ib^{-1}P)},$$
--   where the sign is $+1$ if $c \in (-\infty, 1)$ and $-1$ otherwise.
--
--   These are the objects in terms of which the spectrum, the reflection relation $\alpha \to Q - \alpha$ and the duality $b \to 1/b$ of Liouville theory are stated.
--
--   **Formalization Note** All quantities are complex-valued functions of $b \in \mathbb{C}$. Lean's inverse satisfies $0^{-1} = 0$, so at $b = 0$ the definitions return junk values ($Q = 0$, $c = 1$); statements that need $b \neq 0$ assume it. The power $\lambda^{-2iP}$ is the principal-branch complex power, and $\Gamma$ is Mathlib's complex Gamma function. The condition "$c \in (-\infty,1)$" is encoded as $\operatorname{Im} c = 0$ and $\operatorname{Re} c < 1$.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); sections Introduction (p. 1–2), Spectrum (p. 2), Fields and reflection relation (p. 2–3).

import Mathlib

/-!
# Liouville field theory: kinematic definitions

Source: Wikipedia, "Liouville field theory" (oldid 1376996606): sections
"Introduction", "Spectrum", "Fields and reflection relation".
-/

namespace LiouvilleFieldTheory

open Complex

/-- The background charge `Q = b + 1/b` of Liouville theory with coupling constant `b`. -/
noncomputable def backgroundCharge (b : ℂ) : ℂ := b + b⁻¹

/-- The central charge `c = 1 + 6 Q²` of Liouville theory with coupling constant `b`. -/
noncomputable def centralCharge (b : ℂ) : ℂ := 1 + 6 * backgroundCharge b ^ 2

/-- The conformal dimension `Δ = α (Q - α)` of the primary field with momentum `α`. -/
noncomputable def conformalDimension (b α : ℂ) : ℂ := α * (backgroundCharge b - α)

/-- The sign in the reflection coefficient: `+1` if `c ∈ (-∞, 1)`, and `-1` otherwise. -/
noncomputable def reflectionSign (b : ℂ) : ℂ :=
  if (centralCharge b).im = 0 ∧ (centralCharge b).re < 1 then 1 else -1

/-- The reflection coefficient
`R_P = ± λ^{-2iP} Γ(2ibP) Γ(2ib⁻¹P) / (Γ(-2ibP) Γ(-2ib⁻¹P))`,
with the sign given by `reflectionSign` and normalization parameter `λ`. -/
noncomputable def reflectionCoefficient (b lam P : ℂ) : ℂ :=
  reflectionSign b * lam ^ (-2 * I * P) *
    (Gamma (2 * I * b * P) * Gamma (2 * I * b⁻¹ * P)) /
    (Gamma (-2 * I * b * P) * Gamma (-2 * I * b⁻¹ * P))

end LiouvilleFieldTheory


