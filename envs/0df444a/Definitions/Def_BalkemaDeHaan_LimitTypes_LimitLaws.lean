-- Prove2me | Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws
-- name    : BalkemaDeHaan_LimitTypes_LimitLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:02:51.5728+00:00
-- url     : https://prove2.me/theorems/426fb98f-b66c-4c6d-b138-ea06dcd1e5ef
-- title:
--   The residual-life limit laws Π, Π_γ, Γ_α, Γ_{γ,α} (p. 793) and the four-way type classification
-- statement:
--   The limit laws of the residual life time are the following distribution functions, all of which vanish for $x < 0$. For $x \ge 0$,
--   $$\Gamma_\alpha(x) = 1 - (1+x)^{-\alpha}, \qquad \Pi(x) = 1 - e^{-x},$$
--   $$\Gamma_{\gamma,\alpha}(x) = 1 - \exp\big(-\gamma\,[1 + \alpha \log(1+x)]\big), \qquad \Pi_\gamma(x) = 1 - \exp\big(-\gamma\,[1 + x]\big),$$
--   where $\alpha, \gamma > 0$ and $[a]$ is the integer part of $a$. The first two are continuous; $\Pi_\gamma$ and $\Gamma_{\gamma,\alpha}$ are discrete, with an atom of size $1 - e^{-\gamma}$ at $0$ and jumps where $1 + x$, respectively $1 + \alpha\log(1+x)$, crosses an integer.
--
--   A function $G$ is **of residual-life limit type** if it is of type $\Pi$, of type $\Pi_\gamma$ for some $\gamma > 0$, of type $\Gamma_\alpha$ for some $\alpha > 0$, or of type $\Gamma_{\gamma,\alpha}$ for some $\gamma, \alpha > 0$ (type: $G(x) = K(ax + b)$ with $a > 0$).
--
--   These four families are the possible nondegenerate weak limits of the normed residual life time (Theorem 1). $\Gamma_\alpha$ and $\Pi$ already appear under scale normalization alone; the two discrete families appear only when a shift is allowed as well.
--
--   **Formalization Note** The integer part $[\cdot]$ is `Int.floor`, cast to $\mathbb R$; its arguments $1 + x$ and $1 + \alpha\log(1+x)$ are $\ge 1$ for $x \ge 0$, and the floor is what makes $\Pi_\gamma$ and $\Gamma_{\gamma,\alpha}$ discrete. $(1+x)^{-\alpha}$ is `Real.rpow` with a base $\ge 1$, and $\log$ is applied only to $1 + x \ge 1$. Each law is defined as $0$ for $x < 0$ ("All limit distributions vanish for $x < 0$", p. 793). Theorem 1 writes the fourth family as $\Gamma_{\alpha,\gamma}$; it is the introduction's $\Gamma_{\gamma,\alpha}$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 793 (PDF 2), the limit types Γ_α, Π, Γ_{γ,α}, Π_γ

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

namespace BalkemaDeHaan.LimitTypes

/-- `Γ_α(x) = 1 - (1 + x)^{-α}` for `x ≥ 0`, and `0` for `x < 0` (p. 793, PDF 2). -/
noncomputable def GammaLaw (α : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - (1 + x) ^ (-α)

/-- `Π(x) = 1 - e^{-x}` for `x ≥ 0`, and `0` for `x < 0` (p. 793, PDF 2). -/
noncomputable def PiLaw (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-x)

/-- `Γ_{γ,α}(x) = 1 - exp(-γ [1 + α log(1 + x)])` for `x ≥ 0`, and `0` for `x < 0`, where `[·]` is
the integer part (p. 793, PDF 2). -/
noncomputable def GammaDiscreteLaw (γ α : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-γ * ((⌊1 + α * Real.log (1 + x)⌋ : ℤ) : ℝ))

/-- `Π_γ(x) = 1 - exp(-γ [1 + x])` for `x ≥ 0`, and `0` for `x < 0`, where `[·]` is the integer part
(p. 793, PDF 2). -/
noncomputable def PiDiscreteLaw (γ : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-γ * ((⌊1 + x⌋ : ℤ) : ℝ))

/-- `G` is of one of the four residual-life limit types of the introduction (p. 793):
`Π`, `Π_γ` (`γ > 0`), `Γ_α` (`α > 0`) or `Γ_{γ,α}` (`γ, α > 0`). -/
def IsResidualLimitType (G : ℝ → ℝ) : Prop :=
  IsOfType G PiLaw ∨
  (∃ γ : ℝ, 0 < γ ∧ IsOfType G (PiDiscreteLaw γ)) ∨
  (∃ α : ℝ, 0 < α ∧ IsOfType G (GammaLaw α)) ∨
  (∃ γ : ℝ, 0 < γ ∧ ∃ α : ℝ, 0 < α ∧ IsOfType G (GammaDiscreteLaw γ α))

end BalkemaDeHaan.LimitTypes


