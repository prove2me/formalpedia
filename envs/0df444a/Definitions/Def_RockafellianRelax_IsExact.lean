-- Prove2me | Definitions.Def_RockafellianRelax_IsExact
-- name    : RockafellianRelax_IsExact
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:56.935204+00:00
-- url     : https://prove2.me/theorems/a03b3c29-512d-4374-95b4-5e679f164a6b
-- title:
--   Exact Rockafellian, supported by $\bar y$ (Definition 3.1)
-- statement:
--   A Rockafellian $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ for the problem of minimizing $\varphi$ is **exact, supported by** $\bar y \in \mathbb R^m$, if its min-value function $\mathcal V(u) = \inf_x f(u,x)$ satisfies
--
--   $$
--   \mathcal V(u) \ge \mathcal V(0) + \langle \bar y, u\rangle \qquad \forall u \in \mathbb R^m .
--   $$
--
--   That is, $\bar y$ supports $\mathcal V$ at $0$ globally: perturbing the actual problem never lowers its optimal value below the affine minorant $\mathcal V(0) + \langle\bar y,\cdot\rangle$. Exactness is the paper's analogue of strong duality for the relaxation $\operatorname{minimize}_{u,x} f(u,x) - \langle\bar y, u\rangle$.
--
--   **Formalization Note** The predicate includes that $f$ is a Rockafellian for $\varphi$, as Definition 3.1 does. $\langle\bar y,u\rangle$ is the real number `ybar ⬝ᵥ u`, values in `EReal`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Definition 3.1, p.7

import Mathlib
import Definitions.Def_RockafellianRelax_IsRockafellian
import Definitions.Def_RockafellianRelax_minValue

namespace RockafellianRelax

/-- **Exact Rockafellian, supported by `ȳ`** (Definition 3.1).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Definition 3.1, p.7: "A Rockafellian f : ℝᵐ × ℝⁿ → R̄
for (3.1) is exact, supported by ȳ ∈ ℝᵐ, if 𝒱(u) ≥ 𝒱(0) + ⟨ȳ, u⟩ ∀u ∈ ℝᵐ."

**Formalization Note.** The definition bundles that `f` is a Rockafellian for `φ`
(`f(0, x) = φ(x)` for all `x`), as Definition 3.1 does ("A Rockafellian f … is exact"). `⟨ȳ, u⟩` is
the real number `ȳ ⬝ᵥ u`, so the sum `𝒱(0) + ⟨ȳ, u⟩` never meets `∞ − ∞`. -/
def IsExact {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (φ : (Fin n → ℝ) → EReal)
    (ybar : Fin m → ℝ) : Prop :=
  IsRockafellian f φ ∧
    ∀ u : Fin m → ℝ, minValue f 0 + ((ybar ⬝ᵥ u : ℝ) : EReal) ≤ minValue f u

end RockafellianRelax


