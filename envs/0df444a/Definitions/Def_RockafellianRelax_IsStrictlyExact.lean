-- Prove2me | Definitions.Def_RockafellianRelax_IsStrictlyExact
-- name    : RockafellianRelax_IsStrictlyExact
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:04.428465+00:00
-- url     : https://prove2.me/theorems/59dc1edf-eff5-4fd7-b923-35d18997f908
-- title:
--   Strictly exact Rockafellian, supported by $\bar y$ (Definition 3.1)
-- statement:
--   A Rockafellian $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ for the problem of minimizing $\varphi$ is **strictly exact, supported by** $\bar y \in \mathbb R^m$, if the exactness inequality holds strictly away from $0$:
--
--   $$
--   \mathcal V(u) > \mathcal V(0) + \langle \bar y, u\rangle \qquad \forall u \in \mathbb R^m,\ u \ne 0,
--   $$
--
--   where $\mathcal V(u) = \inf_x f(u,x)$. At $u = 0$ the inequality of Definition 3.1 is an equality, so a strictly exact Rockafellian is exact.
--
--   **Formalization Note** The predicate includes that $f$ is a Rockafellian for $\varphi$. Values in `EReal`; $\langle\bar y,u\rangle$ is `ybar ⬝ᵥ u`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Definition 3.1, p.7 (second sentence)

import Mathlib
import Definitions.Def_RockafellianRelax_IsRockafellian
import Definitions.Def_RockafellianRelax_minValue

namespace RockafellianRelax

/-- **Strictly exact Rockafellian, supported by `ȳ`** (Definition 3.1, second sentence).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Definition 3.1, p.7: "A Rockafellian f … for (3.1) is
exact, supported by ȳ ∈ ℝᵐ, if 𝒱(u) ≥ 𝒱(0) + ⟨ȳ, u⟩ ∀u ∈ ℝᵐ. If the inequality holds strictly for
all u ≠ 0, then f is strictly exact, supported by ȳ."

**Formalization Note.** Bundles that `f` is a Rockafellian for `φ`. At `u = 0` the inequality of
Definition 3.1 is the equality `𝒱(0) = 𝒱(0) + ⟨ȳ, 0⟩`, so the strict inequality for all `u ≠ 0`
already gives exactness; only `u ≠ 0` is required here. `⟨ȳ, u⟩` is the real `ȳ ⬝ᵥ u`. -/
def IsStrictlyExact {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (φ : (Fin n → ℝ) → EReal)
    (ybar : Fin m → ℝ) : Prop :=
  IsRockafellian f φ ∧
    ∀ u : Fin m → ℝ, u ≠ 0 → minValue f 0 + ((ybar ⬝ᵥ u : ℝ) : EReal) < minValue f u

end RockafellianRelax


