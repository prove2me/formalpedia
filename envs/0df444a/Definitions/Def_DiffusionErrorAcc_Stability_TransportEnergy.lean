-- Prove2me | Definitions.Def_DiffusionErrorAcc_Stability_TransportEnergy
-- name    : DiffusionErrorAcc_Stability_TransportEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:58:23.471087+00:00
-- url     : https://prove2.me/theorems/d3cc4234-a198-4951-94dc-d1f8e95811a5
-- title:
--   Realizing a perturbation, the transport energy T_µ(g) ∈ [0, ∞] and the f-conditioned Poincaré constant C_P(µ; f)
-- statement:
--   Let $\mu=\rho\,dx$ be a law on $\mathbb R^d$ with positive $C^1$ density. A vector field $V:\mathbb R^d\to\mathbb R^d$ **realizes perturbation of $\mu$ by $g$** (`Realizes ρ V g`) when
--   $$-\nabla\cdot(\mu V)=g\,\mu,\qquad\text{i.e.}\qquad -\nabla\cdot(\rho V)(x)=g(x)\rho(x)\ \text{ for every } x,$$
--   with the classical divergence of the field $\rho V$. This is the form written in Lemma F.1 and in the constraint of (2.3); the paper's phrase "$V$ realizes perturbation of $\mu$ by $f$" means `Realizes ρ V (f − E_µ f)`.
--
--   The **transport energy** (first expression of (2.3), the definition the paper formally adopts) is
--   $$T_\mu(g)=\inf\big\{\mathbb E_\mu\|V\|^2:\ V\in C^1,\ V\in L^2(\mu;\mathbb R^d),\ g\mu=-\nabla\cdot(\mu V)\big\}\in[0,\infty],$$
--   with $\inf\emptyset=+\infty$ (`transportEnergy`). For a test statistic $f$ with $\mathrm{Var}_\mu(f)>0$ the **f-conditioned Poincaré constant** (Definition 2.4) is
--   $$C_P(\mu;f)=\frac{T_\mu(f-\mathbb E_\mu f)}{\mathrm{Var}_\mu(f)}\in[0,\infty]$$
--   (`poincareConstF`). It may be $+\infty$ (no admissible field).
--
--   **Formalization Note.** Values in `ℝ≥0∞`; $\mathbb E_\mu\|V\|^2$ is a lower Lebesgue integral, so it is never a default value. `variance` is Mathlib's; `poincareConstF` is only used under $\mathrm{Var}_\mu(f)>0$.
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 9, (2.3) (first expression) and Definition 2.4; p. 35, Lemma F.1 (form −∇·(µV) = gµ)

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_Densities

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-! # Realizing a perturbation, the transport energy `T_µ(g)` and the f-conditioned Poincaré
constant `C_P(µ; f)` (Giapitzakis–Moitra–Risteski–Rohatgi, (2.3) and Definition 2.4, p. 9;
Lemma F.1, p. 35)

The law `µ` is `densMeasure ρ` for a positive `C¹` density `ρ`; the product `µV` is the vector
field `x ↦ ρ(x) V(x)` and `∇ · (µV)` is its classical divergence. -/

/-- `V` realizes perturbation of `µ = ρ dx` by `g`: `−∇ · (µV) = g µ`, i.e.
`−∇ · (ρ V)(x) = g(x) ρ(x)` at every `x` (the form written in Lemma F.1 and in the constraint of
(2.3)). For a centred `g = f − E_µ f` this is the paper's "V realizes perturbation (of µ) by f",
`−∇ · (µV) = (f − E_µ f) µ`. -/
def Realizes {d : ℕ} (ρ : Rd d → ℝ) (V : Rd d → Rd d) (g : Rd d → ℝ) : Prop :=
  ∀ x, -divergence (fun y => ρ y • V y) x = g x * ρ x

/-- The transport energy, first expression of (2.3), which the paper formally adopts:
`T_µ(g) = inf { E_µ ‖V‖² : V ∈ L²(µ; ℝ^d), V ∈ C¹, g µ = −∇ · (µV) }`, valued in `[0, ∞]`;
the infimum of the empty set is `+∞`. -/
noncomputable def transportEnergy {d : ℕ} (ρ : Rd d → ℝ) (g : Rd d → ℝ) : ℝ≥0∞ :=
  ⨅ (V : Rd d → Rd d) (_ : ContDiff ℝ 1 V ∧ MemLp V 2 (densMeasure ρ) ∧ Realizes ρ V g),
    ∫⁻ x, ‖V x‖ₑ ^ 2 ∂(densMeasure ρ)

/-- The f-conditioned Poincaré constant (Definition 2.4):
`C_P(µ; f) = T_µ(f − E_µ f) / Var_µ(f) ∈ [0, ∞]`. It is used only when `Var_µ(f) > 0`. -/
noncomputable def poincareConstF {d : ℕ} (ρ : Rd d → ℝ) (f : Rd d → ℝ) : ℝ≥0∞ :=
  transportEnergy ρ (fun x => f x - ∫ y, f y ∂(densMeasure ρ)) /
    ENNReal.ofReal (variance f (densMeasure ρ))

end DiffusionErrorAcc.Stability


