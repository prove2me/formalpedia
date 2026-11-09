-- Prove2me | Definitions.Def_GevreyGibbsSep_IsBump
-- name    : GevreyGibbsSep_IsBump
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:20.465687+00:00
-- url     : https://prove2.me/theorems/2d1cefa1-d7a2-4679-b7b7-447602c68391
-- title:
--   Definition B.4 — bump distribution on a patch
-- statement:
--   Let $\Omega_0\subset\mathbb T^d$ be closed with $v_0=\mathrm{vol}(\Omega_0)\in(0,(2\pi)^d)$. A **bump** on the patch $\Omega_0$ with concentration $\delta\in(0,1)$ and background $\kappa>0$ is a probability distribution $p$ with
--   $$p(\Omega_0)=\delta>\frac{v_0}{(2\pi)^d}\qquad\text{and}\qquad p(x)=\kappa\ \text{ for every }x\notin\Omega_0 .$$
--   Necessarily $\kappa=(1-\delta)/((2\pi)^d-v_0)$. Bumps are the hard instances of the lower bound: off the patch the landscape is flat.
--
--   **Formalization Note** The distribution is the Gibbs state of a potential $V$, and "density $\kappa$ off $\Omega_0$" is stated on the periodic lift: $e^{-V(x)}/Z_V=\kappa$ whenever the class of $x$ is not in $\Omega_0$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.4, p.35; Eq. (25), p.11

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_toTorus
import Definitions.Def_GevreyGibbsSep_partitionFn
import Definitions.Def_GevreyGibbsSep_gibbs

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition B.4 (bump distribution), arXiv:2608.24527 (sha256 d4fd40eb…), p.35, with (25),
p.11: the Gibbs state of `V` is a bump on the closed patch `Ω₀ ⊆ T^d`, with `vol(Ω₀) ∈ (0, (2π)^d)`,
concentration `δ ∈ (0, 1)` and background `κ > 0`: a probability distribution with
`p(Ω₀) = δ > vol(Ω₀)/(2π)^d` and density `κ` at every point outside `Ω₀`.

**Formalization Note** "Density `κ` outside `Ω₀`" is stated on the periodic lift:
`e^{−V(x)}/Z_V = κ` for every `x ∈ ℝ^d` whose class is not in `Ω₀`. -/
def IsBump {d : ℕ} (V : (Fin d → ℝ) → ℝ) (Ω₀ : Set (Torus d)) (δ κ : ℝ) : Prop :=
  IsClosed Ω₀ ∧ 0 < volume Ω₀ ∧ volume Ω₀ < ENNReal.ofReal ((2 * Real.pi) ^ d) ∧
  0 < δ ∧ δ < 1 ∧ 0 < κ ∧ IsProbabilityMeasure (gibbs V) ∧
  (gibbs V Ω₀).toReal = δ ∧ (volume Ω₀).toReal / (2 * Real.pi) ^ d < δ ∧
  ∀ x : Fin d → ℝ, toTorus x ∉ Ω₀ → Real.exp (- V x) / partitionFn V = κ

end GevreyGibbsSep


