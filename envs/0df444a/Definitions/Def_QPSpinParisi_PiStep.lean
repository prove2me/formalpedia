-- Prove2me | Definitions.Def_QPSpinParisi_PiStep
-- name    : QPSpinParisi_PiStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:40.713563+00:00
-- url     : https://prove2.me/theorems/7e5d00e0-be9e-492f-9651-7f377ba22ec7
-- title:
--   The functional (3.13) on a step path
-- statement:
--   For a step path $\pi$,
--   $$P_{\xi,\beta}(\pi)=\mathbb E\,T_0(z_{-1})+\frac{\beta^2}2\int_0^1\{(\operatorname{Tr}\pi(u))\xi'(\operatorname{Tr}\pi(u))-\xi(\operatorname{Tr}\pi(u))\}\,du,\qquad z_{-1}\sim N(0,\beta^2\xi'(\tau_0)I_3).$$
--
--   **Formalization Note** The source writes the first term with a continuous Ruelle cascade, on all of $\Pi$. Step paths are dense in $\Pi$ and the functional is Lipschitz in $L^1$ by estimates quoted on p.21, and p.18 uses the same passage, so the infimum is unchanged. On a step path the time integral is the finite sum written in the Lean code. Used for finite mixtures only.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.13), p.15 (PDF p.15)

import Mathlib
import Definitions.Def_QPSpinParisi_stepT
import Definitions.Def_QPSpinParisi_xiS

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The functional (3.13) on a step path (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.13), p.15, PDF p.15):
`E T₀(z₋₁) + (β²/2) ∫₀¹ θ(Tr π(u)) du`, with `z₋₁ ∼ N(0, β² ξ'(τ₀) I₃)` and `θ(q) = q ξ'(q) - ξ(q)`.

**Formalization Note** The source takes the infimum over all of `Π` with a continuous Ruelle cascade. Step paths are `L¹`-dense in
`Π`, the functional is `L¹`-Lipschitz (estimates quoted on p.21), and p.18 uses the same passage, so the two infima agree. The
cascade integral on a step path is the recursion `stepT`, and `∫₀¹ θ(Tr π(u)) du` on a step path is the finite sum written here.
The functional is used for finite mixtures only, where `ξ`, `ξ'` are polynomials. -/
noncomputable def PiStep (c : ℕ → ℝ) (β : ℝ) (π : StepPath) : ℝ :=
  let τ : ℕ → ℝ := fun l => Matrix.trace (π.Q l)
  let θ : ℝ → ℝ := fun q => q * xiD c q - xiS c q
  (∫ z, stepT c β π (π.k + 1) z ∂(gaussE3 (β ^ 2 * xiD c (τ 0))))
    + (β ^ 2 / 2) * ((∑ l ∈ Finset.range (π.k + 1),
          (π.m l - (if l = 0 then 0 else π.m (l - 1))) * θ (τ l))
        + (1 - π.m π.k) * θ (τ (π.k + 1)))

end QPSpinParisi


