-- Prove2me | Definitions.Def_GnpColoring_PortCovBound
-- name    : GnpColoring_PortCovBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:00.906344+00:00
-- url     : https://prove2.me/theorems/92f155ba-e481-43ed-aa3f-9fe40bf1924e
-- title:
--   $\lambda_{\max}(\Lambda_{B,\tau})\le\lambda$ (Definition 3.13)
-- statement:
--   Let $B$ be a block and $\tau$ a colouring of $V\setminus B$; let $\nu=\nu_{B,\tau}$ be the uniform law of proper colourings agreeing with $\tau$ off $B$. The block covariance operator $\Lambda_{B,\tau}$ has largest eigenvalue at most $\lambda$ when, for every family of functions $g_\rho:[q]\to\mathbb R$ indexed by the ports $\rho\in P_B$,
--
--   $$\mathrm{Var}_\nu\Big(\sum_{\rho\in P_B}g_\rho(\sigma_\rho)\Big)\le\lambda\sum_{\rho\in P_B}\mathrm{Var}_\nu\big(g_\rho(\sigma_\rho)\big).$$
--
--   It measures approximate independence of the port colours.
--
--   **Formalization Note** The quadratic form of $\Lambda_{B,\tau}$ at a centred family is the left side and its squared norm the sum on the right; variance is shift invariant, so the family need not be centred. The law $\nu$ is a probability measure only for feasible $\tau$, the only case used.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.13, p.22; proof of Lemma 3.24, p.30

import Mathlib
import Definitions.Def_GnpColoring_ports
import Definitions.Def_GnpColoring_variance
import Definitions.Def_mm_transport
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **`λ_max(Λ_{B,τ}) ≤ λ`** for the block covariance operator (Definition 3.13), in variance
form: with `ν = ν_{B,τ}` the uniform law of proper colourings agreeing with `τ` off `B`, for every
family `g_ρ : [q] → ℝ` (`ρ ∈ P_B`),
`Var_ν(Σ_ρ g_ρ(σ_ρ)) ≤ λ Σ_ρ Var_ν(g_ρ(σ_ρ))`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.13, p.22: "⟨f, Λ_{B,τ} f⟩_{H_{B,τ}} = Σ_{(ρ1,ρ2)} E_{ν_τ}[f_{ρ1}(σ_{ρ1}) f_{ρ2}(σ_{ρ2})]
where f is a vector of |P_B| centered functions that only depend on the spin at a single port
each"; the first display of the proof of Lemma 3.24, p.30.

**Formalization Note** The quadratic form of `Λ_{B,τ}` at a centred family is
`Var_ν(Σ_ρ g_ρ(σ_ρ))` and the squared norm is `Σ_ρ Var_ν(g_ρ(σ_ρ))`; variance is shift invariant,
so centring is not needed. `ν` is `SpinGirth5.pin µ (V ∖ B) x`; it is a law only for feasible
`x`, which is how every statement uses it. -/
def PortCovBound {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (B : Finset (Fin n)) (x : Fin n → Fin q)
    (lam : ℝ) : Prop :=
  ∀ g : Fin n → Fin q → ℝ,
    variance (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ B) x)
        (fun σ => ∑ ρ ∈ ports G B, g ρ (σ ρ)) ≤
      lam * ∑ ρ ∈ ports G B,
        variance (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ B) x)
          (fun σ => g ρ (σ ρ))

end GnpColoring


