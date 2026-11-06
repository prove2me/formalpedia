-- Prove2me | Definitions.Def_GnpColoring_RelaxBound
-- name    : GnpColoring_RelaxBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:03.710135+00:00
-- url     : https://prove2.me/theorems/9d6cfb5e-a4ba-4013-94e0-96764e279a5e
-- title:
--   $\tau_{\mathrm{rel}}(B,\tau)\le T$ (Definition 5.2)
-- statement:
--   With $\nu=\nu_{B,\tau}$ the uniform law on proper extensions of $\tau$ to $B$, the within-block relaxation time is at most $T$ when
--
--   $$\mathrm{Var}_\nu[f]\le T\sum_{v\in B}\mathbb E_\nu\big[\mathrm{Var}_v[f]\big]\quad\text{for every }f.$$
--
--   The paper defines $\tau_{\mathrm{rel}}(B,\tau)$ as the smallest $T\ge1$ with this property (infinite if none).
--
--   **Formalization Note** The inequality is monotone in $T$, so for $X\ge1$, "$\tau_{\mathrm{rel}}(B,\tau)\le X$" is exactly this property with $T=X$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 5.2, p.43

import Mathlib
import Definitions.Def_GnpColoring_variance
import Definitions.Def_GnpColoring_condVar
import Definitions.Def_mm_transport

open scoped Classical
open Finset

namespace GnpColoring

/-- **`τ_rel(B, τ) ≤ T`** (Definition 5.2) in Poincaré form: with `ν = ν_{B,τ}`, for every `f`,
`Var_ν[f] ≤ T Σ_{v∈B} E_ν[Var_v[f]]`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 5.2, p.43: "We define τ_rel(B, τ) as the smallest constant T ≥ 1 such that
Var_{ν_{B,τ}}[f] ≤ T Σ_{v∈B} E_{ν_{B,τ}}[Var_v[f]] for every f. The value is infinite if this inequality
fails."

**Formalization Note** The inequality is monotone in `T`, so for `X ≥ 1` the paper's
`τ_rel(B, τ) ≤ X` is exactly `RelaxBound G q B x X`; every bound the mission states is `≥ 1`.
`ν` is `SpinGirth5.pin µ (V ∖ B) x`. -/
def RelaxBound {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (B : Finset (Fin n)) (x : Fin n → Fin q)
    (T : ℝ) : Prop :=
  ∀ f : (Fin n → Fin q) → ℝ,
    variance (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ B) x) f ≤
      T * ∑ v ∈ B, expect (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ B) x)
        (condVar (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ B) x) {v} f)

end GnpColoring


