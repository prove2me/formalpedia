-- Prove2me | Definitions.Def_HDXConc_tilt
-- name    : HDXConc_tilt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:25.116204+00:00
-- url     : https://prove2.me/theorems/d013d184-69e0-4104-b9c8-84dd9f095252
-- title:
--   The sum $F$ and the exponentially tilted density $\pi_{d,t}$
-- statement:
--   For $f$ on the vertices and a top face $\sigma$, put $F(\sigma)=\sum_{v\in\sigma}f(v)$. For $t\in\mathbb R$, the **exponentially tilted density** induced by $F$ is
--
--   $$\pi_{d,t}(\sigma)=\frac{\pi_d(\sigma)\exp(tF(\sigma))}{\sum_{\sigma'\in X(d)}\pi_d(\sigma')\exp(tF(\sigma'))}.$$
--
--   It is again a positive probability density on $X(d)$, so it induces measures $\pi_{k,t}$ and link weights exactly as $\pi_d$ does.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Proof of Theorem 1.1, p.15

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace HDXConc

/-!
# The sum `F` and the exponentially tilted density `π_{d,t}`

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), proof of Theorem 1.1, p.15.
-/

variable {V : Type*}

/-- `F(σ) = ∑_{v ∈ σ} f(v)` (p.15). -/
def topSum (f : V → ℝ) (σ : Finset V) : ℝ := ∑ v ∈ σ, f v

/-- The exponentially tilted density of p.15,
`π_{d,t}(σ) = π_d(σ) exp(t F(σ)) / E_{π_d}[exp(t F)]`. -/
noncomputable def tilt (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) (f : V → ℝ) (t : ℝ)
    (σ : Finset V) : ℝ :=
  π σ * Real.exp (t * topSum f σ) / ∑ σ' ∈ SteurerHDX.faces X d, π σ' * Real.exp (t * topSum f σ')

end HDXConc


