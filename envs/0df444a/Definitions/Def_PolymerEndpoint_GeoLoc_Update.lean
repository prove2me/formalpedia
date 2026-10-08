-- Prove2me | Definitions.Def_PolymerEndpoint_GeoLoc_Update
-- name    : PolymerEndpoint_GeoLoc_Update
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:32:04.011598+00:00
-- url     : https://prove2.me/theorems/e3d1141b-1f27-4880-a1c2-1105cfb2278b
-- title:
--   §3–§4, pp. 26–37 — the update map 𝒯, R, the fixed points 𝒦, 𝓡, the minimisers 𝓜, 𝒲 and the empirical measure μ_n
-- statement:
--   Let $(Y_u)_{u\in\mathbb N\times\mathbb Z^d}$ be i.i.d. with law $\mathfrak L$ and $f\in\mathcal S$. Write $v\sim u$ for the $2d$ nearest neighbours of $u=(n,x)$ on the same copy. Define (3.7)–(3.8)
--   $$F(u)=\frac{\sum_{v\sim u}f(v)e^{\beta Y_u}}{\widetilde F},\qquad \widetilde F=\sum_{w}\sum_{v\sim w}f(v)e^{\beta Y_w}+2d(1-\|f\|)e^{\lambda(\beta)},\qquad R(f)=\mathbf E\log\frac{\widetilde F}{2d}.$$
--   1. The **update map** $\mathcal T f\in\mathcal P(\mathcal S)$ is the law of $F$; it is lifted to $\mathcal P(\mathcal S)$ by $\mathcal T\mu(A)=\int\mathcal Tf(A)\,\mu(df)$.
--   2. $\mathcal W$ is the Wasserstein distance on $\mathcal P(\mathcal S)$ with cost $d$, and $\mathcal W(\mu,U)=\inf_{\nu\in U}\mathcal W(\mu,\nu)$.
--   3. $\mathcal K=\{\nu\in\mathcal P(\mathcal S):\mathcal T\nu=\nu\}$ (4.5), $\mathcal R(\nu)=\int R(f)\,\nu(df)$ (4.6), and $\mathcal M=\{\nu\in\mathcal K:\mathcal R(\nu)=\inf_{\mathcal K}\mathcal R\}$ (4.8).
--   4. The **empirical measure** of the endpoint distributions is $\mu_n=\frac1n\sum_{i=0}^{n-1}\delta_{f_i}$ (4.1).
--
--   $\mathcal M$ is the set of limit points of the empirical measures (Theorem 4.9); the single-copy condition (7.4) is a statement about it.
--
--   **Formalization Note.** The double sum in $\widetilde F$ is taken in $[0,\infty]$ and then converted to a real number, so that a non-summable family is not silently replaced by $0$; the sum is almost surely finite. $\mathcal Tf$ is the push-forward of the canonical environment law under $Y\mapsto F$, and $\mathcal T\mu$ is the monadic bind. $\mathcal M$ is written as the set of $\nu\in\mathcal K$ with $\mathcal R(\nu)\le\mathcal R(\nu')$ for all $\nu'\in\mathcal K$, which avoids a real infimum. $\mathcal W$ uses the published optimal-transport cost `RWPI.SqrtLasso.transportCost`.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, pp. 26–29, (3.7), (3.8), §3.2; p. 24, 𝒲; pp. 30–37, (4.1), (4.5), (4.6), (4.8)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_PolymerEndpoint_GeoLoc_Partitioned
import Definitions.Def_PolymerEndpoint_Atomic_Update

namespace PolymerEndpoint.GeoLoc

open MeasureTheory

/-- The updated partitioned subprobability measure `F(u) = ∑_{v∼u} f(v) e^{β Y_u} / PolymerEndpoint.Atomic.F̃` (3.7). -/
noncomputable def Fupd {d : ℕ} (𝔏 : Measure ℝ) (β : ℝ) (f : PolymerEndpoint.Atomic.PSM d) (Y : PolymerEndpoint.Atomic.Cell d → ℝ) : PolymerEndpoint.Atomic.PSM d :=
  toPSM (fun u => PolymerEndpoint.Atomic.nbr f Y β u / PolymerEndpoint.Atomic.Ftil 𝔏 β f Y)

/-- The fixed points `𝒦 = {ν ∈ 𝒫(𝒮) : 𝒯ν = ν}` (4.5). -/
def K (d : ℕ) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) : Set (Measure (PolymerEndpoint.Atomic.PSM d)) :=
  {ν | IsProbabilityMeasure ν ∧ PolymerEndpoint.Atomic.Tlift 𝔏 β ν = ν}

/-- The minimisers `𝓜 = {ν ∈ 𝒦 : 𝓡(ν) = inf_𝒦 𝓡}` (4.8). -/
def M (d : ℕ) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) : Set (Measure (PolymerEndpoint.Atomic.PSM d)) :=
  {ν | ν ∈ K d 𝔏 β ∧ ∀ ν' ∈ K d 𝔏 β, PolymerEndpoint.Atomic.RR 𝔏 β ν ≤ PolymerEndpoint.Atomic.RR 𝔏 β ν'}

/-- The empirical measure `μ_n = n⁻¹ ∑_{i=0}^{n-1} δ_{f_i}` (4.1). -/
noncomputable def empirical {d : ℕ} {Ω : Type*} (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ) (β : ℝ) (n : ℕ) (a : Ω) :
    Measure (PolymerEndpoint.Atomic.PSM d) :=
  (n : ENNReal)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (PolymerEndpoint.Atomic.ofPMF (PolymerEndpoint.Atomic.endpt X β i a))

end PolymerEndpoint.GeoLoc


