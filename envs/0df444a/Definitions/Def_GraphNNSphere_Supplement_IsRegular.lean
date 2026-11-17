-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_IsRegular
-- name    : GraphNNSphere_Supplement_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:05.451433+00:00
-- url     : https://prove2.me/theorems/2cd2fb67-db37-4e98-8a79-dac821afdcc6
-- title:
--   $(\kappa,K)$-regular densities and globally spread query laws
-- statement:
--   Let $d=d(n)$ be a dimension sequence, $\Delta=\lceil e^{\gamma d}\rceil$ with $\gamma>0$, $\kappa\ge0$ and $K>0$. A sequence of sampling densities $f=f_n$ is **$(\kappa,K)$-regular** if
--
--   1. $\log(1/\rho_{\min})=o(d)$, and
--   2. at every center $x$, $\operatorname{ess\,osc}_{C(x,Ke^{\gamma}\rho_f(x))}\log f\le\kappa d$.
--
--   The density then varies by at most a factor $e^{\kappa d}$ on each neighborhood $C(x,Ke^\gamma\rho_f(x))$. A sequence of query laws $Q_n$ is **globally spread** if
--
--   $$\sup_{p\in S^{d-1}}Q_n\big(C(p,\theta)\big)\longrightarrow 0\qquad\text{for every fixed }0<\theta<\pi/2 .$$
--
--   **Formalization Note** $\log(1/\rho_{\min})=o(d)$ is written $\rho_{\min}\ge e^{-\varepsilon_n d}$ with $\varepsilon_n\to0$; this is equivalent because $\rho_{\min}\le\pi$, and it excludes $\rho_{\min}=0$. Both conditions are required for all large $n$, the notion being asymptotic (for small $n$ the dimension may be $0$).
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.5, p.18; §1.3, p.5; Theorem 4.1(b), p.28

import Mathlib
import Definitions.Def_GraphNNSphere_Supplement_rhoF
import Definitions.Def_GraphNNSphere_Supplement_essOscLog

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

/-- A sequence of sampling densities `f = (f_n)` on `S^{d(n)-1}` is `(κ, K)`-regular for the degree
`Δ = ⌈e^{γd}⌉` if `log(1/ρ_min) = o(d)` and, at every center `x`, the essential oscillation of
`log f` on `C(x, K e^γ ρ_f(x))` is at most `κd` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.5, p.18).

**Formalization Note** `log(1/ρ_min) = o(d)` is written `ρ_min ≥ e^{-ε_n d}` for a sequence
`ε_n → 0`, which is equivalent because `ρ_min ≤ π`, and which excludes `ρ_min = 0` (where
`Real.log (1/0) = 0` would be a junk value). Both conditions are required for all large `n`: the
notion is asymptotic, and for small `n` the dimension may be `0`, where no density exists. -/
def IsRegular (d : ℕ → ℕ) (f : ∀ n, Sph (d n) → ℝ) (γ κ K : ℝ) : Prop :=
  (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, Real.exp (-(ε n * (d n : ℝ))) ≤ rhoMin n (d n) (f n)) ∧
    ∀ᶠ n in atTop, ∀ x : Sph (d n),
      essOscLog (d n) (f n) (cap x (K * Real.exp γ * rhoF n (d n) (f n) x)) ≤
        ((κ * (d n : ℝ) : ℝ) : EReal)

/-- A sequence of query laws `Q_n` is globally spread if
`sup_{p ∈ S^{d-1}} Q_n(C(p, θ)) → 0` for every fixed `0 < θ < π/2`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.5, and Theorem 4.1(b), p.28). -/
def IsGloballySpread (d : ℕ → ℕ) (Q : ∀ n, Measure (Sph (d n))) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
    Tendsto (fun n => ⨆ p : Sph (d n), Q n (cap p θ)) atTop (𝓝 0)

end Supplement

end GraphNNSphere


