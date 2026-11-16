-- Prove2me | Definitions.Def_GaussPart_Supplement_SurfaceArea
-- name    : GaussPart_Supplement_SurfaceArea
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:00:57.672578+00:00
-- url     : https://prove2.me/theorems/ad8b295d-2478-42c8-bac6-4f4ad611cdfc
-- title:
--   Gaussian surface area $\Gamma(A)$, $\Gamma(f)$, $\Gamma(\mathcal F)$
-- statement:
--   For a Borel set $A\subseteq\mathbb R^d$ and $t>0$ let $A_t=\{x:\operatorname{dist}(x,A)\le t\}$. The **Gaussian surface area** of $A$ is
--   $$
--   \Gamma(A)=\liminf_{t\downarrow 0}\frac{\Pr_{x\sim\mathcal N(0,I_d)}[x\in A_t\setminus A]}{t}\in[0,\infty].
--   $$
--   For a Boolean function $f$ with level sets $A_b=\{x:f(x)=b\}$, $\Gamma(f)=\Gamma(A_{-1})+\Gamma(A_{+1})$, and for a class, $\Gamma(\mathcal F)=\sup_{f\in\mathcal F}\Gamma(f)$.
--
--   The surface area controls the error made by freezing the constrained coordinates of a thin cell; finiteness of $\Gamma(\mathcal F)$ is item (3) of Definition 4.1 and a hypothesis of Theorems 5.3 and 6.2.
--
--   **Formalization Note** $A_t$ is Mathlib's closed thickening; all values are in $[0,\infty]$, so $\Gamma(\mathcal F)<\infty$ is a genuine hypothesis and no junk value occurs.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition A.1, p.69 (PDF p.71)

import Mathlib
import Definitions.Def_GaussPart_Cell

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussPart

namespace Supplement

/-- **Definition A.1** (Gaussian surface area), arXiv:2611.05264 (sha256 7e0ca6d4…), p.69 (PDF p.71):
for a Borel set `A ⊆ ℝᵈ` and `t > 0`, `A_t := {x : dist(x, A) ≤ t}`, and
`Γ(A) := liminf_{t↓0} Pr_{x∼N(0,I_d)}[x ∈ A_t \ A] / t`.

**Formalization Note.** `A_t` is `Metric.cthickening t A` (infimum of extended distances `≤ t`, so
`A_t = ∅` for `A = ∅`). The value is in `[0, ∞]`, and the limit inferior is over `t → 0⁺`. -/
noncomputable def surfArea {d : ℕ} (A : Set (Vec d)) : ENNReal :=
  liminf (fun t : ℝ => stdGaussian (Vec d) (Metric.cthickening t A \ A) / ENNReal.ofReal t)
    (𝓝[>] 0)

/-- `Γ(f) := Γ(A₋₁) + Γ(A₊₁)` with `A_b := {x : f(x) = b}` (Definition A.1). -/
noncomputable def gsa {d : ℕ} (f : Vec d → ℝ) : ENNReal :=
  surfArea {x | f x = -1} + surfArea {x | f x = 1}

/-- `Γ(F) := sup_{f ∈ F} Γ(f)` (Definition A.1), in `[0, ∞]`. -/
noncomputable def gsaClass {d : ℕ} (F : Set (Vec d → ℝ)) : ENNReal :=
  ⨆ f ∈ F, gsa f

end Supplement

end GaussPart


