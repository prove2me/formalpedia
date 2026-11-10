-- Prove2me | Definitions.Def_BilatMatch_iron
-- name    : BilatMatch_iron
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:11:11.938695+00:00
-- url     : https://prove2.me/theorems/c4bb1c68-4872-4969-86d4-71699ccfa3c0
-- title:
--   Ironing by the greatest convex minorant; ironed rule $M^\alpha$
-- statement:
--   For a finitely supported prior with atoms $x_1<\dots<x_m$, masses $f_k$ and cumulative masses $F_k$, and a score $s$, consider the piecewise-linear curve through $(F_k,\sum_{h\le k}f_hs(x_h))$. Its **greatest convex minorant** $\Phi$ on $[0,1]$ is the pointwise largest convex function below it. The **ironed score** of $x_k$ is the slope $(\Phi(F_k)-\Phi(F_{k-1}))/f_k$. Applied to $\phi^\alpha$ and $\tau^\alpha$ this gives the ironed $\alpha$-virtual values $\bar\phi^\alpha$ and costs $\bar\tau^\alpha$; it coincides with pooling adjacent blocks with decreasing probability-weighted means.
--
--   The **ironed matching rule** $M^\alpha(\theta)$ maximizes $\sum_{(i,j)\in M}(\bar\phi^\alpha_i(v_i)-\bar\tau^\alpha_j(c_j))$ over $\mathcal F$, with the fewest edges among maximizers and remaining ties broken by a fixed order; its allocation is $1_{M^\alpha(\theta)}$.
--
--   **Formalization Note** The ironed functions are meaningful at atoms only.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.3, pp.13–14 (pdf pp.15–16), App. B.1, pp.30–31 (pdf pp.32–33)

import Mathlib
import Definitions.Def_BilatMatch_InX
import Definitions.Def_BilatMatch_canonicalMax

open MeasureTheory

namespace BilatMatch

/-!
# Ironing by the greatest convex minorant, and the ironed matching rule `M^α`

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.3, pp.13–14 (pdf pp.15–16), and App. B.1,
pp.30–31 (pdf pp.32–33).

**Formalization Note**
* For a finitely supported prior `μ` with atoms `x_1 < ⋯ < x_m`, masses `f_k` and cumulative masses
  `F_k`, and a score `s` (an `α`-virtual value or cost), `cumCurve μ s` is the piecewise-linear curve
  through `(F_k, ∑_{h ≤ k} f_h s(x_h))`, `k = 0, …, m` (for sellers with `s = τ^α` these are the points
  `(F_S(c_k), Φ_k)` of p.31, since `Φ_k − Φ_{k−1} = f_S(c_k) τ^α_S(c_k)`).
* `gcm g` is the greatest convex minorant of `g` on `[0,1]`: the pointwise supremum of the convex
  functions lying below `g` on `[0,1]` (p.31).
* The ironed score of an atom `x_k` is the slope of the minorant over `[F_{k−1}, F_k]` (p.31). For
  sellers this is the paper's definition; for buyers the paper describes ironing as pooling
  adjacent blocks with decreasing probability-weighted averages (p.13), which produces the same
  slopes. The ironed functions are meaningful at atoms only.
-/

open Classical in
/-- The piecewise-linear cumulative score curve `q ↦ ∫_0^q s(Q(u)) du` of a finitely supported
prior `μ` (with `Q` the quantile function), written as a finite sum over atoms. -/
noncomputable def cumCurve (μ : Measure ℝ) (s : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∑ᶠ x ∈ atoms μ, s x * min (μ {x}).toReal (max 0 (q - (μ (Set.Iio x)).toReal))

/-- The greatest convex minorant of `g` on `[0,1]`, evaluated at `q`. -/
noncomputable def gcm (g : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup {y | ∃ h : ℝ → ℝ, ConvexOn ℝ (Set.Icc 0 1) h ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, h u ≤ g u) ∧
    y = h q}

/-- The ironed score of the atom `x`: the slope of the greatest convex minorant of the cumulative
score curve over the mass interval `[Pr(X < x), Pr(X ≤ x)]` of `x`. -/
noncomputable def iron (μ : Measure ℝ) (s : ℝ → ℝ) (x : ℝ) : ℝ :=
  (gcm (cumCurve μ s) (μ (Set.Iic x)).toReal - gcm (cumCurve μ s) (μ (Set.Iio x)).toReal) /
    (μ {x}).toReal

/-- The ironed `α`-virtual value `ϕ̄^α` of a finitely supported buyer prior. -/
noncomputable def ironedValue (α : ℝ) (μ : Measure ℝ) : ℝ → ℝ := iron μ (alphaVirtualValue α μ)

/-- The ironed `α`-virtual cost `τ̄^α` of a finitely supported seller prior. -/
noncomputable def ironedCost (α : ℝ) (μ : Measure ℝ) : ℝ → ℝ := iron μ (alphaVirtualCost α μ)

variable {B S : Type*}

/-- The ironed matching rule `M^α(θ)` (p.14): a matching maximizing
`∑_{(i,j) ∈ M} (ϕ̄^α_i(v_i) − τ̄^α_j(c_j))` over `F`, with the fewest edges among maximizers and
remaining ties broken by `rank`. -/
noncomputable def ironedMatching (I : Market B S) (rank : Set (B × S) → ℕ) (α : ℝ)
    (θ : Profile B S) : Set (B × S) :=
  canonicalMax I rank fun M =>
    ∑ᶠ e ∈ M, (ironedValue α (I.buyerLaw e.1) (θ.1 e.1) - ironedCost α (I.sellerLaw e.2) (θ.2 e.2))

/-- The deterministic allocation of the matching rule `M^α`: `x θ = 1_{M^α(θ)}`. -/
noncomputable def ironedAlloc (I : Market B S) (rank : Set (B × S) → ℕ) (α : ℝ) :
    Allocation B S :=
  fun θ => incidence (ironedMatching I rank α θ)

end BilatMatch


