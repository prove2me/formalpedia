-- Prove2me | Definitions.Def_BERicci_Contract_Dual
-- name    : BERicci_Contract_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:59.462989+00:00
-- url     : https://prove2.me/theorems/065fd227-dca9-4af0-9aa1-41fe56307da4
-- title:
--   Proposition 3.2 (i)–(ii), p. 27 — the dual semigroup H_t on probability measures and the pointwise version P̃_t
-- statement:
--   Let $(X,\mathsf d)$ be a metric space with its Borel σ-algebra, $m$ a Borel measure and $(\mathsf P_t)_{t\ge0}$ a semigroup acting on $L^2(X,m)$. A family $(\mathsf H_t)_{t\ge0}$ of maps on measures is called the **dual semigroup** of $(\mathsf P_t)$ when, for every $t\ge0$:
--
--   1. $\mathsf H_t$ maps Borel probability measures to Borel probability measures;
--   2. for every probability density $f\in L^1\cap L^2(X,m)$, $f\ge0$, $\int f\,dm=1$,
--   $$\mathsf H_t(f\,m)=(\mathsf P_tf)\,m;$$
--   3. $\mathsf H_t$ is continuous for the weak convergence of probability measures: if $\int g\,d\mu_n\to\int g\,d\mu$ for every bounded continuous $g$, then $\int g\,d\mathsf H_t\mu_n\to\int g\,d\mathsf H_t\mu$ for every bounded continuous $g$.
--
--   Given such a family, the **pointwise version** of the semigroup is
--   $$\tilde{\mathsf P}_tf(x):=\int_X f\,d\mathsf H_t\delta_x,\qquad x\in X.$$
--
--   This is the object of Proposition 3.2 (i): the map $f m\mapsto(\mathsf P_tf)m$ extends uniquely to a $W_{(\beta)}$-continuous map of $\mathscr P(X)$, and $W_{(\beta)}$ metrizes weak convergence (p. 25). Since the measures $f m$ with $f$ as in item 2 are weakly dense in $\mathscr P(X)$ when $\operatorname{supp} m=X$, the three properties determine $\mathsf H_t$ on $\mathscr P(X)$; Proposition 3.2 states that such a family exists under the Lipschitz bound (3.15).
--
--   **Formalization Note** The dual semigroup is a predicate on a family `H : ℝ → Measure X → Measure X`, not a construction; its values on measures that are not probability measures are irrelevant. Weak convergence is tested against `BoundedContinuousFunction X ℝ`. $\tilde{\mathsf P}_tf(x)$ is a Bochner integral, the paper's value whenever $f$ is $\mathsf H_t\delta_x$-integrable (for instance bounded Borel).
-- source:
--   arXiv:1209.5786v4, Proposition 3.2 (i)–(ii), (3.17), p. 27; weak topology of W_(β), p. 25

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

variable {X : Type*} [MeasurableSpace X]

section Dual
variable [MetricSpace X] [BorelSpace X]

/-- The dual semigroup of Proposition 3.2 (i), p. 27, pinned by its defining property: `H t` maps
probability measures to probability measures, sends `f m` to `(P_t f) m` for every probability density
`f ∈ L¹ ∩ L²(X, m)`, and is continuous for the weak convergence of probability measures (the topology of
`W_(β)`, p. 25). -/
def IsDualSemigroup (m : Measure X) (P : ℝ → (X → ℝ) → X → ℝ) (H : ℝ → Measure X → Measure X) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (∀ μ : Measure X, IsProbabilityMeasure μ → IsProbabilityMeasure (H t μ)) ∧
    (∀ f : X → ℝ, MemLp f 2 m → Integrable f m → 0 ≤ᵐ[m] f → ∫ x, f x ∂m = 1 →
      H t (m.withDensity (fun x => ENNReal.ofReal (f x))) =
        m.withDensity (fun x => ENNReal.ofReal (P t f x))) ∧
    (∀ (μs : ℕ → Measure X) (μ : Measure X), (∀ n, IsProbabilityMeasure (μs n)) → IsProbabilityMeasure μ →
      (∀ g : BoundedContinuousFunction X ℝ, Tendsto (fun n => ∫ x, g x ∂(μs n)) atTop (𝓝 (∫ x, g x ∂μ))) →
      ∀ g : BoundedContinuousFunction X ℝ, Tendsto (fun n => ∫ x, g x ∂(H t (μs n))) atTop (𝓝 (∫ x, g x ∂(H t μ))))

/-- `P̃_t f(x) = ∫ f dH_tδ_x` (Proposition 3.2 (ii)). -/
noncomputable def Ptilde (H : ℝ → Measure X → Measure X) (t : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  ∫ y, f y ∂(H t (Measure.dirac x))

end Dual

end BERicci.Contract


