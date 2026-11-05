-- Prove2me | Definitions.Def_BrownianEnergyRep_IsWienerMeasure
-- name    : BrownianEnergyRep_IsWienerMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:29.827413+00:00
-- url     : https://prove2.me/theorems/a539cce1-7ab9-413b-85fd-9948fb81c7e2
-- title:
--   Wiener measure $\mu$ on $W(G)$: the finite dimensional distributions (2.2)
-- statement:
--   A measure $\mu$ on $(W(G),\mathcal B)$ is the Wiener measure if it is a probability measure and, for all $k$, all partitions $0=s_0<s_1<\dots<s_k=T$, and all bounded measurable $f:G^k\to\mathbb R$,
--   $$
--   \mu\big(f(g_{s_1},\dots,g_{s_k})\big)=\int_{G^k}f(x_1,\dots,x_k)\prod_{i=1}^kp_{\Delta s_i}(x_{i-1}^{-1}x_i)\,dx_1\cdots dx_k,
--   $$
--   where $x_0=e$ and $\Delta s_i=s_i-s_{i-1}$. Its existence and uniqueness is Theorem 2.4.
--
--   **Formalization Note** The value does not depend on the normalization of Haar measure, as $p$ scales inversely.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.4, (2.2), pp.3-4

import Mathlib
import Definitions.Def_BrownianEnergyRep_WienerGroup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `μ` is the Wiener measure of Theorem 2.4: a probability measure on `(W(G), 𝓑)` whose finite
dimensional distributions are (2.2) (arXiv:1511.07378v1, Theorem 2.4, (2.2), pp.3-4).

**Formalization Note** The partition is `0 = s₀ < s₁ < … < s_k = T`, and `Fin.cons 1 x` is the tuple
`(x₀ = e, x₁, …, x_k)`. `f` is bounded, so with `p` continuous both integrals are genuine. -/
structure IsWienerMeasure {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} [CompactSpace ↥G]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (T : ℝ) [Fact (0 < T)]
    (μ : Measure ↥(WienerGroup G T)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  finite_dimensional : ∀ (k : ℕ) (s : Fin (k + 1) → ℝ), s 0 = 0 → StrictMono s →
    s (Fin.last k) = T → ∀ f : (Fin k → ↥G) → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
    ∫ γ, f (fun i => pathAt γ (s i.succ)) ∂μ =
      ∫ x, f x * ∏ i : Fin k, p (s i.succ - s i.castSucc)
        (((Fin.cons 1 x : Fin (k + 1) → ↥G) i.castSucc)⁻¹ *
          (Fin.cons 1 x : Fin (k + 1) → ↥G) i.succ) ∂(Measure.pi fun _ => m)

end BrownianEnergyRep


