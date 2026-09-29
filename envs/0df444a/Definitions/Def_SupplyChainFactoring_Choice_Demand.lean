-- Prove2me | Definitions.Def_SupplyChainFactoring_Choice_Demand
-- name    : SupplyChainFactoring_Choice_Demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:22:26.229746+00:00
-- url     : https://prove2.me/theorems/0e5ec3d9-cb7a-4ed1-a3a3-b03ee8d0bd5f
-- title:
--   The strictly IFR demand model of §3.1: $\bar F$, $S(q)$, $k(q)$ and the failure rate $z$
-- statement:
--   Let the demand $D$ be a nonnegative random variable with law $\mu$ on $\mathbb R$, probability density $f$, cumulative distribution function $F$ and complementary distribution function
--
--   $$\bar F(x) = 1 - F(x) = P(D > x).$$
--
--   Kouvelis and Xu assume that (i) $D$ has a finite mean and a continuous density with $f(\xi) > 0$ on $[0, \mathbb Z]$, where $\mathbb Z \le +\infty$ is the upper end of the support of $D$, and (ii) the **failure rate** $z(\xi) = f(\xi)/\bar F(\xi)$ is strictly increasing in $\xi$ (the demand is strictly IFR). The **expected sales** at stocking quantity $q$ and the auxiliary ratio $k$ are
--
--   $$S(q) = \mathbb E[\min(D, q)] = \int_0^q \bar F(\xi)\,d\xi, \qquad k(q) = \frac{S(q)}{\bar F(q)}.$$
--
--   A demand model in this sense is a probability measure $\mu$ with density $f \ge 0$, no mass on $(-\infty, 0)$, finite mean, an endpoint $\mathbb Z \in (0, +\infty]$ with $P(D > x) = 0$ for every real $x \ge \mathbb Z$, $f$ continuous and positive on $[0, \mathbb Z]$ (on $[0, \infty)$ when $\mathbb Z = +\infty$), and $z$ strictly increasing on $[0, \mathbb Z)$. These are the demand assumptions under which every equilibrium result of the paper is stated.
--
--   **Formalization Note** $\mathbb Z$ is an extended real `Z : EReal`. The paper writes "a continuous p.d.f., with $f(\xi) > 0$ in $[0, \mathbb Z]$"; a density that vanishes after a finite $\mathbb Z$ cannot be continuous on all of $\mathbb R$, so continuity is read on the support $[0, \mathbb Z]$, and $\mathbb Z$ is read as the upper end of the support. The failure rate is only meaningful where $\bar F > 0$, i.e. on $[0, \mathbb Z)$, and strict monotonicity is required there. `Fbar μ x` is $\mu((x, \infty))$ as a real number; `S`, `k`, `z` are the displays above, with Lean's convention that a quotient by $0$ is $0$ (never used on $[0, \mathbb Z)$, where $\bar F > 0$). The paper's further "standard modeling assumptions" of Table EC.2 (Online Appendix A) are not available and are not included.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6075, §3.1 (demand assumptions (i)–(ii)); p. 6076, §3.4 (S(q) and k(q))

import Mathlib

open MeasureTheory

namespace SupplyChainFactoring.Choice

/-- Complementary CDF `F̄(x) = P(D > x) = 1 − F(x)` of the demand law `μ` (Kouvelis–Xu 2021, §3.1,
p. 6075). -/
noncomputable def Fbar (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Ioi x)).toReal

/-- Expected sales `S(q) = E[min(D, q)] = ∫₀^q F̄(ξ) dξ` (p. 6076). -/
noncomputable def S (μ : Measure ℝ) (q : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..q, Fbar μ ξ

/-- `k(q) = S(q) / F̄(q)` (p. 6076). -/
noncomputable def k (μ : Measure ℝ) (q : ℝ) : ℝ := S μ q / Fbar μ q

/-- Failure rate `z(ξ) = f(ξ) / F̄(ξ)` of the demand with density `f` (p. 6075). -/
noncomputable def z (μ : Measure ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ := f ξ / Fbar μ ξ

/-- The demand assumptions of §3.1 (p. 6075): the demand `D` is a nonnegative random variable with
law `μ` and probability density `f`; (i) it has a finite mean and a continuous p.d.f. with
`f(ξ) > 0` on `[0, Z]` (`Z ≤ +∞`), `Z` being the upper end of the support; (ii) its failure rate
`z(ξ) = f(ξ)/F̄(ξ)` is strictly increasing (strict IFR). Continuity of `f` is read on the support
`[0, Z]` (a density that vanishes after a finite `Z` cannot be continuous on all of `ℝ`). -/
structure DemandModel (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal) : Prop where
  isProbability : IsProbabilityMeasure μ
  f_nonneg : ∀ x, 0 ≤ f x
  hasDensity : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))
  nonneg : μ (Set.Iio 0) = 0
  finiteMean : Integrable (fun x : ℝ => x) μ
  Z_pos : 0 < Z
  support_le : ∀ x : ℝ, Z ≤ (x : EReal) → μ (Set.Ioi x) = 0
  f_continuousOn : ContinuousOn f {x : ℝ | 0 ≤ x ∧ (x : EReal) ≤ Z}
  f_pos : ∀ x : ℝ, 0 ≤ x → (x : EReal) ≤ Z → 0 < f x
  strictIFR : StrictMonoOn (z μ f) {x : ℝ | 0 ≤ x ∧ (x : EReal) < Z}

end SupplyChainFactoring.Choice


