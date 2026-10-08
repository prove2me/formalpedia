-- Prove2me | Definitions.Def_PoissonDirichlet_Chain_Setting
-- name    : PoissonDirichlet_Chain_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:03.003732+00:00
-- url     : https://prove2.me/theorems/90732dbf-c46d-4ab6-bdd9-cfe8e6d036ed
-- title:
--   Definition 1, p. 857; (21), (32), (34), (43), (45), (125), (138), (139) — PD(α, θ), the sequences (V_n), (R_n), (Y_n), and the law P*_{α,θ}
-- statement:
--   Fix parameters $0 \le \alpha < 1$ and $\theta > -\alpha$.
--
--   **Stick-breaking and ranking.** For a sequence $y = (y_1, y_2, \dots)$ the **stick-breaking** map (4) gives $\tilde V_1 = y_1$, $\tilde V_n = (1-y_1)\cdots(1-y_{n-1})\,y_n$ for $n \ge 2$. The **ranked values** of a nonnegative sequence $x$ are its terms in decreasing order, counted with multiplicity: the $(k+1)$-th ranked value is the least $t \ge 0$ such that at most $k$ terms of $x$ exceed $t$.
--
--   **Definition 1 (PD$(\alpha,\theta)$).** Let $\tilde Y_1, \tilde Y_2, \dots$ be independent with $\tilde Y_n \sim \mathrm{beta}(1-\alpha, \theta+n\alpha)$, where $\mathrm{beta}(a,b)$ has density $\frac{\Gamma(a+b)}{\Gamma(a)\Gamma(b)}x^{a-1}(1-x)^{b-1}$ on $(0,1)$. The **Poisson–Dirichlet distribution** $\mathrm{PD}(\alpha,\theta)$ is the law of the ranked values $V_1 \ge V_2 \ge \cdots$ of the stick-breaking sequence of $(\tilde Y_n)$. A random sequence $(V_n)$ on $(\Omega, P)$ has the $\mathrm{PD}(\alpha,\theta)$ distribution if $P(V \in S)$ equals the probability that the ranked stick-breaking sequence lies in $S$, for every measurable set $S$ of sequences.
--
--   **Derived sequences.** From a sequence $(V_n)$ define
--   $$R_n = \frac{V_{n+1}}{V_n}\ \ (21), \qquad Y_n = \frac{V_n}{V_n + V_{n+1} + \cdots}\ \ (45), \qquad \Sigma_n = \frac{V_{n+1} + V_{n+2} + \cdots}{V_n}\ \ (32).$$
--   From a sequence of ratios $(R_n)$ define, as in (125),
--   $$Y_n = (1 + R_n + R_nR_{n+1} + \cdots)^{-1}, \qquad \Sigma_1 = R_1 + R_1R_2 + R_1R_2R_3 + \cdots.$$
--
--   **The law $P^*_{\alpha,\theta}$ (Theorem 38).** A probability measure on sequences $(R_1, R_2, \dots)$ under which the $R_n$ are independent and $R_n \sim \mathrm{beta}(\theta + n\alpha, 1)$, i.e. $R_n$ has density $(\theta+n\alpha)x^{\theta+n\alpha-1}$ on $(0,1)$.
--
--   **Functions and constants.** For $0<\alpha<1$, $\lambda \ge 0$:
--   $$\psi_\alpha(\lambda) = 1 + \alpha\int_0^1 (1 - e^{-\lambda x})\,x^{-\alpha-1}\,dx \ \ (34),$$
--   $$C_{\alpha,\theta} = \frac{\Gamma(\theta+1)}{\Gamma(\theta/\alpha+1)}\Gamma(1-\alpha)^{\theta/\alpha}\ \ (43), \qquad K_{\alpha,\theta} = \Gamma(\theta+1)\Gamma(1-\alpha)^{\theta/\alpha}\ \ (138).$$
--   Given a family of functions $r(\alpha,\theta',\cdot)$, the **forward transition density** from $Y_n = y$ to $Y_{n+1} = z$ is
--   $$q_n(y,z) = \alpha\, y^{-\alpha-1}(1-y)^{n\alpha+\theta-1}\,\frac{r(\alpha,\theta+n\alpha,z)}{r(\alpha,\theta+n\alpha-\alpha,y)} \quad (0<y<1,\ 0<z<y/(1-y)),$$
--   and $0$ otherwise. This is (139) with the factor $\alpha$ that the printed (139) omits: Bayes' rule applied to (128), (146) and the $\mathrm{beta}(\theta+n\alpha,1)$ density of $R_n$ produces it, and it is the factor $\alpha^{n-1}$ of Corollary 41.
--
--   Finally, the $m$-fold convolution power $\nu^{*m}$ of a measure $\nu$ on $\mathbb R$ is $\nu^{*0} = \delta_0$, $\nu^{*(m+1)} = \nu^{*m} * \nu$.
--
--   These are the objects of Theorem 38: $\mathrm{PD}(\alpha,\theta)$ and the product law $P^*_{\alpha,\theta}$ both induce a law on the sequence $(Y_n)$, and the theorem compares them.
--
--   **Formalization Note.** Sequences are 0-based: `V ω k` is $V_{k+1}$, `ratio v k` is $R_{k+1}$, `Yseq v k` and `YofR r k` are $Y_{k+1}$, `Sigseq v 0` is $\Sigma_1$, and `r k` is $R_{k+1}$. `ranked` counts with `Set.encard`, never `Set.ncard`. `HasPD` is stated through measures of preimages, never `Measure.map` of `ranked ∘ stick`. `IsStarLaw α θ μ` characterises $P^*_{\alpha,\theta}$ by its independent coordinates. `transDens α θ rf k y z` is $q_{k+1}(y,z)$ with `rf θ' y` in the role of $r(\alpha,\theta',y)$. The definitions `stick`, `ranked`, `IsStickLaw`, `HasPD`, `ratio`, `psi` and `pdConst` repeat those of the other missions of this series, because drafts cannot import drafts.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 857, Definition 1, (3), (4); p. 861, (21); p. 863, (32), (34); p. 865, (43), (45); p. 885, (125); pp. 887–888, Theorem 38, (138), (139)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
import Definitions.Def_PoissonDirichlet_Ratio_Setting
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain

/-- (45), 0-based: `Yseq v k = v k / (v k + v (k+1) + ⋯)` is `Y_{k+1} = V_{k+1} / (V_{k+1} +
V_{k+2} + ⋯)`. -/
noncomputable def Yseq (v : ℕ → ℝ) (k : ℕ) : ℝ := v k / ∑' j, v (k + j)

/-- (125), first expression, 0-based: `YofR r k = (1 + r k + r k r (k+1) + ⋯)⁻¹` is
`Y_{k+1} = (1 + R_{k+1} + R_{k+1} R_{k+2} + ⋯)^{-1}` as a function of the ratios
`R_1, R_2, …` (`r i` plays the role of `R_{i+1}`). -/
noncomputable def YofR (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1 + ∑' j, ∏ i ∈ Finset.range (j + 1), r (k + i))⁻¹

/-- `Σ_1 = R_1 + R_1 R_2 + R_1 R_2 R_3 + ⋯` as a function of the ratios; by (32) this is
`(1 - V_1) / V_1`. -/
noncomputable def SigofR (r : ℕ → ℝ) : ℝ := ∑' j, ∏ i ∈ Finset.range (j + 1), r i

/-- `IsStarLaw α θ μ` (Theorem 38, the law `P*_{α,θ}`): under the probability measure `μ` on
sequences `r`, the coordinates `r 0, r 1, …` (the `R_1, R_2, …`) are independent and `r k`
(that is `R_{k+1}`) has law `beta(θ + (k+1) α, 1)`. -/
def IsStarLaw (α θ : ℝ) (μ : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ iIndepFun (fun k (r : ℕ → ℝ) => r k) μ ∧
    ∀ k : ℕ, HasLaw (fun r : ℕ → ℝ => r k) (betaMeasure (θ + ((k : ℝ) + 1) * α) 1) μ

/-- (138): `K_{α,θ} = Γ(θ + 1) Γ(1 - α)^{θ/α}` (for `0 < α < 1`, `θ > -α`). -/
noncomputable def chainConst (α θ : ℝ) : ℝ :=
  Real.Gamma (θ + 1) * Real.Gamma (1 - α) ^ (θ / α)

/-- The forward transition density of Theorem 38 (ii), (139), from `Y_n = y` to
`Y_{n+1} = z`, with `n = k + 1`, written with the factor `α` that (139) as printed omits (it is
forced by Bayes' rule from (128), (146) and the beta(θ + nα, 1) density, and it is the factor
`α^{n-1}` of Corollary 41):
`α y^{-α-1} (1 - y)^{nα+θ-1} r(α, θ + nα, z) / r(α, θ + nα - α, y)` for `0 < y < 1`,
`0 < z < y/(1 - y)`, and `0` otherwise. Here `rf θ' y` plays the role of `r(α, θ', y)` (140). -/
noncomputable def transDens (α θ : ℝ) (rf : ℝ → ℝ → ℝ) (k : ℕ) (y z : ℝ) : ℝ :=
  if 0 < y ∧ y < 1 ∧ 0 < z ∧ z < y / (1 - y) then
    α * y ^ (-α - 1) * (1 - y) ^ (((k : ℝ) + 1) * α + θ - 1) *
      rf (θ + ((k : ℝ) + 1) * α) z / rf (θ + (k : ℝ) * α) y
  else 0

/-- The `m`-fold additive convolution power of a measure on `ℝ`: `convPow ν 0 = δ_0`,
`convPow ν (m+1) = convPow ν m ∗ ν`. -/
noncomputable def convPow (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | m + 1 => (convPow ν m).conv ν

end PoissonDirichlet.Chain


