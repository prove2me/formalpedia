-- Prove2me | Definitions.Def_NestedCRP_stickMass
-- name    : NestedCRP_stickMass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:21.80726+00:00
-- url     : https://prove2.me/theorems/8e9ecfdd-ef10-40dd-bae7-b96e376a7cf1
-- title:
--   Marginal level mass and the level prior of §5.1
-- statement:
--   For a vector $\zeta$ of levels, the marginal level mass is
--
--   $$
--   \mathrm{stick}(\zeta)=\mathbb E\Bigl[\prod_i\theta_{\zeta_i}\Bigr],\qquad \theta\sim\mathrm{GEM}(m,\pi),
--   $$
--
--   the probability of these levels once the document's $\theta$ is integrated out. With $z'$ the vector leaving out word $n$, the level prior is
--
--   $$
--   \frac{m\pi+\#[z'=k]}{\pi+\#[z'\ge k]}\prod_{j<k}\frac{(1-m)\pi+\#[z'>j]}{\pi+\#[z'\ge j]}.
--   $$
--
--   **Formalization Note** The mass is a genuine Bochner integral, not a collapsed formula; its integrand is measurable with values in $[0,1]$ almost surely, so it is integrable. Levels are 0-based, which leaves the comparisons unchanged. The prior formula is taken at every $k$: §5.1 prints $k\le\max(z_{d,-n})$, and the same derivation covers all $k$.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §4, p.7:11; §5, p.7:14; §5.1, third display, p.7:16

import Mathlib
import Definitions.Def_NestedCRP_gemLaw
open MeasureTheory

namespace NestedCRP

/-- The marginal mass of a vector of levels under a GEM(m, π) draw:
`E[∏_i θ_{ζ i}]`, the probability that words `i` take levels `ζ i` once the document's `θ` is
integrated out. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §4, p.7:11, and §5, p.7:14 (the `θ_d` are marginalized).

**Formalization Note** This is a genuine Bochner integral, not a collapsed formula. The integrand is
measurable and takes values in `[0, 1]` almost surely, so it is integrable. -/
noncomputable def stickMass {ι : Type*} [Fintype ι] (m pi : ℝ) (ζ : ι → ℕ) : ℝ :=
  ∫ U, ∏ i, stick U (ζ i) ∂gemLaw m pi

/-- The level prior `p(z_{d,n} = k | z_{d,-n}, m, π)`:
`(mπ + #[z' = k]) / (π + #[z' ≥ k]) · ∏_{j<k} ((1 − m)π + #[z' > j]) / (π + #[z' ≥ j])`, where `z'`
leaves out word `n` of the vector `ζ` of levels of the document.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.1, third display, p.7:16.

**Formalization Note** Levels are 0-based, which shifts nothing in the comparisons. The formula is
taken at every `k`: §5.1 prints `k ≤ max(z_{d,-n})`, and the same derivation covers all `k`. -/
noncomputable def levelPrior {ι : Type*} [Fintype ι] [DecidableEq ι] (m pi : ℝ) (ζ : ι → ℕ) (n : ι)
    (k : ℕ) : ℝ :=
  let others := Finset.univ.erase n
  (m * pi + ((others.filter fun i => ζ i = k).card : ℝ)) /
      (pi + ((others.filter fun i => k ≤ ζ i).card : ℝ)) *
    ∏ j ∈ Finset.range k,
      ((1 - m) * pi + ((others.filter fun i => j < ζ i).card : ℝ)) /
        (pi + ((others.filter fun i => j ≤ ζ i).card : ℝ))

end NestedCRP


