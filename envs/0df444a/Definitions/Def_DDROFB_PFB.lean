-- Prove2me | Definitions.Def_DDROFB_PFB
-- name    : DDROFB_PFB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:10.464051+00:00
-- url     : https://prove2.me/theorems/2f561b9e-c258-4db6-96cb-adc36a994ed1
-- title:
--   The forward–backward confidence region $\mathcal P^{FB}$
-- statement:
--   Let $m_b, m_f, \bar\sigma_f, \bar\sigma_b \in \mathbb R^d$ be thresholds. The **forward–backward confidence region** $\mathcal P^{FB}$ is the set of probability measures $\mathbb P$ on $\mathbb R^d$ with independent components such that, for every $i = 1,\dots,d$,
--
--   $$
--   m_{bi} \;\le\; \mathbb E^{\mathbb P}[\tilde u_i] \;\le\; m_{fi}, \qquad \sigma_f(\mathbb P_i) \le \bar\sigma_{fi}, \qquad \sigma_b(\mathbb P_i) \le \bar\sigma_{bi},
--   $$
--
--   where $\mathbb P_i$ is the $i$-th marginal and $\sigma_f, \sigma_b$ are the forward and backward deviations (20). In the paper the marginal conditions define $\mathcal P^{FB}_i$, a set of Borel probability measures on $\mathbb R$ (no support restriction), and $\mathcal P^{FB} = \{\mathbb P : \mathbb P_i \in \mathcal P^{FB}_i,\ i=1,\dots,d\}$ is the confidence region of the combined test of the hypotheses (21) on the means and deviations.
--
--   This is the set of distributions over which Step 2 of the paper's schema takes the worst case of the Chen–Sim–Sun bound (22).
--
--   **Formalization Note** Independence of the components is included in the region: the paper defines a confidence region as the measures "consistent with any a priori assumptions of the test" (p. 9), and the a priori assumption of Sec. 5.2 and Theorem 6 is that $\mathbb P^*$ has independent components. Since $\mathbb P^*$ itself has independent components, the event $\mathbb P^* \in \mathcal P^{FB}$ is the same with or without it. The deviations are extended nonnegative reals compared with the real thresholds; a finite forward deviation forces the mean to exist, so the mean is never Lean's default value.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 5.2, p. 18 (unnumbered definitions of P^FB_i and P^FB; Θ(−∞,∞) defined on p. 9)

import Mathlib
import Definitions.Def_DDROFB_fwdDev
import Definitions.Def_DDROFB_bwdDev
import Definitions.Def_DDROFB_marginal
import Definitions.Def_DDROFB_HasIndepComponents
open MeasureTheory

namespace DDROFB

/-- **The forward–backward confidence region** `P^FB`.
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 5.2, p. 18
(unnumbered): "`P^FB_i = {P_i ∈ Θ(−∞,∞) : m_bi ≤ E^P_i[ũ_i] ≤ m_fi, σ_fi(P_i) ≤ σ̄_fi,
σ_bi(P_i) ≤ σ̄_bi}`" and "Its confidence region is `P^FB = {P : P_i ∈ P^FB_i i = 1,…,d}`";
`Θ(−∞,∞)` is "the set of Borel probability measures on `ℝ`" (p. 9).

`PFB mb mf σf σb` is the set of probability measures `P` on `ℝ^d` with independent components
such that for every `i` the mean of `ũ_i` exists and lies in `[mb i, mf i]`, and the forward and
backward deviations of the `i`-th marginal are at most `σf i` and `σb i`.

**Formalization Note.** Independence of the components is part of the region: p. 9 defines a
confidence region as the measures "consistent with any a priori assumptions of the test", and the
a priori assumption of this section is that `P∗` has independent components (Theorem 6, Table 1).
The coverage event `P∗ ∈ P^FB` is unchanged by this, since `P∗` itself has independent components.
No bounded-support condition enters the region: `Θ(−∞,∞)` is every Borel probability measure on
`ℝ`. The mean `E^P[ũ_i]` is the Bochner integral `∫ u, u i ∂P`; it is never Lean's default value
`0` here, because a finite forward deviation forces the `i`-th mean to exist (`fwdDev` is `⊤`
otherwise). The deviations are
`ℝ≥0∞`-valued (`fwdDev`, `bwdDev`) and compared with `ENNReal.ofReal` of the thresholds. -/
def PFB {d : ℕ} (mb mf σf σb : Fin d → ℝ) : Set (Measure (EuclideanSpace ℝ (Fin d))) :=
  {P | IsProbabilityMeasure P ∧ HasIndepComponents P ∧
    ∀ i, mb i ≤ ∫ u, u i ∂P ∧ ∫ u, u i ∂P ≤ mf i ∧
      fwdDev (marginal P i) ≤ ENNReal.ofReal (σf i) ∧
      bwdDev (marginal P i) ≤ ENNReal.ofReal (σb i)}

end DDROFB


