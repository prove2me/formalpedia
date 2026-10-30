-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_extremalSeq
-- name    : WassersteinDRO_ConvexLossP1_extremalSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:11.87931+00:00
-- url     : https://prove2.me/theorems/cfd36389-eaa0-4336-bce0-99eaedc2fc77
-- title:
--   The distributions $\mathbb Q_n$ of the asymptotically optimal sequence
-- statement:
--   Let $E$ be a real normed space, $\widehat\xi_1, \dots, \widehat\xi_N \in E$ samples, $i_0 \in \{1, \dots, N\}$, $\xi^\star \in E$, $\varepsilon \in \mathbb R$ and $n \ge 1$. Define the probability distribution
--   $$\mathbb Q_n = \frac1N \sum_{i \ne i_0} \delta_{\widehat\xi_i} + \frac{n-1}{nN} \, \delta_{\widehat\xi_{i_0}} + \frac{1}{nN} \, \delta_{\widehat\xi_{i_0} + \varepsilon n N \xi^\star}.$$
--
--   It is obtained from the empirical distribution by moving the fraction $1/(nN)$ of the mass at $\widehat\xi_{i_0}$ to the far point $\widehat\xi_{i_0} + \varepsilon n N \xi^\star$; as $n \to \infty$ ever less mass moves ever farther at the same transport cost.
--
--   **Formalization Note** The weights are converted to nonnegative extended reals; at $n = 0$ (outside the paper's range $n \ge 1$) the negative weight $(n-1)/(nN)$ is clipped to $0$. The conditions the paper puts on $i_0$ and $\xi^\star$ are hypotheses of the statements that use $\mathbb Q_n$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.2, unnumbered display after Remark 3, p. 14

import Mathlib

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The distributions `Q_n` of the asymptotically optimal sequence.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.2, unnumbered display after Remark 3, p. 14: "select i0 ∈ [N] and ξ⋆ ∈ arg max_{‖ξ‖≤1}
ξ^⊤z⋆. Then, the distributions
Q_n = (1/N) Σ_{i≠i0}^{N} δ_{ξ̂i} + (n − 1)/(nN) δ_{ξ̂i0} + 1/(nN) δ_{ξ̂i0+εnNξ⋆}
can be shown to be feasible and asymptotically optimal in (6) as n ≥ 1 tends to infinity."

`extremalSeq ξhat i0 ξstar ε n` is the measure
`N⁻¹ Σ_{i ≠ i0} δ_{ξhat i} + ((n − 1)/(nN)) δ_{ξhat i0} + (1/(nN)) δ_{ξhat i0 + εnN ξstar}`.

**Formalization Note.** The choice of `i0` and `ξstar` is a parameter; the conditions the paper
puts on them (`ξ⋆` a maximizer of `ξ ↦ z⋆(ξ)` on the unit ball) are hypotheses of the statements.
The weights are real numbers converted with `ENNReal.ofReal`; for `n ≥ 1` (the paper's range) they
are the paper's nonnegative weights, summing to `1` together with the `N − 1` weights `1/N`. At
`n = 0` the weight `(n − 1)/(nN)` would be negative and is clipped to `0`; no statement uses
`n = 0` except through limits along `n → ∞`. -/
noncomputable def extremalSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {N : ℕ} (ξhat : Fin N → E) (i0 : Fin N) (ξstar : E) (ε : ℝ) (n : ℕ) :
    Measure E :=
  ((N : ENNReal)⁻¹) • ∑ i ∈ Finset.univ.erase i0, Measure.dirac (ξhat i)
    + ENNReal.ofReal (((n : ℝ) - 1) / ((n : ℝ) * N)) • Measure.dirac (ξhat i0)
    + ENNReal.ofReal (1 / ((n : ℝ) * N)) • Measure.dirac (ξhat i0 + (ε * n * N) • ξstar)

end WassersteinDRO.ConvexLossP1


