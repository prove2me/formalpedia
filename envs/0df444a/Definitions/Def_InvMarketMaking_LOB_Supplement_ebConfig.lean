-- Prove2me | Definitions.Def_InvMarketMaking_LOB_Supplement_ebConfig
-- name    : InvMarketMaking_LOB_Supplement_ebConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:30:39.919212+00:00
-- url     : https://prove2.me/theorems/c8e66475-95a6-4997-9cb7-ee5cf8da1ab6
-- title:
--   Empirical-Bernstein radii of Proposition 6.5 as an Algorithm 4 configuration
-- statement:
--   For finite grids $\mathcal B^\circ,\mathcal A^\circ\subseteq[0,1]$, a horizon $T$ and a failure parameter $\delta$, the **empirical-Bernstein radii** of Proposition 6.5 are
--   $$
--   \psi_t(b,\delta)=\sqrt{\frac{2\widehat F_t(b)(1-\widehat F_t(b))\log(3|\mathcal B^\circ|T/\delta)}{t}}+\frac{3\log(3|\mathcal B^\circ|T/\delta)}{t}\quad(b\in\mathcal B^\circ),
--   $$
--   and the same on the ask side with $\widehat S_t$ and $|\mathcal A^\circ|$. Here $\widehat F_t(b)=\frac1t\sum_{\tau\le t}\mathbb I(V^{\mathrm{sell}}_\tau\le b)$ and $\widehat S_t(a)=\frac1t\sum_{\tau\le t}\mathbb I(V^{\mathrm{buy}}_\tau\ge a)$ are the estimators of Eq. (12). This object packages the grids and radii as a configuration of the published Algorithm 4 (`lobRound`). With it, the published good event is exactly Eq. (16) for these radii.
--
--   These radii give the instance-dependent guarantee of Theorem 6.19, and Theorem 6.6 compares them with the Bernstein radius built from the true $F$.
--
--   **Formalization Note** The square root covers only the first fraction. Algorithm 4 reads the radius at time $t-1$ only at its active prices. There $\widehat F_{t-1}$ and $\widehat S_{t-1}$ equal the algorithm's observable limit-order-book estimates (Proposition 6.7), so this is the algorithm as run. At $t=0$ Algorithm 4 uses $\psi_0=1$.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 6.5, p. 35; Definition 6.4, Eq. (16), p. 34; Eq. (12), p. 33

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_lobRound
import Definitions.Def_InvMarketMaking_LOB_goodEvent

namespace InvMarketMaking.LOB.Supplement

/-- The empirical-Bernstein radius `√(2 p (1 − p) L / t) + 3 L / t` at the empirical frequency `p`,
time `t` and logarithmic factor `L` (Maran, Restelli, Stradi, No-Regret Revenue Maximization in
Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 6.5, p. 35).
The square root covers only the first fraction. -/
noncomputable def ebRadius (L p : ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (2 * p * (1 - p) * L / t) + 3 * L / t

/-- The radii of Proposition 6.5 (p. 35), packaged as a configuration of Algorithm 4: grids
`B° = Bg`, `A° = Ag`, and, for `b ∈ B°` and `a ∈ A°`,
`ψ_t(b, δ) = √(2 F̂_t(b)(1 − F̂_t(b)) log(3|B°|T/δ)/t) + 3 log(3|B°|T/δ)/t`,
`ψ_t(a, δ) = √(2 Ŝ_t(a)(1 − Ŝ_t(a)) log(3|A°|T/δ)/t) + 3 log(3|A°|T/δ)/t`,
with `F̂_t`, `Ŝ_t` the empirical estimators of Eq. (12), p. 33 (`empCdf`, `empSurv`). With this
configuration, `goodEvent V (ebConfig M Bg Ag T δ) M T` is the good event (16) of Definition 6.4 for
the radii of Proposition 6.5.

**Formalization Note** (i) `log` is the natural logarithm and `|B°|` is the cardinality of the
finite set. (ii) Algorithm 4 run with this configuration (`lobRound`) reads the radius at time
`t − 1` only at its active prices, where `F̂_{t−1}` and `Ŝ_{t−1}` equal the algorithm's observable
limit-order-book estimates (Proposition 6.7, p. 36); so this is the algorithm as run, and it avoids a
circular definition (`lobRound` takes the radius as an input). (iii) At `t = 0` the formula is not
used: Algorithm 4 uses `ψ_0 = 1` (`radius`). -/
noncomputable def ebConfig {Ω : Type*} (M : Market Ω) (Bg Ag : Finset ℝ) (T : ℕ) (δ : ℝ) :
    LOBConfig Ω where
  Bg := Bg
  Ag := Ag
  ψF := fun t b ω => ebRadius (Real.log (3 * Bg.card * T / δ)) (empCdf M t b ω) t
  ψS := fun t a ω => ebRadius (Real.log (3 * Ag.card * T / δ)) (empSurv M t a ω) t

end InvMarketMaking.LOB.Supplement


