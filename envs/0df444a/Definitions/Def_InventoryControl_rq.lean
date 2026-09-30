-- Prove2me | Definitions.Def_InventoryControl_rq
-- name    : InventoryControl_rq
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-23T23:40:18.268897+00:00
-- url     : https://prove2.me/theorems/4758c37f-e782-42ba-a794-6d9aca6ea9a7
-- title:
--   The continuous review $(R,Q)$ policy under normally distributed lead-time demand: inventory level, service levels and cost rate
-- statement:
--   The steady-state model of a continuous review $(R,Q)$ policy facing continuous, normally
--   distributed demand, in the notation of Axsäter, *Inventory Control*, Chapter 5.
--
--   An order for $Q$ units is placed whenever the **inventory position** (stock on hand plus
--   outstanding orders minus backorders) reaches the **reorder point** $R$, and it arrives after a
--   constant lead-time. The book's standing approximation for continuous demand (Sect. 5.3.1,
--   p. 75) is that in steady state the inventory position is uniformly distributed on the interval
--   $[R, R+Q]$; this is `rqPosition R Q`, the uniform probability measure on that interval. The
--   **lead-time demand** is normal with mean $\mu'$ and standard deviation $\sigma'$ and is
--   independent of the inventory position; it is the same law `newsboyDemand m s` as in the newsboy
--   model, with $m = \mu'$ and $s = \sigma'$.
--
--   The fundamental relationship of Sect. 5.3.2, Eq. (5.35), is
--   $$ IL(t+L) \;=\; IP(t) - D(t, t+L), $$
--   the inventory level a lead-time later equals the inventory position now minus the demand in
--   between. Accordingly `rqLevel R Q m s` is the law of $IP - D$, the image of the product of the
--   two laws above under subtraction. From it,
--
--   * `rqCDF R Q m s x` is the distribution function $F(x) = \Pr[IL \le x]$ of Eq. (5.39);
--   * `rqReadyRate R Q m s` is the **ready rate** $S_3 = \Pr[IL > 0]$ of Eq. (5.50), which for
--     continuous demand coincides with the **fill rate** $S_2$ (Sect. 5.7.2);
--   * `rqBatchBackorders R Q m s` is $\mathbb{E}(B)$, the expected backordered quantity covered by
--     one batch, defined in Sect. 5.8 by the three cases $B = 0$ for $u \le R$, $B = u - R$ for
--     $R < u \le R + Q$ and $B = Q$ for $u > R + Q$, where $u$ is the lead-time demand; that is
--     $\mathbb{E}\big[\min\{(u-R)^{+}, Q\}\big]$;
--   * `rqCost h b1 R Q m s` is the expected cost rate of Eq. (5.56),
--     $\mathbb{E}\big[h\,(IL)^{+} + b_1\,(IL)^{-}\big]$, with holding cost $h$ per unit and time unit
--     and backorder cost $b_1$ per unit and time unit;
--   * `normalLossH x` is the second loss function $H(x) = \int_x^{\infty} G(v)\,\mathrm{d}v$ of
--     Eq. (5.64), built on the loss function $G$ of Eq. (5.40) published with the newsboy model.
--
--   Two lemmas record that `rqPosition R Q` and `rqLevel R Q m s` are probability measures whenever
--   $Q > 0$.
--
--   **Formalization Note** `rqPosition R Q` is Lebesgue measure conditioned on $[R, R+Q]$, which
--   is the zero measure when $Q = 0$; `rqLevel` is the pushforward of the product measure under
--   $(u, d) \mapsto u - d$. Every statement assumes $Q > 0$ and $\sigma' > 0$. The mean $\mu'$ is an
--   arbitrary real: the book has $\mu' = \mu L > 0$, but none of the formulas depends on its sign.
--   Costs $h$ and $b_1$ are unconstrained in the definitions; positivity is a hypothesis of each
--   theorem. The integrals are Bochner integrals, which return $0$ for a non-integrable function;
--   integrability of the cost integrand is therefore a theorem of this mission rather than an
--   assumption.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Sect. 5.3.2 p. 75 (Eq. 5.35), Sect. 5.3.4 pp. 75-76 (the uniform inventory position and Eq. 5.39), Sect. 5.7.2 p. 82 (Eq. 5.50, 5.52), Sect. 5.8 p. 83 (Eq. 5.54-5.55), Sect. 5.9 pp. 83-86 (Eq. 5.56, 5.62, 5.64)

import Definitions.Def_InventoryControl_newsboy

open MeasureTheory ProbabilityTheory

namespace InventoryControl

/-- The steady-state inventory position of a continuous review `(R, Q)` policy under continuous
demand: uniform on `[R, R + Q]`. Axsäter, *Inventory Control*, Sect. 5.3.1 p. 75. -/
noncomputable def rqPosition (R Q : ℝ) : Measure ℝ := volume[|Set.Icc R (R + Q)]

/-- The law of the inventory level `IL = IP - D(L)`, Eq. (5.35): the inventory position is
uniform on `[R, R + Q]` and the lead-time demand is normal with mean `m` and standard deviation
`s`, the two being independent. Axsäter, *Inventory Control*, Sects. 5.3.2 and 5.3.4. -/
noncomputable def rqLevel (R Q m s : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 - p.2) ((rqPosition R Q).prod (newsboyDemand m s))

/-- The distribution function `F(x) = P(IL ≤ x)` of the inventory level, Eq. (5.39). -/
noncomputable def rqCDF (R Q m s x : ℝ) : ℝ := (rqLevel R Q m s).real (Set.Iic x)

/-- The ready rate `S₃ = P(IL > 0)`, Eq. (5.50); equal to the fill rate `S₂` for continuous
demand, Sect. 5.7.2. -/
noncomputable def rqReadyRate (R Q m s : ℝ) : ℝ := (rqLevel R Q m s).real (Set.Ioi 0)

/-- `E(B)`: the expected backordered quantity covered by one batch, Sect. 5.8 p. 83.  With
lead-time demand `u`, `B = 0` if `u ≤ R`, `B = u - R` if `R < u ≤ R + Q`, and `B = Q` if
`u > R + Q`. -/
noncomputable def rqBatchBackorders (R Q m s : ℝ) : ℝ :=
  ∫ u, min (max (u - R) 0) Q ∂(newsboyDemand m s)

/-- The second loss function `H(x) = ∫_x^∞ G(v) dv`, Eq. (5.64). -/
noncomputable def normalLossH (x : ℝ) : ℝ := ∫ v in Set.Ioi x, normalLoss v

/-- The expected holding-plus-backorder cost rate `h E(IL)⁺ + b₁ E(IL)⁻`, Eq. (5.56) and
(5.62). -/
noncomputable def rqCost (h b1 R Q m s : ℝ) : ℝ :=
  ∫ x, (h * max x 0 + b1 * max (-x) 0) ∂(rqLevel R Q m s)

lemma isProbabilityMeasure_rqPosition (R Q : ℝ) (hQ : 0 < Q) :
    IsProbabilityMeasure (rqPosition R Q) := by
  unfold rqPosition
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;>
    simp [Real.volume_Icc, hQ]

lemma isProbabilityMeasure_rqLevel (R Q m s : ℝ) (hQ : 0 < Q) :
    IsProbabilityMeasure (rqLevel R Q m s) := by
  have := isProbabilityMeasure_rqPosition R Q hQ
  unfold rqLevel
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end InventoryControl


