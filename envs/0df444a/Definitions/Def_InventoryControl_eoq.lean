-- Prove2me | Definitions.Def_InventoryControl_eoq
-- name    : InventoryControl_eoq
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T06:45:38.272311+00:00
-- url     : https://prove2.me/theorems/61fc7e8d-6bc7-44fe-9dc9-25b3ed506b01
-- title:
--   The classical economic order quantity model
-- statement:
--   The model underlying the classical economic order quantity (EOQ) formula, in the notation of
--   Axsäter, *Inventory Control*, Sect. 4.1.
--
--   A single item faces **constant, continuous demand** at rate $d$ units per time unit. Stock is
--   replenished in batches of a fixed size $Q$; each order costs a fixed **ordering (setup) cost**
--   $A$ regardless of its size, and carrying one unit for one time unit costs the **holding cost**
--   $h$. Shortages are not allowed, the whole batch arrives at once, and $Q$ need not be an
--   integer. Because a batch is delivered exactly when the previous one runs out, the stock level
--   is a sawtooth between $Q$ and $0$, so the average stock on hand is $Q/2$ and orders are placed
--   at the average rate $d/Q$. The **cost per time unit** is therefore
--
--   $$ C(Q) \;=\; \frac{Q}{2}h + \frac{d}{Q}A, $$
--
--   which is `eoqCost A d h Q`. The **economic order quantity**
--
--   $$ Q^{*} \;=\; \sqrt{\frac{2Ad}{h}} $$
--
--   is `eoq A d h`.
--
--   The second pair of definitions is the **finite production rate** variant of Sect. 4.2. There
--   the batch is not delivered all at once but produced continuously at rate $p > d$, so stock
--   builds at rate $p - d$ for a time $Q/p$ and then drains at rate $d$. The peak stock is
--   $Q(1 - d/p)$ and the average stock $Q(1 - d/p)/2$, giving
--
--   $$ C_p(Q) \;=\; \frac{Q(1 - d/p)}{2}h + \frac{d}{Q}A, \qquad
--      Q_p^{*} \;=\; \sqrt{\frac{2Ad}{h(1 - d/p)}} , $$
--
--   which are `eoqCostFinite A d h p Q` and `eoqFinite A d h p`. Letting $p \to \infty$ recovers
--   the classical model.
--
--   These four definitions are the shared vocabulary of the whole *Inventory Control* series: the
--   cost-ratio identity built on `eoqCost` reappears in the analysis of powers-of-two policies and
--   in Roundy's approximation for multi-echelon systems.
--
--   **Formalization Note** All four are plain real-valued functions of real parameters, with no
--   positivity built in; each theorem states the hypotheses ($A, d, h > 0$, and $d < p$ where
--   relevant) it needs. Division in Lean is total, so `eoqCost A d h 0` evaluates to `0` rather
--   than being undefined — every statement below quantifies over $Q > 0$ explicitly.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Chapter 4 'Single-Echelon Systems: Deterministic Lot Sizing', Sect. 4.1 pp. 45-47 (Eq. 4.1, 4.3) and Sect. 4.2 pp. 48-49 (Eq. 4.6, 4.7)

import Mathlib

namespace InventoryControl

/-- Cost per time unit of ordering in batches of size `Q`, for a single item facing constant
continuous demand `d`, with ordering cost `A` and holding cost `h` per unit and time unit.
Axsäter, *Inventory Control*, Eq. (4.1): the average stock `Q / 2` times `h`, plus the average
number of orders per time unit `d / Q` times `A`. -/
noncomputable def eoqCost (A d h Q : ℝ) : ℝ := Q / 2 * h + d / Q * A

/-- The economic order quantity `√(2Ad/h)`. Axsäter, *Inventory Control*, Eq. (4.3). -/
noncomputable def eoq (A d h : ℝ) : ℝ := Real.sqrt (2 * A * d / h)

/-- Cost per time unit when the batch is produced continuously at the finite rate `p > d`
instead of being delivered all at once: the average stock is `Q * (1 - d / p) / 2`.
Axsäter, *Inventory Control*, Eq. (4.6). -/
noncomputable def eoqCostFinite (A d h p Q : ℝ) : ℝ := Q * (1 - d / p) / 2 * h + d / Q * A

/-- The optimal batch quantity under a finite production rate `p > d`,
`√(2Ad / (h(1 - d/p)))`. Axsäter, *Inventory Control*, Eq. (4.7). -/
noncomputable def eoqFinite (A d h p : ℝ) : ℝ := Real.sqrt (2 * A * d / (h * (1 - d / p)))

end InventoryControl


