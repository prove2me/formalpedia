-- Prove2me | Definitions.Def_CondBasedProd_CountingProcess
-- name    : CondBasedProd_CountingProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:53.276561+00:00
-- url     : https://prove2.me/theorems/d54b1f3e-37f1-408f-bd36-4aaf74faf902
-- title:
--   A counting process with history-dependent intensity, driven by exponential clocks
-- statement:
--   An **intensity rule** $\iota$ gives the intensity $\iota(j,v,\tau)$ at elapsed time $v$ after $j$ events at times $\tau=(\tau_1,\dots,\tau_j)$. Given clock values $E_0,E_1,\dots$, the $(j+1)$-st event occurs at
--   $$
--   \tau_{j+1}=\inf\Bigl\{v\ge\tau_j:\ \int_{(\tau_j,v]}\iota(j,w,\tau)^+\,dw\ge E_j\Bigr\},
--   $$
--   and never, if the set is empty. The file defines the cumulative intensity, the next event, the event history, the event times (with value $\top$ for events that never occur), and the number of events in $[0,t]$ when only the first $n$ clocks are used.
--
--   This is the construction of a counting process by time change. With i.i.d. $\mathrm{Exp}(1)$ clocks (the published `GVRPricing.FixedPrice.clockLaw`) it yields the process with the given intensity. It refers to no production model and may be reused for any controlled pure-birth process.
--
--   **Formalization Note** The construction follows `GVRPricing.FixedPrice.Policy`, whose type is tied to that paper's pricing model and so is not reused; `lastTime` and `clockLaw` are.
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, §3, p.8 (Poisson deterioration with controlled rate); construction after the published GVRPricing_FixedPrice_SalesProcess

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory Set
open scoped ENNReal
open GVRPricing.FixedPrice (lastTime)

namespace CondBasedProd

/-- A history-dependent **intensity rule**: `ι j v τ` is the intensity at elapsed time `v` after
`j` events at times `τ = (τ₁, …, τ_j)`. Nothing here refers to the production model. -/
abbrev IntensityRule := (j : ℕ) → ℝ → (Fin j → ℝ) → ℝ

namespace CountingProcess

/-- The cumulative intensity `∫_{(τ_j, v]} ι_w dw` since the last event, in `[0, ∞]`. -/
noncomputable def cumIntensity (ι : IntensityRule) (j : ℕ) (τ : Fin j → ℝ) (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in Ioc (lastTime j τ) v, ENNReal.ofReal (ι j w τ)

open Classical in
/-- The time of the `(j+1)`-st event given the first `j` event times `τ` and the clock value `e`:
the first `v ≥ τ_j` at which the cumulative intensity since `τ_j` reaches `e`, or `none` if it
never does. -/
noncomputable def nextEvent (ι : IntensityRule) (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) : Option ℝ :=
  if {v : ℝ | lastTime j τ ≤ v ∧ ENNReal.ofReal e ≤ cumIntensity ι j τ v}.Nonempty then
    some (sInf {v : ℝ | lastTime j τ ≤ v ∧ ENNReal.ofReal e ≤ cumIntensity ι j τ v})
  else none

/-- The event history driven by the clocks `E`: `history ι E j = some τ` with `τ` the first `j`
event times if at least `j` events ever occur, and `none` otherwise. The `(j+1)`-st event uses the
clock `E j`. -/
noncomputable def history (ι : IntensityRule) (E : ℕ → ℝ) : (j : ℕ) → Option (Fin j → ℝ)
  | 0 => some Fin.elim0
  | j + 1 => (history ι E j).bind fun τ =>
      (nextEvent ι j τ (E j)).map fun v => Fin.snoc (α := fun _ => ℝ) τ v

/-- `eventTime ι E j` is the time `τ_j` of the `j`-th event (`τ₀ = 0`), and `⊤` if fewer than `j`
events ever occur. -/
noncomputable def eventTime (ι : IntensityRule) (E : ℕ → ℝ) (j : ℕ) : WithTop ℝ :=
  (history ι E j).elim ⊤ fun τ => ((lastTime j τ : ℝ) : WithTop ℝ)

open Classical in
/-- The number of events in `[0, t]` when only the first `n` clocks are used. -/
noncomputable def eventsBy (ι : IntensityRule) (n : ℕ) (t : ℝ) (E : ℕ → ℝ) : ℕ :=
  ((Finset.range n).filter fun j => eventTime ι E (j + 1) ≤ ((t : ℝ) : WithTop ℝ)).card

end CountingProcess

end CondBasedProd


