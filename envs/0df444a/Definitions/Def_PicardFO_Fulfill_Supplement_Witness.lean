-- Prove2me | Definitions.Def_PicardFO_Fulfill_Supplement_Witness
-- name    : PicardFO_Fulfill_Supplement_Witness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:08:37.878009+00:00
-- url     : https://prove2.me/theorems/707dcc4e-1b9f-4d79-bcc3-dcb5e5a413b9
-- title:
--   Concrete OWMR data witnessing failure of Theorem B.1
-- statement:
--   Take three retailers, retailer capacities $c_n=2$, warehouse capacity $c_0=5$, reorder level $s=2$ and target $S=5$. Initial warehouse inventory is $5$ and every retailer starts empty. Demand is zero, and each local policy requests $\max(2-\max(x,0),0)$, filling any valid nonnegative retailer stock to capacity. Every retailer owns its own process. The four source orders visit retailers $0,1,0,2$ in that order; later orders, if evaluated, visit retailer $2$.
--   $$
--   N=3,\quad s=2,\quad S=c_0=5,\quad c_n=2,\quad x_0=5,\quad x_n=0.
--   $$
--   These are witness data, not a replacement for the general OWMR policy class. The following counterexample certifies the policy constraints, the sequential count and the wrong numerical action at iteration $2R$.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, pp. 14–15, Appendix B.1–B.2 and Theorem B.1 (counterexample data)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Supplement_Picard

namespace PicardFO.Fulfill.Supplement

/-- Three retailers, no demand, capacity 2 each and warehouse capacity 5. -/
def witnessModel : Model 3 (Fin 3) := ⟨id, fun _ => 0, 5, fun _ => 2⟩

/-- Fill the retailer to capacity. Defined also for negative or over-capacity raw stock. -/
noncomputable def witnessPolicy : Policy 3 (Fin 3) :=
  ⟨fun _ x _ => max (2 - max x 0) 0, 2, 5⟩

/-- Initial warehouse is S, every retailer empty. -/
def witnessStock : Stock 3 := ⟨5, fun _ => 0⟩

/-- Retailer sequence 0,1,0,2; all later orders are for retailer 2. -/
def witnessOrders (t : ℕ) : Fin 3 :=
  if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 0 else 2

end PicardFO.Fulfill.Supplement


