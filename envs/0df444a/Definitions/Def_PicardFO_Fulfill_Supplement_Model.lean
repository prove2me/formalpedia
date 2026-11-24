-- Prove2me | Definitions.Def_PicardFO_Fulfill_Supplement_Model
-- name    : PicardFO_Fulfill_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:05:39.279222+00:00
-- url     : https://prove2.me/theorems/fcd39055-7a58-4436-889f-4f711e9716b8
-- title:
--   OWMR numerical states, immediate lost-sales dynamics and feasible actions (12)
-- statement:
--   There are $N$ retailers and one warehouse. A disturbance $w$ identifies an active retailer $n(w)$ and demand $d(w)$; it may contain any other exogenous data. The real state $x$ has warehouse coordinate $x_0$ and retailer coordinates $x_n$. Upper storage limits are $c_0,c_n$. An action $(u,q)$ gives the numerical warehouse replenishment and active retailer request. Write $z^+=\max(z,0)$. Immediate replenishments give
--   $$
--   x'_0=(x_0-q)^++u,\qquad x'_{n(w)}=(x_{n(w)}-d(w))^++\min(q,x_0),\qquad x'_n=x_n\ (n\ne n(w)).
--   $$
--   Feasible numerical actions are nonnegative and obey the local requested-stock inequality and warehouse upper storage bound. The zero action is always feasible. The general controlled system is the existing published System, instantiated with these dynamics; it is not redefined.
--
--   **Formalization Note** The raw stock carrier is real-valued and total, even for negative or over-capacity coordinates. Validity imposes only the printed upper bounds. Feasibility explicitly admits zero on raw invalid inputs to meet the general System interface. The admissible policy conditions are in the separate Policy item.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 14, Appendix B.1, eq. (12)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Picard

namespace PicardFO.Fulfill.Supplement

/-- Real-valued OWMR state; no lower bound is imposed on the raw carrier. -/
structure Stock (N : ℕ) where
  warehouse : ℝ
  retailer : Fin N → ℝ

/-- Numerical replenishment quantities: warehouse first, active retailer second. -/
abbrev Action := ℝ × ℝ

/-- Appendix B.1 data. The disturbance can contain arbitrary exogenous information. -/
structure Model (N : ℕ) (Ω : Type*) where
  retailer : Ω → Fin N
  demand : Ω → ℝ
  warehouseCap : ℝ
  retailerCap : Fin N → ℝ

namespace Model
variable {N : ℕ} {Ω : Type*}

/-- Exactly the printed upper storage constraints; negative initial coordinates are not excluded. -/
def Valid (D : Model N Ω) (x : Stock N) : Prop :=
  x.warehouse ≤ D.warehouseCap ∧ ∀ n, x.retailer n ≤ D.retailerCap n

/-- Equation (12), with immediate replenishment and lost sales. -/
def transition (D : Model N Ω) (x : Stock N) (a : Action) (w : Ω) : Stock N :=
  ⟨max (x.warehouse - a.2) 0 + a.1,
    fun n => if n = D.retailer w then
      max (x.retailer n - D.demand w) 0 + min a.2 x.warehouse
    else x.retailer n⟩

/-- Numeric feasibility includes the local request constraint and warehouse storage constraint.
The zero action is explicitly always feasible, including on raw invalid inputs. -/
def Feasible (D : Model N Ω) (x : Stock N) (w : Ω) (a : Action) : Prop :=
  a = (0, 0) ∨ (0 ≤ a.1 ∧ 0 ≤ a.2 ∧
    max (x.retailer (D.retailer w) - D.demand w) 0 + a.2 ≤
      D.retailerCap (D.retailer w) ∧
    max (x.warehouse - a.2) 0 + a.1 ≤ D.warehouseCap)

/-- Instantiate the published general System; its algorithm is not redeclared. -/
def system (D : Model N Ω) : PicardFO.Fulfill.System (Stock N) Action Ω where
  feasible := D.Feasible
  aPhi := (0, 0)
  aPhi_feasible := fun _ _ => Or.inl rfl
  f := D.transition

end Model
end PicardFO.Fulfill.Supplement


