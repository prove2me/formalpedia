-- Prove2me | Definitions.Def_HealthRefPricing_PriceCompare_Supplement_ERP
-- name    : HealthRefPricing_PriceCompare_Supplement_ERP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:38:03.99594+00:00
-- url     : https://prove2.me/theorems/3213a6e6-f5de-47d2-a934-2edcbf79fe43
-- title:
--   §6.1, p. 20 — endogenous reference pricing game
-- statement:
--   Consider two providers with common treatment cost $c$, patient population $m$, price sensitivity $\gamma$, attributes $a_1\le a_2$, outside-option utility $u_0$, and co-payment $\tilde c$. Reuse the published multinomial-logit share $S_j(o)=e^{a_j-\gamma o_j}/(e^{u_0}+\sum_k e^{a_k-\gamma o_k})$. Under endogenous reference pricing (ERP), the reference price is the lower of the providers' prices:
--
--   $$r(p)=\min\{p_1,p_2\},\qquad o^{ERP}_j(p)=\tilde c+\max\{0,p_j-r(p)\},\qquad V^{ERP}_j(p)=m(p_j-c)S_j(o^{ERP}(p)).$$
--
--   An ERP equilibrium is a pure Nash equilibrium of this simultaneous price game. Each unilateral deviation changes the reference price as well as the deviating provider's price. These definitions supply the game of Theorem 3, rather than a system of stationary equations.
--
--   **Formalization Note** The published Params, Standing, share and generic IsPureNash are imported. Providers use `Fin 2`: index 0 is provider 1 and index 1 is provider 2. Prices and deviations range over all real numbers; equilibria have prices above cost because a price at or below cost earns nonpositive profit whereas every price above cost earns positive profit. The stored exogenous reference price `ps` is unused. Assumption 3 is not built into the game.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 20 (PDF 21), §6.1; §3, equations (2), (4)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare.Supplement

/-- §6.1: the reference price changes with the deviating price profile. -/
noncomputable def oopERP (P : Params) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => P.ct + max 0 (p j - min (p 0) (p 1))

/-- Profit (4) with the endogenous-reference out-of-pocket rule. -/
noncomputable def profitERP (P : Params) (p : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  P.m * (p j - P.c) * share P (oopERP P p) j

/-- Pure Nash equilibrium with all real prices feasible. -/
def IsEqERP (P : Params) (p : Fin 2 → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin 2) (strategy := fun _ => ℝ)
    (fun _ => Set.univ) (fun j q => profitERP P q j) p

end HealthRefPricing.PriceCompare.Supplement


