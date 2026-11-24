-- Prove2me | Definitions.Def_HealthRefPricing_PriceCompare_Supplement_RV
-- name    : HealthRefPricing_PriceCompare_Supplement_RV
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:38:33.102909+00:00
-- url     : https://prove2.me/theorems/601ace5c-922a-41b0-b43e-61a55fd83f52
-- title:
--   Appendix C.1, Appendix p. 2 — reference pricing with variable cost share
-- statement:
--   Consider the published two-provider model, with reference price $p^*$ and patient cost share $\lambda\in(0,1]$. Reference pricing with variable cost share (RV) makes the patient pay a fraction of the price up to the reference price, and the full excess above it:
--
--   $$o^{RV}_j(p)=\lambda\min\{p_j,p^*\}+\max\{0,p_j-p^*\},\qquad V^{RV}_j(p)=m(p_j-c)S_j(o^{RV}(p)).$$
--
--   Here $S_j$ is the published multinomial-logit share determined by attributes $a_1\le a_2$, sensitivity $\gamma$, and outside-option utility $u_0$; $m$ is the patient population and $c$ the common treatment cost. An RV equilibrium is a pure Nash equilibrium, and a best response to rival price $y$ maximizes the provider's profit over its own price. These objects supply the equilibrium and best-response relations for Theorem 5 and Assumption 5.
--
--   **Formalization Note** The published generic IsPureNash and base Model are imported. Providers use `Fin 2`: index 0 is provider 1 and index 1 provider 2. Prices and deviations range over all real numbers, which leaves equilibria unchanged since prices at or below cost are strictly dominated by a price above cost. The co-payment `ct` is unused by RV. The cost-share restriction is a theorem hypothesis, not part of the formula's definition.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix p. 2 (PDF 35), Appendix C.1; §3, equations (2), (4)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare.Supplement

/-- Appendix C.1: variable cost share below the reference price, full excess above it. -/
noncomputable def oopRV (P : Params) (lam : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => lam * min (p j) P.ps + max 0 (p j - P.ps)

/-- Profit (4) under reference pricing with variable cost share. -/
noncomputable def profitRV (P : Params) (lam : ℝ) (p : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  P.m * (p j - P.c) * share P (oopRV P lam p) j

/-- Pure Nash equilibrium under RV; real prices are feasible. -/
def IsEqRV (P : Params) (lam : ℝ) (p : Fin 2 → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin 2) (strategy := fun _ => ℝ)
    (fun _ => Set.univ) (fun j q => profitRV P lam q j) p

/-- A best response to rival price `y`, using the published two-provider profile constructor. -/
def IsBestRespRV (P : Params) (lam : ℝ) (j : Fin 2) (y x : ℝ) : Prop :=
  ∀ x', profitRV P lam (vs j x' y) j ≤ profitRV P lam (vs j x y) j

end HealthRefPricing.PriceCompare.Supplement


