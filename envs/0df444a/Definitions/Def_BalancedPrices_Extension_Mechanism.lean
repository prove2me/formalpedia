-- Prove2me | Definitions.Def_BalancedPrices_Extension_Mechanism
-- name    : BalancedPrices_Extension_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:33.896462+00:00
-- url     : https://prove2.me/theorems/4e39b481-5987-4bb6-b065-7e2496a913ba
-- title:
--   §2–3, pp. 547–549 — expected prices E_ṽ[p^ṽ], the posted prices δ·p with δ = α/(1 + αβ), the sequential run, utility-maximizing agents and utilities
-- statement:
--   The Bayesian layer of §2 and of Theorem 3.2.
--
--   Agent $i$'s type $v_i$ ranges over a set $V_i$ with a probability distribution $\mathcal D_i$, and $\mathcal D=\mathcal D_1\times\dots\times\mathcal D_n$. A type $w\in V_i$ values outcome $x_i$ at $\mathrm{val}_i(w,x_i)$; a type profile $\mathbf v$ determines the valuation profile $(\mathrm{val}_i(v_i,\cdot))_i$. Given a full-information pricing rule $p^{\tilde{\mathbf v}}$ for every type profile $\tilde{\mathbf v}$:
--
--   1. the **expected pricing rule** is $p_i(x_i\mid\mathbf y)=\mathbb E_{\tilde{\mathbf v}\sim\mathcal D}\bigl[p^{\tilde{\mathbf v}}_i(x_i\mid\mathbf y)\bigr]$;
--   2. the **posted pricing rule** is $\delta p$ with $$\delta=\frac{\alpha}{1+\alpha\beta};$$
--   3. the **run** of the posted-price mechanism on $\mathbf v$ approaches the agents in index order; agent $i$ is shown the partial allocation $\mathbf y$ made to the agents before it (all later agents hold $\varnothing$) and receives $\mathrm{choice}_i(v_i,\mathbf y)$. The resulting profile is $\mathbf x(\mathbf v)$;
--   4. agents are **utility maximizing** under prices $q$ if, at every feasible partial allocation $\mathbf y$, the chosen outcome has finite price and $\mathrm{val}_i(w,x_i)-q_i(x_i\mid\mathbf y)\le\mathrm{val}_i(w,c)-q_i(c\mid\mathbf y)$ for every finitely priced $x_i$, where $c=\mathrm{choice}_i(w,\mathbf y)$;
--   5. agent $i$'s **utility** in the run is $u_i(\mathbf v)=v_i(x_i(\mathbf v))-q_i(x_i(\mathbf v)\mid\mathbf x_{[i-1]}(\mathbf v))$ (quasilinear).
--
--   The choice of agent $i$ depends only on its own type and on the outcomes of earlier agents, which is what makes the mechanism online.
--
--   **Formalization Note** The expected price is a Lebesgue integral in $[0,\infty]$ against the product measure, so it is $\infty$ as soon as the full-information prices are $\infty$ on a set of positive probability (the paper's convention). The constant $\delta=\alpha/(1+\alpha\beta)$ is written into `postedPrice`. Utility maximization is required only at feasible partial allocations $\mathbf y\in\mathcal F$; at infeasible ones every non-null price may be infinite and no requirement is made. `utility` converts a price to a real number; it is used only where the price is known to be finite. Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), pp. 547–549, §2 (Pricing rules and mechanisms), Theorem 3.2

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model

namespace BalancedPrices.Extension

open MeasureTheory
open scoped ENNReal

/-- The valuation profile `(v_1, …, v_n)` determined by the type profile `v`: agent `i` with
type `v i` values outcome `xi` at `val i (v i) xi`. -/
def prof {n : ℕ} {X V : Fin n → Type*} (val : ∀ i, V i → X i → ℝ) (v : ∀ i, V i) :
    Valuation X :=
  fun i => val i (v i)

/-- The expected pricing rule `p_i(x_i | y) = E_ṽ[p^ṽ_i(x_i | y)]`, with `ṽ ∼ D = ∏_i D_i`. -/
noncomputable def expPrice {n : ℕ} {X V : Fin n → Type*} [∀ i, MeasurableSpace (V i)]
    (μ : ∀ i, Measure (V i)) (pv : (∀ i, V i) → PriceRule X) : PriceRule X :=
  fun i xi y => ∫⁻ w, pv w i xi y ∂(Measure.pi μ)

/-- The posted pricing rule `δ p` with `δ = α / (1 + α β)` and `p` the expected pricing rule. -/
noncomputable def postedPrice {n : ℕ} {X V : Fin n → Type*} [∀ i, MeasurableSpace (V i)]
    (α β : ℝ) (μ : ∀ i, Measure (V i)) (pv : (∀ i, V i) → PriceRule X) : PriceRule X :=
  fun i xi y => ENNReal.ofReal (α / (1 + α * β)) * expPrice μ pv i xi y

/-- The outcome profile `x(v)` produced by the posted-price mechanism on the type profile `v`
when agents are approached in the index order of `Fin n`: agent `i` receives
`choice i (v i) y`, where `y` is the partial allocation made so far (agents `j < i` keep their
outcomes, the others hold the null outcome). -/
noncomputable def run {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v : ∀ i, V i) : Outcome X
  | i => choice i (v i) (fun j => if j < i then run nul choice v j else nul j)
termination_by i => i.val
decreasing_by assumption

/-- Agents maximize quasilinear utility under the posted prices `q`: at every feasible partial
allocation `y`, the outcome `choice i w y` chosen by agent `i` with type `w` has a finite price
and utility `val i w xi − q_i(xi | y)` at least that of every finitely priced outcome `xi`. -/
def IsUtilMax {n : ℕ} {X V : Fin n → Type*} (F : Set (Outcome X))
    (val : ∀ i, V i → X i → ℝ) (q : PriceRule X) (choice : ∀ i, V i → Outcome X → X i) :
    Prop :=
  ∀ i w y, y ∈ F →
    q i (choice i w y) y ≠ ⊤ ∧
      ∀ xi, q i xi y ≠ ⊤ →
        val i w xi - (q i xi y).toReal ≤ val i w (choice i w y) - (q i (choice i w y) y).toReal

/-- The utility `u_i(v) = v_i(x_i(v)) − q_i(x_i(v) | x_[i−1](v))` of agent `i` in the run. -/
noncomputable def utility {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (val : ∀ i, V i → X i → ℝ) (q : PriceRule X) (choice : ∀ i, V i → Outcome X → X i)
    (v : ∀ i, V i) (i : Fin n) : ℝ :=
  val i (v i) (run nul choice v i) -
    (q i (run nul choice v i) (pre nul (run nul choice v) i)).toReal

end BalancedPrices.Extension


