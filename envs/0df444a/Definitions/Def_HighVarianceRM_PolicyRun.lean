-- Prove2me | Definitions.Def_HighVarianceRM_PolicyRun
-- name    : HighVarianceRM_PolicyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:49.005947+00:00
-- url     : https://prove2.me/theorems/df94384a-26ce-4454-b701-99add9357250
-- title:
--   A realization of the approximate policy: capacity path, revenue, expected revenue
-- statement:
--   A **realization of the approximate policy** for a parameter $\theta$ and a fluid solution $y$ is a family of random variables on a probability space $(\Omega,\mathbb P)$: the number of customers $D$; the product $P_t$ wanted at period $t$, with $\Lambda_{jt}=\mathbf 1_{(P_t=j)}$; and the availability decisions $A_{jt}\in\{0,1\}$. Their laws are
--
--   $$
--   \mathbb P\{D=t\}\ \text{ as in the instance},\qquad \mathbb P\{\Lambda_{jt}=1\}=\lambda_{jt},\qquad \mathbb P\{A_{jt}=1\}=\theta\,\frac{y_{jt}}{\lambda_{jt}}.
--   $$
--
--   The period slices $(P_t,(A_{jt})_j)$ are independent across periods, $P_t$ is independent of $(A_{jt})_j$, and $D$ is independent of all the slices.
--
--   The remaining capacity $X_t$ starts at $c$. At period $t$ it loses $\sum_{i\in A_j}e_i$ if $j=P_t$ is available and can be served at $X_t$, and it is unchanged otherwise; it runs through all $T$ periods whatever the value of $D$. Then $G_{jt}=1$ means that product $j$ can be served at $X_t$, and the total revenue is the random variable
--
--   $$
--   \sum_{t=1}^T\sum_{j\in\mathcal J} f_j\,\mathbf 1_{(D\ge t,\ A_{jt}=1,\ \Lambda_{jt}=1,\ G_{jt}=1)} .
--   $$
--
--   Its expectation is $J_{\mathrm{App}}(c)$. The demand indicator $N_{it}$ equals $1$ when the product requested at $t$ uses resource $i$ and is available, whether or not it can be served.
--
--   The structure ties the policy to $\theta$ and $y$, so that the statements of this mission concern the paper's policy and not an arbitrary revenue process.
--
--   **Formalization Note** The fields ask for less than full independence: $A_{jt}$ for different $j$ in one period may be correlated, and every fully independent family is a run. The type of products carries a measurable structure with measurable singletons, which on a finite type is the discrete one. `req t ω = j` is $\Lambda_{jt}=1$ and `avail t j ω = true` is $A_{jt}=1$. The Lean index of `D` is 0-based, so the number of customers is `D ω + 1`, and the paper's $D\ge t$ at period $t+1$ reads `t ≤ D ω`. Availability is drawn at every period and capacity is checked at the sale, as in Appendix B.
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, §2, p.6; App. B, pp.21–22

import Mathlib
import Definitions.Def_HighVarianceRM_Instance

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace HighVarianceRM

/-- **A realization of the approximate policy** on a probability space `(Ω, P)`, for a parameter
`θ` and a fluid solution `y`. Bai et al., *Fluid Approximations for Revenue Management under
High-Variance Demand*, Management Science, doi:10.1287/mnsc.2023.4769, App. B, p. 21, and §2, p. 6.

* `D ω`: the number of customers is `D ω + 1`;
* `req t ω`: the product wanted by the customer at period `t` (so `Λ_jt = 1` means `req t ω = j`);
* `avail t j ω`: `A_jt = 1`, the policy makes product `j` available at period `t`;
* `law_D`, `law_req`, `law_avail`: `P{D = t + 1} = pD t`, `P{Λ_jt = 1} = λ_jt`,
  `P{A_jt = 1} = θ y_jt / λ_jt`;
* `indep_slices`: the period slices `(req t, avail t ·)` are independent across periods;
* `indep_req_avail`: within a period, the request is independent of the availability decisions;
* `indep_D`: `D` is independent of all the slices.

**Formalization Note** `A_jt` is drawn at every period and capacity is checked at the sale, as in
App. B; §5 draws it only when capacity is available, and the sales are the same. Period index
0-based, as in `Instance`. The paper says all these variables are independent; the three fields
ask for less (`A_jt` for different `j` in one period may be correlated), and every fully
independent family is a run. `J` carries a measurable structure with measurable singletons, which
for finite `J` is the discrete one. At `λ_jt = 0`, Lean's `0 / 0 = 0` gives `P{A_jt = 1} = 0` when
`y` is feasible, and such a product is never requested at `t`. -/
structure PolicyRun {R J : Type*} [Fintype J] [MeasurableSpace J] {T : ℕ} (I : Instance R J T)
    (θ : ℝ) (y : Fin T → J → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- The number of customers, `D ω + 1`. -/
  D : Ω → Fin T
  /-- The product wanted at period `t`. -/
  req : Fin T → Ω → J
  /-- `A_jt = 1`. -/
  avail : Fin T → J → Ω → Bool
  measurable_D : Measurable D
  measurable_req : ∀ t, Measurable (req t)
  measurable_avail : ∀ t j, Measurable (avail t j)
  law_D : ∀ t, P.real {ω | D ω = t} = I.pD t
  law_req : ∀ t j, P.real {ω | req t ω = j} = I.lam t j
  law_avail : ∀ t j, P.real {ω | avail t j ω = true} = θ * (y t j / I.lam t j)
  indep_slices : iIndepFun (fun (t : Fin T) ω => (req t ω, fun j => avail t j ω)) P
  indep_req_avail : ∀ t, IndepFun (req t) (fun ω j => avail t j ω) P
  indep_D : IndepFun D (fun ω (t : Fin T) => (req t ω, fun j => avail t j ω)) P

namespace PolicyRun

variable {R J : Type*} [Fintype J] [MeasurableSpace J] {T : ℕ} {I : Instance R J T}
  {θ : ℝ} {y : Fin T → J → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (run : PolicyRun I θ y P)

/-- **Remaining capacity** at the start of period `t` under the approximate policy: `X ω 0 = c`,
and at a period `t < T` the vector `X ω t` loses `∑_{i ∈ A_j} e_i` if `j = req t ω` is available
and servable at `X ω t`, and stays unchanged otherwise. Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, App. B, p. 21.

**Formalization Note** The path runs through all `T` periods whatever the value of `D`, because
the paper's `G_jt` "depends on the decisions of the approximate policy at time periods
1, …, t − 1" and is independent of `D`. -/
noncomputable def X (ω : Ω) : ℕ → R → ℕ
  | 0 => I.c
  | t + 1 =>
    if h : t < T then
      if run.avail ⟨t, h⟩ (run.req ⟨t, h⟩ ω) ω = true ∧
          I.Servable (X ω t) (run.req ⟨t, h⟩ ω) then
        I.consume (X ω t) (run.req ⟨t, h⟩ ω)
      else X ω t
    else X ω t

/-- **`G_jt = 1`**: there is capacity to serve a request for product `j` at period `t` under the
approximate policy. Bai et al., Management Science, doi:10.1287/mnsc.2023.4769, App. B, p. 21. -/
def G (t : Fin T) (j : J) (ω : Ω) : Prop :=
  I.Servable (run.X ω t) j

/-- **The total revenue of the approximate policy** on the sample point `ω`:
`∑_t ∑_j f_j 1(D ≥ t, A_jt = 1, Λ_jt = 1, G_jt = 1)`. Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, App. B, p. 21.

**Formalization Note** With the 0-based index, the paper's `D ≥ t` at the paper's period `t + 1`
reads `t ≤ D ω`. -/
noncomputable def revenue (ω : Ω) : ℝ :=
  ∑ t : Fin T, ∑ j,
    if t ≤ run.D ω ∧ run.avail t j ω = true ∧ run.req t ω = j ∧ run.G t j ω then I.f j else 0

/-- **`J_App(c)`, the total expected revenue of the approximate policy**: the expectation of the
revenue random variable. Bai et al., Management Science, doi:10.1287/mnsc.2023.4769, App. B, p. 21.

**Formalization Note** `revenue` takes finitely many values and is measurable, so the Bochner
integral is the true expectation (proved in `Solutions/verification/HighVarianceRM_Sanity.lean`). -/
noncomputable def JApp : ℝ :=
  ∫ ω, run.revenue ω ∂P

/-- **The demand indicator `N_it`**: there is a unit of demand for the capacity of resource `i` at
period `t`, i.e. the product requested at `t` uses `i` and is available. Bai et al., Management
Science, doi:10.1287/mnsc.2023.4769, App. B, p. 22.

**Formalization Note** The paper introduces `N_it` as "a collection of independent Bernoulli random
variables" and then uses it pathwise, jointly over the resources of a product, so it is this
indicator on the same probability space. -/
noncomputable def N (i : R) (t : Fin T) (ω : Ω) : ℕ :=
  if i ∈ I.A (run.req t ω) ∧ run.avail t (run.req t ω) ω = true then 1 else 0

end PolicyRun

end HighVarianceRM


