-- Prove2me | Definitions.Def_HighVarianceRM_Instance
-- name    : HighVarianceRM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:07.070932+00:00
-- url     : https://prove2.me/theorems/d8a0976b-50b2-4882-97e2-c179cc5871ac
-- title:
--   Revenue management with a random number of customers: instance, dynamic program, Universal Fluid
-- statement:
--   This is the model of the mission. Let $\mathcal L$ and $\mathcal J$ be finite sets of resources and products. A sale of product $j$ earns $f_j$ and consumes one unit of each resource in $A_j\subseteq\mathcal L$; resource $i$ has capacity $c_i\in\mathbb Z_+$. The number of customers $D$ has an arbitrary law on $\{1,\dots,T\}$, and the customer at period $t$ wants product $j$ with probability $\lambda_{jt}$, where $\sum_{j}\lambda_{jt}=1$.
--
--   Write $\rho_t=\mathbb P\{D\ge t+1\mid D\ge t\}$. The value functions satisfy $J_{T+1}=0$ and
--
--   $$
--   J_t(x)=\sum_{j\in\mathcal J}\lambda_{jt}\,\max\Big\{f_j+\rho_t\,J_{t+1}\big(x-\sum_{i\in A_j}e_i\big),\ \rho_t\,J_{t+1}(x)\Big\},
--   $$
--
--   where the first term of the maximum is present only when $x_i\ge1$ for all $i\in A_j$. The optimal total expected revenue is $J_1(c)$.
--
--   The **Universal Fluid** is the linear program
--
--   $$
--   Z^*_{\mathrm{LP}}=\max\Big\{\sum_{t}\sum_{j}f_j\,\mathbb P\{D\ge t\}\,y_{jt}\ :\ \sum_t\sum_j\mathbf 1_{(i\in A_j)}\,y_{jt}\le c_i\ \ \forall i,\quad 0\le y_{jt}\le\lambda_{jt}\ \ \forall j,t\Big\}.
--   $$
--
--   The law of $D$ enters the objective only, not the capacity constraint. An optimal solution is a feasible $y$ whose objective dominates that of every feasible solution. The constants of the main theorem are $c_{\min}=\min_i c_i$, $L=\max_j|A_j|$ and $\theta=1-\sqrt{2\log c_{\min}/c_{\min}}$.
--
--   Every statement of this mission is about these objects.
--
--   **Formalization Note** Time periods are `Fin T`, 0-based, so `t` is the paper's period $t+1$, and `Jt 0` is $J_1$. The value functions are named `Jt` because `J` is the type of products. The dynamic program is written in the form of eq. (1), p. 18, which the paper states is equivalent to the recursion of §2: the §2 convention $J=-\infty$ at negative capacity meets $\rho_t=0$ in a product $0\cdot(-\infty)$. At $\mathbb P\{D\ge t\}=0$ the rate $\rho_t$ is undefined, and Lean's $0/0=0$ is harmless because the value at that period is multiplied by $0$. Revenues carry no sign hypothesis, as in the paper.
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, §2, p.6; §4 (Universal Fluid), p.9; Theorem 5.1, p.12; App. A, eq. (1), p.18

import Mathlib

open scoped Classical

namespace HighVarianceRM

/-- **Revenue management instance with a random number of customer arrivals.**
Bai, El Housni, Jin, Rusmevichientong, Topaloglu, Williamson, *Fluid Approximations for Revenue
Management under High-Variance Demand*, Management Science, doi:10.1287/mnsc.2023.4769, §2, p. 6.

* `R`, `J`: the finite sets of resources `𝓛` and products `𝓙`;
* `T`: the largest possible number of customers; time periods are `Fin T`;
* `A j`: the resources `A_j ⊆ 𝓛` of which a sale of product `j` consumes one unit each;
* `f j`: the revenue of product `j`;
* `lam t j`: the probability `λ_jt` that the customer at period `t` wants product `j`;
* `pD t`: the probability `P{D = t + 1}`, the law of the number of customers `D` on `{1, …, T}`;
* `c i`: the capacity of resource `i`.

**Formalization Note** Periods are 0-based: `t : Fin T` is the paper's time period `t + 1`, and
`pD t` the mass of the paper's value `t + 1`. The paper's survival rates `ρ_t` are derived from
`pD` (`Instance.surv`, `Instance.rho`). A customer arrives at each period with probability one
(p. 6), so `∑ j, lam t j = 1`. Capacities are natural numbers because the paper's state space is
`Z₊^{|𝓛|}` (p. 18). The paper puts no sign on `f`. `pD_sum` forces `T ≥ 1`, and then `lam_sum`
forces `J` to be nonempty. -/
structure Instance (R J : Type*) [Fintype J] (T : ℕ) where
  /-- The resources `A_j` used by product `j`. -/
  A : J → Finset R
  /-- The revenue `f_j`. -/
  f : J → ℝ
  /-- The request probability `λ_jt`. -/
  lam : Fin T → J → ℝ
  lam_nonneg : ∀ t j, 0 ≤ lam t j
  lam_sum : ∀ t, ∑ j, lam t j = 1
  /-- The probability `P{D = t + 1}`. -/
  pD : Fin T → ℝ
  pD_nonneg : ∀ t, 0 ≤ pD t
  pD_sum : ∑ t, pD t = 1
  /-- The capacity `c_i`. -/
  c : R → ℕ

namespace Instance

variable {R J : Type*} [Fintype J] {T : ℕ} (I : Instance R J T)

/-- **Survival function** `P{D ≥ t + 1}` of the number of customers (paper's `P{D ≥ t}` at the
paper's period `t + 1`), Bai et al., Management Science, doi:10.1287/mnsc.2023.4769, §2, p. 6.

**Formalization Note** Indexed by `ℕ`, so that `surv t = 0` for `t ≥ T` and `surv 0 = 1`. -/
noncomputable def surv (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin T => t ≤ (k : ℕ)), I.pD k

/-- **Survival rate** `ρ_t = P{D ≥ t + 1 | D ≥ t}` at the paper's period `t + 1`, Bai et al.,
Management Science, doi:10.1287/mnsc.2023.4769, §2, p. 6.

**Formalization Note** With the 0-based index, `rho t = P{D ≥ t + 2} / P{D ≥ t + 1}`. The paper's
conditional probability is undefined where `P{D ≥ t + 1} = 0`; there Lean's `0 / 0 = 0` gives
`rho t = 0`, which is harmless because `Jt t` is then multiplied by `rho (t - 1) = 0`. -/
noncomputable def rho (t : ℕ) : ℝ :=
  I.surv (t + 1) / I.surv t

/-- Product `j` can be served at the capacity vector `x`: `x_i ≥ 1` for every `i ∈ A_j`
(Bai et al., Management Science, doi:10.1287/mnsc.2023.4769, App. A, p. 18, the set `𝓤(x)`). -/
def Servable (x : R → ℕ) (j : J) : Prop :=
  ∀ i ∈ I.A j, 1 ≤ x i

/-- The capacity vector `x - ∑_{i ∈ A_j} e_i` after a sale of product `j`
(Bai et al., Management Science, doi:10.1287/mnsc.2023.4769, §2, p. 6).

**Formalization Note** Natural subtraction; it is only ever applied behind `Servable`, where it
does not truncate. -/
noncomputable def consume (x : R → ℕ) (j : J) : R → ℕ :=
  fun i => if i ∈ I.A j then x i - 1 else x i

/-- **The value functions `J_t` of the dynamic program**, Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, §2, p. 6, in the equivalent form of eq. (1), App. A, p. 18:
`Jt t x = ∑_j λ_jt max{f_j + ρ_t J_{t+1}(x - ∑_{i ∈ A_j} e_i), ρ_t J_{t+1}(x)}` when `j` can be
served at `x`, the sale branch being absent otherwise, with `J_{T+1} = 0`.

**Formalization Note** `t` is 0-based: `Jt 0` is the paper's `J₁`, and `Jt t = 0` for `t ≥ T` is the
boundary condition. The paper's §2 convention `J_t(x) = -∞` at negative `x` meets `ρ_t = 0` in a
product `0 · (-∞)`; eq. (1), which the paper states is equivalent, has no such term, so this
definition is real-valued. Per product, the maximum over `u_j ∈ {0, 1}` in eq. (1) is the
two-branch maximum written here, with `u_j = 1` allowed exactly when `j` is servable. -/
noncomputable def Jt (t : ℕ) (x : R → ℕ) : ℝ :=
  if h : t < T then
    ∑ j, I.lam ⟨t, h⟩ j *
      (if I.Servable x j then
        max (I.f j + I.rho t * Jt (t + 1) (I.consume x j)) (I.rho t * Jt (t + 1) x)
      else I.rho t * Jt (t + 1) x)
  else 0
termination_by T - t

/-- **The optimal total expected revenue** `J₁(c)`, Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, §2, p. 6, and p. 12: the value of the dynamic program at the first
period and the initial capacities. -/
noncomputable def J1 : ℝ :=
  I.Jt 0 I.c

/-- **Feasibility in the Universal Fluid**, Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, §4, p. 9: `y ≥ 0`, `∑_t ∑_j 1(i ∈ A_j) y_jt ≤ c_i` for every resource
`i`, and `y_jt ≤ λ_jt` for all `j`, `t`.

**Formalization Note** The distribution of `D` does not appear in the capacity constraint; that is
the point of the Universal Fluid. -/
structure Feasible (y : Fin T → J → ℝ) : Prop where
  nonneg : ∀ t j, 0 ≤ y t j
  capacity : ∀ i, ∑ t, ∑ j, (if i ∈ I.A j then y t j else 0) ≤ (I.c i : ℝ)
  le_lam : ∀ t j, y t j ≤ I.lam t j

/-- **Objective of the Universal Fluid**, Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, §4, p. 9: `∑_t ∑_j f_j P{D ≥ t} y_jt`.
At an optimal `y` this is the paper's `Z*_LP`. -/
noncomputable def objective (y : Fin T → J → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ j, I.f j * I.surv t * y t j

/-- **Optimal solution of the Universal Fluid**, Bai et al., Management Science,
doi:10.1287/mnsc.2023.4769, §4, p. 9: a feasible `y` whose objective dominates that of every
feasible solution. -/
def IsOptimal (y : Fin T → J → ℝ) : Prop :=
  I.Feasible y ∧ ∀ y', I.Feasible y' → I.objective y' ≤ I.objective y

/-- **`c_min = min_{i ∈ 𝓛} c_i`**, Bai et al., Management Science, doi:10.1287/mnsc.2023.4769,
Theorem 5.1, p. 12, cast to `ℝ`. -/
noncomputable def cmin [Fintype R] [Nonempty R] : ℝ :=
  ((Finset.univ.inf' Finset.univ_nonempty I.c : ℕ) : ℝ)

/-- **`L = max_{j ∈ 𝓙} |A_j|`**, Bai et al., Management Science, doi:10.1287/mnsc.2023.4769,
Theorem 5.1, p. 12, cast to `ℝ`. -/
noncomputable def L : ℝ :=
  ((Finset.univ.sup fun j => (I.A j).card : ℕ) : ℝ)

/-- **The tuning parameter** `θ = 1 - √(2 log c_min / c_min)`, natural logarithm, Bai et al.,
Management Science, doi:10.1287/mnsc.2023.4769, §5, p. 12. -/
noncomputable def theta [Fintype R] [Nonempty R] : ℝ :=
  1 - Real.sqrt (2 * Real.log I.cmin / I.cmin)

end Instance

end HighVarianceRM


