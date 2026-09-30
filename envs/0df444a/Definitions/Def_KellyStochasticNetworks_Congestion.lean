-- Prove2me | Definitions.Def_KellyStochasticNetworks_Congestion
-- name    : KellyStochasticNetworks_Congestion
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T16:35:50.652117+00:00
-- url     : https://prove2.me/theorems/026a48e9-c929-407e-a636-42f2f19ea0a8
-- title:
--   Internet congestion control: the network problem, the primal algorithm and its Lyapunov function
-- statement:
--   The congestion control model of Chapter 7 of Kelly and Yudovina, *Stochastic Networks*.
--
--   A network has $J$ resources and $R$ routes, with link-route incidence matrix $A$ ($A_{jr}=1$
--   when route $r$ uses resource $j$). A flow vector $x$ is **feasible** for
--   $\mathrm{network}(A,C;w)$ when $x\ge0$ and the induced load on each resource respects its
--   capacity, $\sum_{s:j\in s}x_s\le C_j$; the problem is to maximize the objective
--   $$\sum_r w_r\log x_r$$
--   over the feasible set, where $w_r>0$ weights route $r$.
--
--   The **primal algorithm** (7.5)–(7.6) is the differential equation
--   $$\frac{d}{dt}x_r(t)=\kappa_r\Bigl(w_r-x_r(t)\sum_{j\in r}p_j\Bigl(\sum_{s:j\in s}x_s(t)\Bigr)\Bigr),$$
--   with $\kappa_r>0$ and $p_j$ non-negative, continuous, increasing and not identically zero. It
--   is a caricature of end-to-end control: resource $j$ generates congestion signals at rate
--   $p_j(\text{load})$, these reach every user whose route passes through $j$, and the user
--   responds with a decrease proportional to the signals received plus a steady increase
--   proportional to $w_r$. Both sums are local, so no machine needs to know $A$.
--
--   Its **Lyapunov function** is
--   $$U(x)=\sum_r w_r\log x_r-\sum_j\int_0^{\sum_{s:j\in s}x_s}p_j(y)\,dy,$$
--   whose first term is the network objective and whose second penalizes resource load.
--
--   **Formalization Note** The link loads reuse the `linkFlow` of mission IV of this series, so the
--   incidence-matrix conventions of Chapters 4 and 7 agree. Flow vectors are real-valued and the
--   natural domain is the open positive orthant, since $\log x_r$ is meaningless at $x_r = 0$ and
--   the book's maximum is interior to the orthant. The drift is given as a function of the state,
--   so a trajectory is a differentiable function whose derivative equals it pointwise.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 7, pp. 153-163 (PDF pp. 161-171): the network problem network(A, C; w) p. 153, weighted proportional fairness p. 159, the primal algorithm (7.5)-(7.6) p. 162, and the Lyapunov function U(x) of Theorem 7.6 p. 163. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

/-- The feasible flow vectors of the network problem `network(A, C; w)` of section 7.1:
non-negative route rates whose induced link loads respect the capacities. -/
def networkFeasible {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ) : Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∀ j, linkFlow A x j ≤ C j}

/-- The objective `∑_r w_r log x_r` of `network(A, C; w)`. -/
noncomputable def networkObjective {R : ℕ} (w x : Fin R → ℝ) : ℝ :=
  ∑ r, w r * Real.log (x r)

/-- The utility `U(x) = ∑_r w_r log x_r - ∑_j ∫_0^{y_j} p_j(y) dy` of Theorem 7.6, where
`y_j = ∑_{s : j ∈ s} x_s` is the load on resource `j`. -/
noncomputable def primalUtility {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (x : Fin R → ℝ) : ℝ :=
  (∑ r, w r * Real.log (x r)) - ∑ j, ∫ y in (0:ℝ)..(linkFlow A x j), p j y

/-- The right-hand side of the **primal algorithm** (7.5)–(7.6):
`κ_r (w_r - x_r ∑_{j ∈ r} p_j(∑_{s : j ∈ s} x_s))`. -/
noncomputable def primalDrift {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (x : Fin R → ℝ) (r : Fin R) : ℝ :=
  κ r * (w r - x r * ∑ j, A j r * p j (linkFlow A x j))

end KellyStochasticNetworks


