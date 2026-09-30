-- Prove2me | Definitions.Def_KellyStochasticNetworks_Wardrop
-- name    : KellyStochasticNetworks_Wardrop
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T15:56:52.126268+00:00
-- url     : https://prove2.me/theorems/6fcc82cc-055d-4601-b63b-4ea40291e6ac
-- title:
--   Selfish routing: link flows, Wardrop equilibrium, and the two Braess networks
-- statement:
--   The road traffic model of Chapter 4 of Kelly and Yudovina, *Stochastic Networks*, and the two
--   networks of Braess's paradox.
--
--   A network is a set of $J$ directed links. A **route** is a subset of links, and the
--   **link-route incidence matrix** $A$ has $A_{jr} = 1$ when link $j$ belongs to route $r$ and
--   $A_{jr} = 0$ otherwise. If $x_r$ is the flow on route $r$, the **link flow** is
--   $$y_j = \sum_r A_{jr}x_r .$$
--   Each route serves exactly one **source–destination pair**, written $s(r)$, and the flow
--   requirement on pair $\sigma$ is $f_\sigma$; a flow vector is **feasible** when it is
--   non-negative and the flows on the routes serving $\sigma$ sum to $f_\sigma$.
--
--   Each link carries a **delay function** $D_j$, and the delay along route $r$ is the sum
--   $\sum_j D_j(y_j)A_{jr}$ of the delays of its links. A **Wardrop equilibrium** (Definition 4.2)
--   is a feasible $x$ such that every route carrying positive traffic has minimal delay among the
--   routes serving the same source–destination pair:
--   $$x_r > 0 \implies \sum_j D_j(y_j)A_{jr} = \min_{r' \in s(r)}\sum_j D_j(y_j)A_{jr'} .$$
--
--   Three further objects are defined. The **objective** $\sum_j \int_0^{y_j}D_j(u)\,du$ of the
--   convex program used to prove that an equilibrium exists. The **mean cost per unit time**
--   $$W(\nu;\varphi) = \sum_r w_r \sum_{j \in r}\frac{\nu_r}{\varphi_j - \lambda_j},
--     \qquad \lambda_j = \sum_{r' : j \in r'}\nu_{r'},$$
--   of the queueing network of section 4.3.1, in which a unit delay of a customer on route $r$
--   costs $w_r$ and the mean sojourn time at queue $j$ is $1/(\varphi_j - \lambda_j)$. And the two
--   road networks of **Braess's paradox**: Figure 4.4a with four links, delays $10y$, $y+50$,
--   $y+50$, $10y$ and two routes, and Figure 4.4b, the same network with an extra road of delay
--   $y+10$ added and the third route it creates.
--
--   **Formalization Note** Links, routes and source–destination pairs are indexed by finite types.
--   The map $s$ from routes to source–destination pairs replaces the book's incidence matrix $H$,
--   which carries exactly the same information since each column of $H$ sums to one. The
--   equilibrium condition is written as "the delay on $r$ is at most the delay on $r'$, for every
--   $r'$ serving the same pair", which is the displayed minimum with the minimum written out;
--   the two are equivalent because $r$ serves $s(r)$ itself. Delay functions are total functions
--   on the reals, so the vertical asymptote that Figure 4.5 permits is excluded.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 4, pp. 92-101 (PDF pp. 100-109): Braess's paradox and Figures 4.3, 4.4a, 4.4b on pp. 92-93, the network model and the link-route incidence matrix p. 94, Definition 4.2 (Wardrop equilibrium) p. 96, the optimization problem in the proof of Theorem 4.3 p. 97, and the mean cost W(nu; phi) of the queueing network p. 101. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib

namespace KellyStochasticNetworks

/-- The flow on link `j` induced by the route flows `x` and the link-route incidence matrix `A`:
`y_j = ∑_r A_{jr} x_r`.  Kelly–Yudovina, *Stochastic Networks*, p. 94. -/
def linkFlow {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ) (j : Fin J) : ℝ :=
  ∑ r, A j r * x r

/-- The feasible route flows: non-negative, and carrying exactly `f σ` between each
source-destination pair `σ`.  The map `s` sends a route to the source-destination pair it
serves, which is the book's incidence matrix `H` (whose column sums are `1`). -/
def wardropFeasible {R Sd : ℕ} (s : Fin R → Fin Sd) (f : Fin Sd → ℝ) : Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∀ σ, (∑ r ∈ Finset.univ.filter (fun r => s r = σ), x r) = f σ}

/-- **Wardrop equilibrium**, Definition 4.2: a feasible vector of route flows such that every
route carrying positive traffic has minimal delay among the routes serving the same
source-destination pair.  The delay on route `r` is `∑_j D_j(y_j) A_{jr}`, the sum of the link
delays along it. -/
def IsWardropEquilibrium {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s f ∧
    ∀ r r' : Fin R, s r' = s r → 0 < x r →
      (∑ j, D j (linkFlow A x j) * A j r) ≤ ∑ j, D j (linkFlow A x j) * A j r'

/-- The objective `∑_j ∫_0^{y_j} D_j(u) du` of the optimization problem in the proof of
Theorem 4.3. -/
noncomputable def wardropObjective {J R : ℕ} (A : Fin J → Fin R → ℝ) (D : Fin J → ℝ → ℝ)
    (x : Fin R → ℝ) : ℝ :=
  ∑ j, ∫ u in (0:ℝ)..(linkFlow A x j), D j u

/-- The mean cost per unit time `W(ν; φ)` of the queueing network of section 4.3.1: a customer
on route `r` costs `w_r` per unit delay, and the mean sojourn time at queue `j` is
`1/(φ_j - λ_j)` with `λ_j = ∑_{r : j ∈ r} ν_r`. -/
noncomputable def queueingCost {J R : ℕ} (A : Fin J → Fin R → ℝ) (w ν : Fin R → ℝ)
    (φ : Fin J → ℝ) : ℝ :=
  ∑ r, w r * ∑ j, A j r * (ν r / (φ j - ∑ r', A j r' * ν r'))

/-- Braess's paradox, Figure 4.4a: links `S→W`, `W→N`, `S→E`, `E→N` and the two routes
`{S→W, W→N}` and `{S→E, E→N}`. -/
def braessIncidenceA : Fin 4 → Fin 2 → ℝ := ![![1, 0], ![1, 0], ![0, 1], ![0, 1]]

/-- The link delays of Figure 4.4a: `10y` on `S→W` and `E→N`, `y + 50` on `W→N` and `S→E`. -/
noncomputable def braessDelayA : Fin 4 → ℝ → ℝ :=
  ![fun y => 10 * y, fun y => y + 50, fun y => y + 50, fun y => 10 * y]

/-- Braess's paradox, Figure 4.4b: the same network with the extra road `W→E` added, and the
third route `{S→W, W→E, E→N}` it creates. -/
def braessIncidenceB : Fin 5 → Fin 3 → ℝ :=
  ![![1, 0, 1], ![1, 0, 0], ![0, 1, 0], ![0, 1, 1], ![0, 0, 1]]

/-- The link delays of Figure 4.4b: those of Figure 4.4a together with `y + 10` on the new
road `W→E`. -/
noncomputable def braessDelayB : Fin 5 → ℝ → ℝ :=
  ![fun y => 10 * y, fun y => y + 50, fun y => y + 50, fun y => 10 * y, fun y => y + 10]

end KellyStochasticNetworks


