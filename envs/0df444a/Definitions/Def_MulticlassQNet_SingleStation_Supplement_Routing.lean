-- Prove2me | Definitions.Def_MulticlassQNet_SingleStation_Supplement_Routing
-- name    : MulticlassQNet_SingleStation_Supplement_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:28:34.179623+00:00
-- url     : https://prove2.me/theorems/94290d22-95ad-4612-ab76-85bdd4baacf7
-- title:
--   §5 — routing-and-sequencing policies, their Markov chain, Assumption A, and the moments u_r, D_rr', G_rr'j, I_rj of (32)–(35)
-- statement:
--   Fix open network data as in §2: stations $1,\dots,N$, classes $1,\dots,R$, the station $\sigma(r)$ of each class, external Poisson arrival rates $\lambda_{0r}\ge0$ and exponential service rates $\mu_r>0$. In §5 the routing probabilities are no longer given; for each class $r$ a set $F_r$ of allowed **routing targets** is given, where a target is a class $s$ or the exit (index $0$).
--
--   A **routing-and-sequencing policy** decides, as a function of the current state $\vec n=(n_1,\dots,n_R)$,
--
--   1. which classes are in service (at most one class per single-server station, only classes with a job present; idling and preemption are allowed), as for the sequencing policies of §2; and
--   2. for each class $r$ a probability distribution $p_{r\cdot}(\vec n)$ over the targets, supported on $F_r$: after a class-$r$ service completion the job becomes class $s$ with probability $p_{rs}(\vec n)$ or leaves with probability $p_{r0}(\vec n)$.
--
--   The state then evolves as a continuous-time Markov chain. **Assumption A** requires that this chain have a unique invariant distribution and that $E[n_r^2]<\infty$ for every class $r$ under it. With $B_r$ the event that station $\sigma(r)$ serves a class-$r$ job and expectations under the invariant distribution, the variables of (32)–(35) are
--
--   $$u_r=E[1\{B_r\}],\quad D_{rr'}=E[1\{B_r\}p_{rr'}],\quad G_{rr'j}=E[1\{B_r\}p_{rr'}n_j],\quad I_{rj}=E[1\{B_r\}n_j],$$
--
--   with $r'$ ranging over the classes and the exit.
--
--   These objects are the setting of Theorem 5.1, which gives a polyhedron containing every achievable vector $(n_r,u_r,D_{rr'},G_{rr'j},I_{rj})$.
--
--   **Formalization Note** The policy extends the published `MulticlassQNet.FirstOrder.Policy` (its `serve` field) by `route n r d`, where a target `d : Option (Fin R)` is `some s` for class `s` and `none` for the exit. `F r : Finset (Option (Fin R))` therefore states whether exit is allowed for class `r`. The fixed routing matrix `net.p` of the network record is not used in this section. Expectations are `tsum`s over the countable state space $\mathbb N^R$, and global balance is stated as in the published `IsInvariant`.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), pp. 22–23, §5, Eqs. (32)–(35); Assumption A, p. 7

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- A Markovian routing-and-sequencing policy (§5, pp. 22–23) on the network data `net`, with
allowed routing sets `F r`. A routing target is an `Option (Fin R)`: `some s` is class `s`,
`none` is the exit (the paper's index `0`). The policy extends a sequencing policy (`serve`, as
in §2) by a routing distribution `route n r` over the targets, chosen as a function of the
current state `n`: after a class-`r` service completion in state `n` the job goes to target `d`
with probability `route n r d`. The distribution is supported on `F r`. The fixed routing
matrix `net.p` is not used in this section. -/
structure RoutingPolicy {N R : ℕ} (net : Network N R) (F : Fin R → Finset (Option (Fin R)))
    extends Policy net where
  route : (Fin R → ℕ) → Fin R → Option (Fin R) → ℝ
  route_nonneg : ∀ n r d, 0 ≤ route n r d
  route_sum_one : ∀ n r, ∑ d, route n r d = 1
  route_supp : ∀ n r d, d ∉ F r → route n r d = 0

namespace RoutingPolicy

variable {N R : ℕ} {net : Network N R} {F : Fin R → Finset (Option (Fin R))}
  (P : RoutingPolicy net F)

/-- The generator of the controlled chain `n(t)`: class-`r` arrivals at rate `λ_{0r}`; if class
`r` is in service, completions at rate `μ_r`, after which the job becomes class `s` with
probability `route n r (some s)` or leaves with probability `route n r none`. -/
noncomputable def generator (g : (Fin R → ℕ) → ℝ) (n : Fin R → ℕ) : ℝ :=
  ∑ r, net.lam0 r * (g (n + unitVec r) - g n) +
  ∑ r, P.toPolicy.busy n r * net.μ r *
    (∑ s, P.route n r (some s) * (g (n - unitVec r + unitVec s) - g n) +
      P.route n r none * (g (n - unitVec r) - g n))

/-- `π` is an invariant distribution of the controlled chain (global balance). -/
def IsInvariant (π : (Fin R → ℕ) → ℝ) : Prop :=
  (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧
    ∀ m : Fin R → ℕ, HasSum (fun n => π n * P.generator (fun k => if k = m then 1 else 0) n) 0

/-- Assumption A (p. 7) for the routing-and-sequencing policy: `π` is the unique invariant
distribution of its chain, and `E_π[n_r²] < ∞` for every class `r`. -/
def AssumptionA (π : (Fin R → ℕ) → ℝ) : Prop :=
  P.IsInvariant π ∧ (∀ π', P.IsInvariant π' → π' = π) ∧
    ∀ r, Summable (fun n => π n * ((n r : ℝ)) ^ 2)

/-- `u_r = E[1{B_r}]`, Eq. (32). -/
noncomputable def u (π : (Fin R → ℕ) → ℝ) (r : Fin R) : ℝ :=
  ∑' n, π n * P.toPolicy.busy n r

/-- `D_{rd} = E[1{B_r} p_{rd}]`, Eq. (33); `d = none` is the exit index `0`. -/
noncomputable def D (π : (Fin R → ℕ) → ℝ) (r : Fin R) (d : Option (Fin R)) : ℝ :=
  ∑' n, π n * P.toPolicy.busy n r * P.route n r d

/-- `G_{rdj} = E[1{B_r} p_{rd} n_j]`, Eq. (34); `d = none` is the exit index `0`. -/
noncomputable def G (π : (Fin R → ℕ) → ℝ) (r : Fin R) (d : Option (Fin R)) (j : Fin R) : ℝ :=
  ∑' n, π n * P.toPolicy.busy n r * P.route n r d * (n j : ℝ)

/-- `I_{rj} = E[1{B_r} n_j]`, Eq. (35). -/
noncomputable def I (π : (Fin R → ℕ) → ℝ) (r j : Fin R) : ℝ :=
  ∑' n, π n * P.toPolicy.busy n r * (n j : ℝ)

end RoutingPolicy

end MulticlassQNet.SingleStation.Supplement


