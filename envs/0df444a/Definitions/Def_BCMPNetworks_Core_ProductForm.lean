-- Prove2me | Definitions.Def_BCMPNetworks_Core_ProductForm
-- name    : BCMPNetworks_Core_ProductForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:41:01.558987+00:00
-- url     : https://prove2.me/theorems/0ecc504d-6619-4f4e-8a7d-dfafd9c23cbc
-- title:
--   Traffic equations and the BCMP product form $d(S)\,f_1(x_1)\cdots f_N(x_N)$
-- statement:
--   The **traffic equations** (§3.2) for relative arrival rates $e_{ir}$ are
--   $$\sum_{(i,r)} e_{ir}\,p_{i,r;j,s} + q_{js} = e_{js} \quad\text{for every pair } (j,s).$$
--
--   The **product form** is $\pi(S) = d(S)\,f_1(x_1)\cdots f_N(x_N)$, where, with $A_{irl} = \prod_{j<l} a_{irj}$ and $n_i$ the number of customers at center $i$,
--
--   1. type 1: $f_i(x_i) = (1/\mu_i)^{n_i} \prod_{j=1}^{n_i} e_{i x_{ij}}$;
--   2. type 2: $f_i(x_i) = n_i! \prod_{r}\prod_{l} \big(e_{ir}A_{irl}/\mu_{irl}\big)^{m_{irl}}/m_{irl}!$;
--   3. type 3: $f_i(x_i) = \prod_{r}\prod_{l} \big(e_{ir}A_{irl}/\mu_{irl}\big)^{m_{irl}}/m_{irl}!$;
--   4. type 4: $f_i(x_i) = \prod_{j=1}^{n_i} e_{i r_j}A_{i r_j m_j}/\mu_{i r_j m_j}$;
--
--   and $d(S) = 1$ for a closed network, $d(S) = \prod_{n=0}^{M(S)-1}\lambda(n)$ for arrival process (A), and $d(S) = \prod_{k \text{ open}} \prod_{n=0}^{M(S/E_k)-1}\lambda_k(n)$ for arrival process (B).
--
--   This is the unnormalized equilibrium distribution of the paper's THEOREM.
--
--   **Formalization Note** Three printed slips are corrected: $A_{irl}$ (p. 253) is shifted by one stage, as explained in the network definition; the type-2 factor $1/m_{ikl}!$ (p. 254) is read $1/m_{irl}!$; and the "fixed probabilities $p_{ir}$" of the $d(S)$ sentence are the arrival probabilities $q_{ir}$ of p. 250. Under process (B) the product runs over open subchains only: a closed subchain has no arrival stream, and the factor $1$ is the paper's own value for a closed network. Under process (A) the printed $\prod_{n<M(S)}\lambda(n)$ is kept even in a mixed network, where the closed-subchain customers contribute a constant factor absorbed into the normalizing constant. The traffic equations are summed over all pairs $(i,r)$; because routing stays inside a subchain this equals the paper's sum over $(i,r)\in E_k$.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), p. 253, Section 3.2 (traffic equations); p. 254, THEOREM (f_i and d(S))

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics

namespace BCMPNetworks.Core

namespace Network

variable {N R m : ℕ} (net : Network N R m)

/-- The traffic equations of §3.2 (p. 253) for the relative arrival rates `e`:
`∑_{(i,r)} e_{ir} p_{i,r;j,s} + q_{js} = e_{js}` for every pair `(j, s)`. Since routing never
leaves a subchain, the sum over all pairs `(i, r)` equals the paper's sum over `(i,r) ∈ E_k`. -/
def TrafficEquations (e : Fin N → Fin R → ℝ) : Prop :=
  ∀ j s, ∑ i, ∑ r, e i r * net.P i r j s + net.q j s = e j s

/-- The factor `f_i(x_i)` of the product form (p. 254), with the corrected `A_{irl}`:

* type 1: `(1/μ_i)^{n_i} ∏_{j=1}^{n_i} e_{i x_{ij}}`;
* type 2: `n_i! ∏_r ∏_l (e_{ir} A_{irl} / μ_{irl})^{m_{irl}} / m_{irl}!`;
* type 3: `∏_r ∏_l (e_{ir} A_{irl} / μ_{irl})^{m_{irl}} / m_{irl}!`;
* type 4: `∏_{j=1}^{n_i} e_{i r_j} A_{i r_j m_j} / μ_{i r_j m_j}`.

A local state whose shape does not match the center type never occurs in a feasible state;
its value is irrelevant. -/
noncomputable def f (e : Fin N → Fin R → ℝ) (i : Fin N) : LocalState R (net.u i) → ℝ
  | .fcfs l => (1 / net.μ i) ^ l.length * (l.map (fun r => e i r)).prod
  | .stages v =>
      match net.type i with
      | .ps => ((∑ r, ∑ l, v r l).factorial : ℝ) *
          ∏ r, ∏ l, (e i r * net.A i r l / net.μs i r l) ^ (v r l) / ((v r l).factorial : ℝ)
      | .is =>
          ∏ r, ∏ l, (e i r * net.A i r l / net.μs i r l) ^ (v r l) / ((v r l).factorial : ℝ)
      | _ => 0
  | .lcfs l => (l.map (fun x => e i x.1 * net.A i x.1 x.2 / net.μs i x.1 x.2)).prod

open Classical in
/-- The factor `d(S)` of the product form (p. 254): `1` for a closed network;
`∏_{n=0}^{M(S)-1} λ(n)` for arrival process (A); and `∏_{k open} ∏_{n=0}^{M(S/E_k)-1} λ_k(n)`
for arrival process (B), the outer product running over the open subchains (a closed
subchain has no arrival stream and contributes the factor `1`). -/
noncomputable def d (S : net.Config) : ℝ :=
  if net.IsClosedNetwork then 1 else
  match net.arrival with
  | .total lam => ∏ n ∈ Finset.range (net.totalPop S), lam n
  | .perChain lam =>
      ∏ k ∈ Finset.univ.filter (fun k => ¬ net.IsClosedChain k),
        ∏ n ∈ Finset.range (net.chainPop S k), lam k n

/-- The unnormalized product form `π(S) = d(S) f_1(x_1) ⋯ f_N(x_N)` on the state space. -/
noncomputable def productForm (e : Fin N → Fin R → ℝ) (S : net.State) : ℝ :=
  net.d S.1 * ∏ i, net.f e i (S.1 i)

end Network

end BCMPNetworks.Core


