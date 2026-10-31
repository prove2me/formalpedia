-- Prove2me | Definitions.Def_MWMSLagrange_IsSLaBSRun
-- name    : MWMSLagrange_IsSLaBSRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:37.748986+00:00
-- url     : https://prove2.me/theorems/64473eb3-9503-4027-a4fb-cf05061fe7be
-- title:
--   A run of SLaBS (Algorithm 1, step 3)
-- statement:
--   A feasible policy is a **run of SLaBS** with levels $y^*_{i,t}$ and allocation $\rho^*_{i,j}$ if, on every sample path, in every period $t$ and at every warehouse $j$, with $I_{i,t}$ the stores' actual on-hand inventory and $R_{j,t}=C_j-\sum_{s<t}\sum_{i\in\mathcal N_j}z_{i,j,s}$ the inventory left in $j$, each store $i\in\mathcal N_j$ requests $q_{i,j,t}=\rho^*_{i,j}(y^*_{i,t}-I_{i,t})^+$ and
--
--   1. if $\sum_{i\in\mathcal N_j}q_{i,j,t}\le R_{j,t}$, warehouse $j$ ships $z_{i,j,t}=q_{i,j,t}$ to every $i\in\mathcal N_j$;
--   2. otherwise it splits what is left: $0\le z_{i,j,t}\le q_{i,j,t}$ and $\sum_{i\in\mathcal N_j}z_{i,j,t}=R_{j,t}$, after which $j$ is empty.
--
--   Other warehouses keep shipping their own requests "as if all warehouses have unlimited inventory".
--
--   **Formalization Note** Every split in case 2 is allowed, since the page leaves the split arbitrary; the proportional split of the numerical study is one instance. No store receives more than it requested.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), Algorithm 1, step 3, p.13

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_FeasiblePolicy
import Definitions.Def_MWMSLagrange_onHand

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), Algorithm 1, step 3, p.13:
the feasible policy `π` is a run of SLaBS with order-up-to levels `y^*_{i,t}` and allocation
`ρ^*_{i,j}`. On every sample path `ω`, in every period `t` and at every warehouse `j`, with
`I_{i,t}` the stores' actual on-hand inventory under `π`, each store `i ∈ 𝓝_j` requests
`q_{i,j,t} = ρ^*_{i,j} (y^*_{i,t} − I_{i,t})^+` from `j`, and with `R_{j,t} = C_j − ∑_{s<t}
∑_{i∈𝓝_j} z_{i,j,s}` the inventory left in `j`:

1. if `∑_{i∈𝓝_j} q_{i,j,t} ≤ R_{j,t}`, warehouse `j` ships exactly `z_{i,j,t} = q_{i,j,t}`;
2. otherwise "split the remaining arbitrarily to each store and stop ordering from this
   warehouse": `0 ≤ z_{i,j,t} ≤ q_{i,j,t}` and `∑_{i∈𝓝_j} z_{i,j,t} = R_{j,t}` (so `j` is
   empty from then on and ships nothing more).

**Formalization Note.** Every split in case 2 is allowed (the page leaves it arbitrary; no
store receives more than it requested). Requests use the store's actual inventory, and other
warehouses keep shipping their own requests "as if all warehouses have unlimited inventory".
The conditions are imposed on every `ω`. -/
def IsSLaBSRun {M N T : ℕ} (I : Instance M N) (y : Fin N → Fin T → ℝ)
    (ρ : Fin N → Fin M → ℝ) (π : FeasiblePolicy I T) : Prop :=
  ∀ (ω : Fin N × Fin T → ℝ) (t : Fin T) (j : Fin M),
    (∑ i ∈ I.Nset j, ρ i j * max (y i t - onHand I π.z ω i t) 0
        ≤ I.C j - ∑ s : Fin T with s < t, ∑ i ∈ I.Nset j, π.z s ω i j →
      ∀ i ∈ I.Nset j, π.z t ω i j = ρ i j * max (y i t - onHand I π.z ω i t) 0) ∧
    (I.C j - ∑ s : Fin T with s < t, ∑ i ∈ I.Nset j, π.z s ω i j
        < ∑ i ∈ I.Nset j, ρ i j * max (y i t - onHand I π.z ω i t) 0 →
      (∀ i ∈ I.Nset j, 0 ≤ π.z t ω i j ∧
          π.z t ω i j ≤ ρ i j * max (y i t - onHand I π.z ω i t) 0) ∧
        ∑ i ∈ I.Nset j, π.z t ω i j = I.C j - ∑ s : Fin T with s < t, ∑ i ∈ I.Nset j, π.z s ω i j)

end MWMSLagrange


