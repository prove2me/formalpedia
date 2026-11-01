-- Prove2me | Definitions.Def_CloudCostOpt_System
-- name    : CloudCostOpt_System
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:27.295359+00:00
-- url     : https://prove2.me/theorems/56cd5227-3bd3-4fd0-be25-0cd9ac9c9a7f
-- title:
--   Data of the cloud cost model: order types, resource types, deadlines, steps, costs, success probabilities
-- statement:
--   There are $I$ types of orders, indexed by $i$, and $J+1$ types of resources, indexed by $j=0,1,\dots,J$; resource type $0$ is a dummy resource that models the idling of an order. The model data are:
--
--   1. for every order type $i$: the deadline offset $\delta_i\in\mathbb N$ (an order arriving in period $t$ is due at the end of period $t+\delta_i$), the number of steps $L_i\in\mathbb N$, and the waiting cost $W_i$ charged in every period in which the order is late;
--   2. for every pair $(i,j)$: the probability $\beta_{i,j}$ that one period of service on resource type $j$ completes the current step of a type-$i$ order;
--   3. for every real resource type $j=1,\dots,J$: the reserved price $R_j$ and the on-demand price $V_j$ per resource per period.
--
--   This structure carries everything except the arrival rates $\lambda=(\lambda_1,\dots,\lambda_I)$, which are passed separately so that the demand scaling $\lambda\mapsto\theta\lambda$ of Corollary 6 changes nothing else.
--
--   **Formalization Note** Order types are `Fin I`, resource types `Fin (J+1)` with `0` the dummy. The price vectors are indexed by `Fin J`; index `j` stands for resource type `j+1`. The standing assumptions on the data are the separate definition `Standing`.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, pp.3–4 ("There are I types of orders …", Resources, Orders, Service Process)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The data of the cloud cost model** (§1, pp.3–4).

There are `I` order types `i : Fin I` and `J + 1` resource types `j : Fin (J + 1)`; type `0` is the
dummy resource that models idling.  A type-`i` order has deadline `δ i` periods after its arrival
period, consists of `L i` steps, and costs `W i` per period once it is late.  A type-`j` resource
completes the current step of a type-`i` order with probability `β i j`.  A reserved resource of
real type `j + 1` costs `R j` per period, an on-demand one `V j` per period.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, pp.3–4.

Formalization Note: the arrival rates `λ i` are not part of this structure; they are passed
separately (`lam : Fin S.I → ℝ≥0`) so that demand scaling `λ ↦ θ • λ` changes nothing else.
The cost vectors `R V : Fin J → ℝ` are indexed by the real resources `1, …, J`: index `j : Fin J`
is resource type `j.succ : Fin (J + 1)`; the paper's `R₀ = 0` is `resCost`.  The standing
assumptions are in `Standing`. -/
structure System where
  /-- number of order types -/
  I : ℕ
  /-- number of real resource types (type `0` is the dummy) -/
  J : ℕ
  /-- deadline offset `δᵢ` -/
  δ : Fin I → ℕ
  /-- number of steps `Lᵢ` -/
  L : Fin I → ℕ
  /-- waiting cost per late period `Wᵢ` -/
  W : Fin I → ℝ
  /-- step success probability `β_{i,j}` -/
  β : Fin I → Fin (J + 1) → ℝ
  /-- reserved cost per period `R_j` of resource `j.succ` -/
  R : Fin J → ℝ
  /-- on-demand cost per period `V_j` of resource `j.succ` -/
  V : Fin J → ℝ

end CloudCostOpt


