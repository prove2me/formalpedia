-- Prove2me | Definitions.Def_MCPoise_MultirootLP
-- name    : MCPoise_MultirootLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:47.685105+00:00
-- url     : https://prove2.me/theorems/58e11907-8534-46c7-8b6a-de44eef2e3c8
-- title:
--   Feasibility for Multiroot-LP
-- statement:
--   Given roots $r_1, \dots, r_\mu$, terminal sets $S_j$, parameters $L_\Delta$ and $L'_d$, and the set $P^j_t$ of $r_j$-$t$ paths of length at most $L'_d$, a pair $(\hat x, \hat f)$ is **feasible for Multiroot-LP** when
--   $$\sum_{e \in \delta(v)} \sum_j \hat x_{e,j} \le L_\Delta, \qquad \sum_{p \in P^j_t : e \in p} \hat f_p \le \hat x_{e,j}, \qquad \sum_{p \in P^j_t} \hat f_p = 1 \ (t \in S_j),$$
--   with $\hat x_{e,j}, \hat f_p \in [0, 1]$.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Multiroot-LP, p.15

import Mathlib
import Definitions.Def_MCPoise_IsPathIn

namespace MCPoise

/-- **Feasibility for Multiroot-LP.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), (Multiroot-LP), p.15, with "P^j_t to denote the set of all r_j-t paths of length at most L′_d":
```
Σ_{e∈δ(v)} Σ_{j∈[μ]} x̂_{e,j} ≤ L_∆          ∀v ∈ V
Σ_{p∈P^j_t : e∈p} f̂_p ≤ x̂_{e,j}             ∀e ∈ E, j ∈ [μ], t ∈ S_j
Σ_{p∈P^j_t} f̂_p = 1                          ∀t ∈ S_j, j ∈ [μ]
x̂_{e,j}, f̂_p ∈ [0, 1]                        ∀e ∈ E, j ∈ [μ], p ∈ ∪_{t,j} P^j_t
```
**Formalization Note.** `f j t` holds the flow variables for the terminal `t` of the group `j`; only its values on the finite
set `P^j_t` enter. -/
structure MultirootLP {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {μ : ℕ}
    (r : Fin μ → V) (S : Fin μ → Finset V) (LΔ : ℝ) (Lp : ℕ)
    (x : Sym2 V → Fin μ → ℝ) (f : Fin μ → V → List V → ℝ) : Prop where
  degree : ∀ v, ∑ e ∈ delta G v, ∑ j, x e j ≤ LΔ
  capacity : ∀ e ∈ G.edgeSet, ∀ j, ∀ t ∈ S j, pathLoad (pathSet G (r j) t Lp) (f j t) e ≤ x e j
  unit : ∀ j, ∀ t ∈ S j, ∑ᶠ p ∈ pathSet G (r j) t Lp, f j t p = 1
  x_mem : ∀ e ∈ G.edgeSet, ∀ j, 0 ≤ x e j ∧ x e j ≤ 1
  f_mem : ∀ j, ∀ t ∈ S j, ∀ p ∈ pathSet G (r j) t Lp, 0 ≤ f j t p ∧ f j t p ≤ 1

end MCPoise


