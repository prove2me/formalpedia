-- Prove2me | Definitions.Def_MCPoise_JunctionLPFeasible
-- name    : MCPoise_JunctionLPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:00.962119+00:00
-- url     : https://prove2.me/theorems/edde0f15-0c73-49f9-b89e-794d50d298b6
-- title:
--   Feasibility for Junction-LP
-- statement:
--   Let $L_d = (1 + \lfloor \log_2 k \rfloor) L$, let the candidate roots be the sources, $r_j = s_j$ with $M = k$, and let $P^j_t$ be the set of $r_j$-$t$ paths of $G$ of length at most $L_d$. A vector $(x, f, \lambda)$ is **feasible for Junction-LP** when
--   $$\sum_{j} x_{e,j} \le x_e \ (e \in E), \qquad \sum_{e \in \delta(v)} x_e \le L \ (v \in V),$$
--   $$\sum_{p \in P^j_t : e \in p} f_p \le x_{e,j}, \qquad \sum_{p \in P^j_t} f_p \ge \lambda_{i,j} \ (t \in \{s_i, t_i\}),$$
--   $$\sum_j \lambda_{i,j} \le 1, \qquad \sum_i \sum_j \lambda_{i,j} \ge k/2,$$
--   with all variables nonnegative.
--
--   The capacities $x_{e,j}$ bound each terminal's flow separately, not the sum over terminals.
--
--   **Formalization Note** Flow variables are labelled by the demand occurrence and its side, as the source directs when a vertex is a terminal of several demands.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Junction-LP, p.10; §2, p.9, footnote 2

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_IsPathIn

namespace MCPoise

/-- `L_d = (1 + ⌊log₂ k⌋) · L`, §2, p.9. `Nat.log 2 0 = 0`, which is unused since `k = 0` has no paths. -/
def Ld (I : Inst) (L : ℕ) : ℕ := (1 + Nat.log 2 I.k) * L

/-- `P^j_t` for `t` the terminal of the demand `i` on side `b` and the root `r_j = s_j`: the `r_j`-`t` paths of `G` of
length at most `L_d` (p.9). -/
def JP (I : Inst) (L : ℕ) (i : Fin I.k) (b : Bool) (j : Fin I.k) : Set (List (Fin I.n)) :=
  pathSet I.graph (I.s j) (I.term i b) (Ld I L)

/-- **Feasibility for Junction-LP.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), (Junction-LP), p.10, with `L_d` and `P^j_t` of p.9:
```
Σ_{j∈[M]} x_{e,j} ≤ x_e                     ∀e ∈ E
Σ_{e∈δ(v)} x_e ≤ L                          ∀v ∈ V
Σ_{p∈P^j_t : e∈p} f_p ≤ x_{e,j}             ∀e ∈ E, j ∈ [M], t ∈ ∪_{i∈[k]}{s_i, t_i}
Σ_{p∈P^j_t} f_p ≥ λ_{i,j}                   ∀i ∈ [k], t ∈ {s_i, t_i}, j ∈ [M]
Σ_{j∈[M]} λ_{i,j} ≤ 1                       ∀i ∈ [k]
Σ_{i∈[k]} Σ_{j∈[M]} λ_{i,j} ≥ k/2
x_e, x_{e,j}, λ_{i,j}, f_p ≥ 0              for all corresponding indices
```
**Formalization Note.** `M = k` and `r_j = s_j` (p.9: "we write r₁, . . . , r_M as s₁, . . . , s_k"). The flow variables
are labelled by the demand occurrence `(i, b)` and the root `j`, as footnote 2, p.9 directs when a vertex is a
terminal of several demands. `f` is a function on all vertex lists, of which only the values on `P^j_t` enter;
`P^j_t` is finite, so its `finsum`s are finite sums. -/
structure JunctionLPFeasible (I : Inst) (L : ℕ) (x : Sym2 (Fin I.n) → ℝ)
    (x' : Sym2 (Fin I.n) → Fin I.k → ℝ) (lam : Fin I.k → Fin I.k → ℝ)
    (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ) : Prop where
  sum_le : ∀ e ∈ I.graph.edgeSet, ∑ j, x' e j ≤ x e
  degree : ∀ v, ∑ e ∈ delta I.graph v, x e ≤ L
  capacity : ∀ e ∈ I.graph.edgeSet, ∀ i b j, pathLoad (JP I L i b j) (f i b j) e ≤ x' e j
  cover : ∀ i b j, lam i j ≤ ∑ᶠ p ∈ JP I L i b j, f i b j p
  lam_le : ∀ i, ∑ j, lam i j ≤ 1
  total : (I.k : ℝ) / 2 ≤ ∑ i, ∑ j, lam i j
  x_nonneg : ∀ e ∈ I.graph.edgeSet, 0 ≤ x e
  x'_nonneg : ∀ e ∈ I.graph.edgeSet, ∀ j, 0 ≤ x' e j
  lam_nonneg : ∀ i j, 0 ≤ lam i j
  f_nonneg : ∀ i b j, ∀ p ∈ JP I L i b j, 0 ≤ f i b j p

end MCPoise


