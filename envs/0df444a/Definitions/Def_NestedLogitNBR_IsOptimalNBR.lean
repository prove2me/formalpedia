-- Prove2me | Definitions.Def_NestedLogitNBR_IsOptimalNBR
-- name    : NestedLogitNBR_IsOptimalNBR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:38:31.271902+00:00
-- url     : https://prove2.me/theorems/24c3a563-ab4d-4785-bc1a-4e44f661962a
-- title:
--   Optimal solution of problem (4) with nested-by-revenue candidates
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   A pair $(\hat x,\hat y)$ is an optimal solution of problem (4) with the nested-by-revenue candidate assortments $\{N_{ij}:j\in N_+\}$ when it satisfies
--
--   $$
--   v_0\hat x\ge\sum_{i\in M}\hat y_i,\qquad \hat y_i\ge V_i(N_{ij})^{\gamma_i}\big(R_i(N_{ij})-\hat x\big)\ \ \forall j\in N_+,\ i\in M,
--   $$
--
--   and $\hat x\le x$ for every feasible $(x,y)$ (the objective is $\min x$). This is the hypothesis of Theorem 7.
--
--   **Formalization Note** When the problem has no optimal solution (for example $v_0=0$ and all weights $0$, where every $x$ is feasible) no pair satisfies the predicate.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), Theorem 7, p. 21 (optimal solution of problem (4), p. 12)

import Mathlib
import Definitions.Def_NestedLogitNBR_FeasibleNBR

namespace NestedLogitNBR

/-- **Optimal solution of problem (4) with nested-by-revenue candidates.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), Theorem 7, p. 21: "Let `(x̂, ŷ)` be an optimal solution to problem (4) when we solve this
problem after replacing the collection of candidate assortments `{A_it : t ∈ T_i}` in the second
set of constraints with the nested-by-revenue assortments `{N_ij : j ∈ N_+}`."

The objective of (4) is `min x` (p. 12), so `(x, y)` is optimal when it is feasible
(`FeasibleNBR`) and every feasible `(x', y')` has `x ≤ x'`.

**Formalization Note.** If the problem has no optimal solution (for example `v_0 = 0` and all
weights `0`, where every `x` is feasible), no `(x, y)` satisfies this predicate. -/
def IsOptimalNBR {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (x : ℝ)
    (y : Fin m → ℝ) : Prop :=
  FeasibleNBR v0 r v γ x y ∧ ∀ (x' : ℝ) (y' : Fin m → ℝ), FeasibleNBR v0 r v γ x' y' → x ≤ x'

end NestedLogitNBR


