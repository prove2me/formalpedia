-- Prove2me | Definitions.Def_NestedLogitNBR_FeasibleNBR
-- name    : NestedLogitNBR_FeasibleNBR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:37:52.038309+00:00
-- url     : https://prove2.me/theorems/b0f24cd5-5f18-422b-974d-075fdf654437
-- title:
--   Feasibility for problem (4) with the nested-by-revenue candidates
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Problem (4) (p. 12), with its candidate assortments replaced by the nested-by-revenue assortments as in Theorem 7 (p. 21), is the linear program
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(N_{ij})^{\gamma_i}\big(R_i(N_{ij})-x\big)\ \ \forall j\in N_+,\ i\in M,
--   $$
--
--   with $1+m(1+n)$ constraints. This predicate says that $(x,y)$ satisfies every constraint.
--
--   **Formalization Note** $V_i(S)^{\gamma_i}$ is taken as $0$ when $V_i(S)=0$, so the constraint for $N_{i0}=\emptyset$ reads $y_i\ge0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), problem (4), p. 12, with {A_it} replaced by {N_ij : j ∈ N_+} as in Theorem 7, p. 21

import Mathlib
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_nestRevenue
import Definitions.Def_NestedLogitNBR_nestAttraction

namespace NestedLogitNBR

/-- **Feasibility for problem (4) with the nested-by-revenue assortments as candidates.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), problem (4), p. 12: `min x` s.t. `v_0 x ≥ Σ_{i∈M} y_i`,
`y_i ≥ V_i(S_i)^{γ_i}(R_i(S_i) − x)` for all `S_i ∈ {A_it : t ∈ T_i}`, `i ∈ M`; Theorem 7
(p. 21) solves it "after replacing the collection of candidate assortments `{A_it : t ∈ T_i}` in
the second set of constraints with the nested-by-revenue assortments `{N_ij : j ∈ N_+}`".

`FeasibleNBR v0 r v γ x y` says that `(x, y)` satisfies the first constraint and, for every
nest `i` and every `j = 0, 1, …, n`, the nest constraint for `N_ij` (`nbr j`, with
`N_i0 = ∅`): `1 + m(1 + n)` constraints, as on p. 21.

**Formalization Note.** `V_i(S)^{γ_i}` is `nestAttraction` (value `0` when `V_i(S) = 0`),
`R_i(S)` is `nestRevenue`, both with `v_i0 = 0` (Section 4, p. 16). -/
def FeasibleNBR {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (x : ℝ)
    (y : Fin m → ℝ) : Prop :=
  ∑ i, y i ≤ v0 * x ∧
    ∀ (i : Fin m) (j : ℕ), j ≤ n →
      nestAttraction v γ i (nbr j) * (nestRevenue r v i (nbr j) - x) ≤ y i

end NestedLogitNBR


