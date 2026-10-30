-- Prove2me | Definitions.Def_NestedLogitNBR_FeasibleFull
-- name    : NestedLogitNBR_FeasibleFull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:37:09.597652+00:00
-- url     : https://prove2.me/theorems/bc8465c4-668f-40da-abd9-6fd6a7bcb6c4
-- title:
--   Feasibility for the full assortment linear program (3)
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Problem (3) of the paper (p. 11) is the linear program
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(S)^{\gamma_i}\big(R_i(S)-x\big)\ \ \forall S\subseteq N,\ i\in M,
--   $$
--
--   with $1+m$ variables and $1+m2^n$ constraints; its optimal value is the optimal expected revenue $Z^*$ of the assortment problem. This predicate says that $(x,y)$ satisfies every constraint of (3).
--
--   **Formalization Note** $S$ ranges over all subsets of $N$, $\emptyset$ and $N$ included; $V_i(S)^{\gamma_i}$ is taken as $0$ when $V_i(S)=0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), problem (3), p. 11

import Mathlib
import Definitions.Def_NestedLogitNBR_nestRevenue
import Definitions.Def_NestedLogitNBR_nestAttraction

namespace NestedLogitNBR

/-- **Feasibility for the full assortment linear program (3).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), problem (3), p. 11:
`min x` s.t. `v_0 x ≥ Σ_{i∈M} y_i`, `y_i ≥ V_i(S_i)^{γ_i}(R_i(S_i) − x)` for all `S_i ⊂ N`,
`i ∈ M`. "Problem (3) is a linear program with `1 + m` decision variables and `1 + m 2^n`
constraints."

`FeasibleFull v0 r v γ x y` says that `(x, y)` satisfies every constraint of (3): the first one
and, for every nest `i` and every subset `S` of the products (`∅` and `N` included), the
nest constraint.

**Formalization Note.** "`S_i ⊂ N`" is every `Finset (Fin n)`, as the count `1 + m 2^n`
shows. `V_i(S)^{γ_i}` is `nestAttraction` (value `0` when `V_i(S) = 0`), `R_i(S)` is
`nestRevenue`, both with `v_i0 = 0` (Section 4, p. 16). -/
def FeasibleFull {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (x : ℝ)
    (y : Fin m → ℝ) : Prop :=
  ∑ i, y i ≤ v0 * x ∧
    ∀ (i : Fin m) (S : Finset (Fin n)), nestAttraction v γ i S * (nestRevenue r v i S - x) ≤ y i

end NestedLogitNBR


