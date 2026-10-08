-- Prove2me | Definitions.Def_NestedLogitVariants_General_Factor
-- name    : NestedLogitVariants_General_Factor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:27:00.658725+00:00
-- url     : https://prove2.me/theorems/8707b8be-9872-40aa-b566-aaaa1de8864d
-- title:
--   p. 26 — the set whose maximum is the performance guarantee (12)
-- statement:
--   Let $M^f=\{i : v_{i0}=0\}$ be the fully-captured nests and $M^p=\{i : v_{i0}>0\}$ the partially-captured ones, and write $a\vee b=\max\{a,b\}$. The performance guarantee (12) is
--   $$
--   \beta=\max_{i\in M^f,\ j=2,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\ \vee\ \max_{i\in M^p,\ j=1,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\ \vee\ 2 .
--   $$
--   For a fully-captured nest the term with $j=1$ is not considered, since $V_i(N_{i0})=V_i(\emptyset)=0$ (p. 26). This definition is the finite set of all the numbers inside the maxima, including $2$; $\beta$ is its greatest element, so $\beta\ge2$.
--
--   **Formalization Note** `betaSet I` is the set; theorems take $\beta$ with `IsGreatest (betaSet I) β`. Under the standing assumptions every denominator that occurs is positive: $j-1\ge1$ products in $M^f$, and $v_{i0}>0$ in $M^p$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 26, expression (12)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model

namespace NestedLogitVariants.General

variable {ι : Type*} {n : ℕ}

/-- The finite set whose maximum is the factor (12) (p. 26):
`{2} ∪ {V_i(N_ij)/V_i(N_{i,j−1}) : v_{i0} = 0, j = 2, …, n}
  ∪ {V_i(N_ij)/V_i(N_{i,j−1}) : v_{i0} > 0, j = 1, …, n}`.
Fully-captured nests (`v_{i0} = 0`) skip `j = 1`, as the page does (`V_i(N_{i0}) = 0`); every
denominator that occurs is positive under the standing assumptions. -/
noncomputable def betaSet (I : Instance ι n) : Set ℝ :=
  {2} ∪
    {b | ∃ i, I.vnp i = 0 ∧ ∃ j ∈ Finset.Icc 2 n, b = V I i (nbr n j) / V I i (nbr n (j - 1))} ∪
    {b | ∃ i, 0 < I.vnp i ∧ ∃ j ∈ Finset.Icc 1 n, b = V I i (nbr n j) / V I i (nbr n (j - 1))}

end NestedLogitVariants.General


