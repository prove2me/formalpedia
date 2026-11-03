-- Prove2me | Definitions.Def_RankOneBTF_nuY
-- name    : RankOneBTF_nuY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:10.479311+00:00
-- url     : https://prove2.me/theorems/84f6e38c-0b46-40a8-8bb7-15e720da9233
-- title:
--   The random variable $\nu^{y,j}_{ik}$ of (42)
-- statement:
--   For $i$ with $\bar x_i=1$ and $(j,k)\in[m]\times[l]$, define
--   $$
--   \nu^{y,j}_{ik}:=\frac{\sum_{i',k'}\bigl(\tfrac13f^{y,j}_{i'k'\to00}+\tfrac12f^{y,j}_{i'k'\to01}+\tfrac12f^{y,j}_{i'k'\to10}+f^{y,j}_{i'k'\to11}\bigr)}{\sum_{i',k'}t^{y,j}_{i'k'\to11}}
--   $$
--   if $\bar y_j=0$, $\bar z_k=1$ and $(i,j,k)\in\mathcal T$, and $\nu^{y,j}_{ik}:=0$ otherwise. Here $t^{y,j}_{i'k'\to rs}$ (resp. $f^{y,j}_{i'k'\to rs}$) equals $1$ if $\bar x_{i'}=r$, $\bar z_{k'}=s$ and $(i',j,k')\in\mathcal T$ (resp. $\in\mathcal F$), and $0$ otherwise. In the random models, $\nu^{y,j}_{ik}$ is a function of the noisy tensor.
--
--   It enters the proofs of Claims 3 and 7 through the bound (48) on its expectation.
--
--   **Formalization Note** Summing the indicators gives counts: the numerator is $\tfrac13F^{y,j}_{00}+\tfrac12(F^{y,j}_{01}+F^{y,j}_{10})+F^{y,j}_{11}$ and the denominator is $T^{y,j}_{11}$, which is at least $1$ in the nonzero case when $\bar x_i=1$.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, p.22, (42); pp.19–20 (indicators t, f)

import Mathlib
import Definitions.Def_RankOneBTF_Tx

namespace RankOneBTF

/-- The random variable `ν^{y,j}_{ik}` of (42) (arXiv:2202.07053v3, p.22), as a function of the
input tensor `G`:
```
ν^{y,j}_{ik} := Σ_{i',k'} ((1/3)f^{y,j}_{i'k'→00} + (1/2)f^{y,j}_{i'k'→01} + (1/2)f^{y,j}_{i'k'→10}
                 + f^{y,j}_{i'k'→11}) / Σ_{i',k'} t^{y,j}_{i'k'→11}
```
if `ȳ_j = 0, z̄_k = 1, (i,j,k) ∈ 𝒯`, and `ν^{y,j}_{ik} := 0` otherwise. Here
`t^{y,j}_{i'k'→rs}` (resp. `f^{y,j}_{i'k'→rs}`) is `1` if `x̄_{i'} = r, z̄_{k'} = s` and
`(i',j,k') ∈ 𝒯` (resp. `∈ ℱ`), and `0` otherwise (pp.19–20). The paper defines it for `i` with
`x̄_i = 1`.

**Formalization Note** Summing the indicators gives the counts of p.16: the numerator is
`(1/3)F^{y,j}_{00} + (1/2)(F^{y,j}_{01} + F^{y,j}_{10}) + F^{y,j}_{11}` (`phiY`) and the
denominator is `T^{y,j}_{11}` (`Ty … true true j`), which is at least `1` when `x̄_i = 1` and the
case condition holds. -/
noncomputable def nuY {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : ℝ := by
  classical
  exact if yb j = false ∧ zb k = true ∧ IsT xb yb zb G i j k then
    phiY xb yb zb G j / Ty xb yb zb G true true j
  else 0

end RankOneBTF


