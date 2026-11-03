-- Prove2me | Definitions.Def_RankOneBTF_gammaBar
-- name    : RankOneBTF_gammaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:19.058149+00:00
-- url     : https://prove2.me/theorems/93859b5c-4a0b-4bc3-87e3-7ab9437f9102
-- title:
--   Condition 4 of Proposition 10: $\bar\gamma_{ijk}$ and inequality (51)
-- statement:
--   For $(i,j,k)\in\mathcal T\cap\mathcal P$ and a parameter $\alpha$, define
--   $$
--   \begin{aligned}
--   \bar\gamma_{ijk}:=\frac13\Bigl(2&-\frac13\frac{n_{\bar x}}{T^{y,z,j,k}_1}-\frac13\frac{n_{\bar y}}{T^{x,z,i,k}_1}-\frac13\frac{n_{\bar z}}{T^{x,y,i,j}_1}\\
--   &-\frac{1}{\alpha\bar T^{y,z}_1}\sum_{\substack{i':\bar x_{i'}=0\\(i',j,k)\in\mathcal T}}\frac{1}{T^{x,i'}_{11}}\Bigl(\frac13F^{x,i'}_{00}+\frac12(F^{x,i'}_{01}+F^{x,i'}_{10})+F^{x,i'}_{11}\Bigr)\\
--   &-\frac{1}{\alpha\bar T^{x,z}_1}\sum_{\substack{j':\bar y_{j'}=0\\(i,j',k)\in\mathcal T}}\frac{1}{T^{y,j'}_{11}}\Bigl(\frac13F^{y,j'}_{00}+\frac12(F^{y,j'}_{01}+F^{y,j'}_{10})+F^{y,j'}_{11}\Bigr)\\
--   &-\frac{1}{\alpha\bar T^{x,y}_1}\sum_{\substack{k':\bar z_{k'}=0\\(i,j,k')\in\mathcal T}}\frac{1}{T^{z,k'}_{11}}\Bigl(\frac13F^{z,k'}_{00}+\frac12(F^{z,k'}_{01}+F^{z,k'}_{10})+F^{z,k'}_{11}\Bigr)\Bigr).
--   \end{aligned}
--   $$
--   **Condition 4 of Proposition 10** requires, for each $(i,j,k)\in\mathcal T\cap\mathcal P$,
--   $$
--   3\bar\gamma_{ijk}\ \ge\ \max\Bigl\{\frac{F^{x,i}_{11}}{T^{x,i}_{11}},\ \frac{F^{y,j}_{11}}{T^{y,j}_{11}},\ \frac{F^{z,k}_{11}}{T^{z,k}_{11}}\Bigr\}.\qquad(51)
--   $$
--   Its strict form is a hypothesis of Proposition 11 and the event $A^4$ of Claim 7.
--
--   **Formalization Note** Real division (Lean sets $a/0=0$). Under the hypotheses of Propositions 10 and 11 every denominator occurring at $(i,j,k)\in\mathcal T\cap\mathcal P$ is positive.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.1, p.25, Proposition 10, Condition 4, γ̄_ijk and inequality (51); p.29 (strict (51)); p.31 (event A⁴)

import Mathlib
import Definitions.Def_RankOneBTF_Tx

namespace RankOneBTF

variable {n m l : ℕ}

/-- The quantity `γ̄_ijk` of Condition 4 of Proposition 10, with parameter `α`
(arXiv:2202.07053v3, p.25):
```
γ̄_ijk := (1/3)( 2 − (1/3) n_x̄/T^{y,z,j,k}_1 − (1/3) n_ȳ/T^{x,z,i,k}_1 − (1/3) n_z̄/T^{x,y,i,j}_1
  − (1/(αT̄^{y,z}_1)) Σ_{i': x̄_{i'}=0, (i',j,k)∈𝒯} (1/T^{x,i'}_{11})((1/3)F^{x,i'}_{00}
        + (1/2)(F^{x,i'}_{01} + F^{x,i'}_{10}) + F^{x,i'}_{11})
  − (1/(αT̄^{x,z}_1)) Σ_{j': ȳ_{j'}=0, (i,j',k)∈𝒯} (1/T^{y,j'}_{11})(… F^{y,j'} …)
  − (1/(αT̄^{x,y}_1)) Σ_{k': z̄_{k'}=0, (i,j,k')∈𝒯} (1/T^{z,k'}_{11})(… F^{z,k'} …) ).
```
`n_x̄, n_ȳ, n_z̄` are the numbers of ones of `x̄, ȳ, z̄` (p.20).

**Formalization Note** Real division (`a / 0 = 0` in Lean). Under the hypotheses of
Propositions 10 and 11 every denominator that occurs at `(i,j,k) ∈ 𝒯 ∩ 𝒫` is positive. -/
noncomputable def gammaBar (α : ℝ) (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : ℝ :=
  (1 / 3) * (2
    - (1 / 3) * (numOnes xb / Tyz xb yb zb G true j k)
    - (1 / 3) * (numOnes yb / Txz xb yb zb G true i k)
    - (1 / 3) * (numOnes zb / Txy xb yb zb G true i j)
    - 1 / (α * TbarYZ xb yb zb G) *
        ∑ i' ∈ Finset.univ.filter (fun i' => xb i' = false ∧ IsT xb yb zb G i' j k),
          1 / Tx xb yb zb G true true i' * phiX xb yb zb G i'
    - 1 / (α * TbarXZ xb yb zb G) *
        ∑ j' ∈ Finset.univ.filter (fun j' => yb j' = false ∧ IsT xb yb zb G i j' k),
          1 / Ty xb yb zb G true true j' * phiY xb yb zb G j'
    - 1 / (α * TbarXY xb yb zb G) *
        ∑ k' ∈ Finset.univ.filter (fun k' => zb k' = false ∧ IsT xb yb zb G i j k'),
          1 / Tz xb yb zb G true true k' * phiZ xb yb zb G k')

/-- The right-hand side `max{F^{x,i}_{11}/T^{x,i}_{11}, F^{y,j}_{11}/T^{y,j}_{11},
F^{z,k}_{11}/T^{z,k}_{11}}` of inequality (51) (arXiv:2202.07053v3, p.25). -/
noncomputable def rhs51 (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : ℝ :=
  max (max (Fx xb yb zb G true true i / Tx xb yb zb G true true i)
           (Fy xb yb zb G true true j / Ty xb yb zb G true true j))
      (Fz xb yb zb G true true k / Tz xb yb zb G true true k)

/-- **Condition 4 of Proposition 10** with parameter `α` (arXiv:2202.07053v3, p.25): for each
`(i,j,k) ∈ 𝒯 ∩ 𝒫`, `3γ̄_ijk ≥ max{F^{x,i}_{11}/T^{x,i}_{11}, F^{y,j}_{11}/T^{y,j}_{11},
F^{z,k}_{11}/T^{z,k}_{11}}` (51). -/
def Prop10Cond4 (α : ℝ) (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  ∀ i j k, IsT xb yb zb G i j k → xb i = true → yb j = true → zb k = true →
    rhs51 xb yb zb G i j k ≤ 3 * gammaBar α xb yb zb G i j k

/-- Inequalities (51) **strictly satisfied** (arXiv:2202.07053v3, p.29, Proposition 11; the
event `A⁴` of Claim 7, p.31): for each `(i,j,k) ∈ 𝒯 ∩ 𝒫`,
`3γ̄_ijk > max{F^{x,i}_{11}/T^{x,i}_{11}, F^{y,j}_{11}/T^{y,j}_{11}, F^{z,k}_{11}/T^{z,k}_{11}}`. -/
def Ineq51Strict (α : ℝ) (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  ∀ i j k, IsT xb yb zb G i j k → xb i = true → yb j = true → zb k = true →
    rhs51 xb yb zb G i j k < 3 * gammaBar α xb yb zb G i j k

end RankOneBTF


