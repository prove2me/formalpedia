-- Prove2me | Definitions.Def_RankOneBTF_Prop10Cond1
-- name    : RankOneBTF_Prop10Cond1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:11.110484+00:00
-- url     : https://prove2.me/theorems/eccb7db7-7170-4936-897f-cd4681762995
-- title:
--   Conditions 1–3 of Proposition 10, inequality (50) and its strict form
-- statement:
--   Let $\alpha$ be a parameter. The deterministic recovery conditions of Proposition 10 are:
--
--   1. **Condition 1.** $T^{x,y,i,j}_1\ge1$ whenever $\bar x_i=\bar y_j=1$; $T^{y,z,j,k}_1\ge1$ whenever $\bar y_j=\bar z_k=1$; $T^{x,z,i,k}_1\ge1$ whenever $\bar x_i=\bar z_k=1$.
--   2. **Condition 2.** For each $i$ with $\bar x_i=0$, $T^{x,i}_{111}\ge\alpha T^{x,i}_{11}\bar T^{y,z}_1$; for each $j$ with $\bar y_j=0$, $T^{y,j}_{111}\ge\alpha T^{y,j}_{11}\bar T^{x,z}_1$; for each $k$ with $\bar z_k=0$, $T^{z,k}_{111}\ge\alpha T^{z,k}_{11}\bar T^{x,y}_1$.
--   3. **Condition 3.** For each $(i,j,k)\in\mathcal T$ with $\bar x_i=0$, $\bar y_j=\bar z_k=1$,
--   $$
--   \min\Bigl\{T^{x,i}_{11},\ \frac{T^{x,i}_{111}}{T^{y,z,j,k}_1}\Bigr\}\ \ge\ \frac13F^{x,i}_{00}+\frac12\bigl(F^{x,i}_{01}+F^{x,i}_{10}\bigr)+F^{x,i}_{11},\qquad(50)
--   $$
--   and the same with $(x,i,n)$ replaced by $(y,j,m)$ (for $(i,j,k)\in\mathcal T$ with $\bar y_j=0$, $\bar x_i=\bar z_k=1$, with $T^{y,j}_{11}$, $T^{y,j}_{111}/T^{x,z,i,k}_1$ and $F^{y,j}$) and by $(z,k,l)$ (for $\bar z_k=0$, $\bar x_i=\bar y_j=1$, with $T^{z,k}_{11}$, $T^{z,k}_{111}/T^{x,y,i,j}_1$ and $F^{z,k}$).
--
--   The strict form of (50) and its counterparts (every $\ge$ replaced by $>$) is the hypothesis of Proposition 11 and the event $A^3$ of Claim 6; Conditions 1 and 2 are the events $A^1$, $A^2$ of Claims 4, 5.
--
--   **Formalization Note** Both counterparts of (50) are written out. Division is real division (Lean sets $a/0=0$); under Condition 1 the denominators in (50) are at least $1$.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.1, p.24, Proposition 10, Conditions 1–3, inequality (50); p.29 (strict (50)); p.31 (events A¹, A², A³)

import Mathlib
import Definitions.Def_RankOneBTF_Tx

namespace RankOneBTF

variable {n m l : ℕ}

/-- **Condition 1 of Proposition 10** (arXiv:2202.07053v3, p.24): "For each i ∈ [n], j ∈ [m]
with x̄_i = ȳ_j = 1, we have T^{x,y,i,j}_1 ≥ 1, for each j ∈ [m], k ∈ [l] with ȳ_j = z̄_k = 1,
we have T^{y,z,j,k}_1 ≥ 1 and, for each i ∈ [n], k ∈ [l] with x̄_i = z̄_k = 1, we have
T^{x,z,i,k}_1 ≥ 1." This is the event `A¹` of Claim 4 (p.31). -/
def Prop10Cond1 (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  (∀ i j, xb i = true → yb j = true → 1 ≤ Txy xb yb zb G true i j) ∧
  (∀ j k, yb j = true → zb k = true → 1 ≤ Tyz xb yb zb G true j k) ∧
  (∀ i k, xb i = true → zb k = true → 1 ≤ Txz xb yb zb G true i k)

/-- **Condition 2 of Proposition 10** with parameter `α` (arXiv:2202.07053v3, p.24): "for each
i ∈ [n] with x̄_i = 0, we have T^{x,i}_{111} ≥ αT^{x,i}_{11}T̄^{y,z}_1, for each j ∈ [m] with
ȳ_j = 0, we have T^{y,j}_{111} ≥ αT^{y,j}_{11}T̄^{x,z}_1, and for each k ∈ [l] with z̄_k = 0, we
have T^{z,k}_{111} ≥ αT^{z,k}_{11}T̄^{x,y}_1." This is the event `A²` of Claim 5 (p.31). -/
def Prop10Cond2 (α : ℝ) (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  (∀ i, xb i = false →
    α * Tx xb yb zb G true true i * TbarYZ xb yb zb G ≤ Tx3 xb yb zb G true true true i) ∧
  (∀ j, yb j = false →
    α * Ty xb yb zb G true true j * TbarXZ xb yb zb G ≤ Ty3 xb yb zb G true true true j) ∧
  (∀ k, zb k = false →
    α * Tz xb yb zb G true true k * TbarXY xb yb zb G ≤ Tz3 xb yb zb G true true true k)

/-- The left-hand side `min{T^{x,i}_{11}, T^{x,i}_{111} / T^{y,z,j,k}_1}` of inequality (50)
(arXiv:2202.07053v3, p.24). -/
noncomputable def lhs50x (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : ℝ :=
  min (Tx xb yb zb G true true i) (Tx3 xb yb zb G true true true i / Tyz xb yb zb G true j k)

/-- The left-hand side of the counterpart of (50) with `(x, i, n)` replaced by `(y, j, m)`:
`min{T^{y,j}_{11}, T^{y,j}_{111} / T^{x,z,i,k}_1}` (arXiv:2202.07053v3, p.24). -/
noncomputable def lhs50y (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : ℝ :=
  min (Ty xb yb zb G true true j) (Ty3 xb yb zb G true true true j / Txz xb yb zb G true i k)

/-- The left-hand side of the counterpart of (50) with `(x, i, n)` replaced by `(z, k, l)`:
`min{T^{z,k}_{11}, T^{z,k}_{111} / T^{x,y,i,j}_1}` (arXiv:2202.07053v3, p.24). -/
noncomputable def lhs50z (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : ℝ :=
  min (Tz xb yb zb G true true k) (Tz3 xb yb zb G true true true k / Txy xb yb zb G true i j)

/-- **Condition 3 of Proposition 10**: inequality (50) and its two counterparts
(arXiv:2202.07053v3, p.24): "For each (i,j,k) ∈ 𝒯 with x̄_i = 0, ȳ_j = z̄_k = 1, we have
min{T^{x,i}_{11}, T^{x,i}_{111}/T^{y,z,j,k}_1} ≥ (1/3)F^{x,i}_{00} + (1/2)(F^{x,i}_{01} +
F^{x,i}_{10}) + F^{x,i}_{11}. (50) Moreover, (50) holds when (x, i, n) is replaced with (y, j, m)
and (z, k, l), respectively."

**Formalization Note** The two counterparts are written out: for `(i,j,k) ∈ 𝒯` with `ȳ_j = 0`,
`x̄_i = z̄_k = 1`, `min{T^{y,j}_{11}, T^{y,j}_{111}/T^{x,z,i,k}_1} ≥ (1/3)F^{y,j}_{00} + …`; and
for `(i,j,k) ∈ 𝒯` with `z̄_k = 0`, `x̄_i = ȳ_j = 1`,
`min{T^{z,k}_{11}, T^{z,k}_{111}/T^{x,y,i,j}_1} ≥ (1/3)F^{z,k}_{00} + …`. Division is real
division (`a / 0 = 0` in Lean); under Condition 1 the denominators are at least `1`. -/
def Prop10Cond3 (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  (∀ i j k, IsT xb yb zb G i j k → xb i = false → yb j = true → zb k = true →
    phiX xb yb zb G i ≤ lhs50x xb yb zb G i j k) ∧
  (∀ i j k, IsT xb yb zb G i j k → yb j = false → xb i = true → zb k = true →
    phiY xb yb zb G j ≤ lhs50y xb yb zb G i j k) ∧
  (∀ i j k, IsT xb yb zb G i j k → zb k = false → xb i = true → yb j = true →
    phiZ xb yb zb G k ≤ lhs50z xb yb zb G i j k)

/-- Inequalities (50) **and all symmetric counterparts strictly satisfied**
(arXiv:2202.07053v3, p.29, Proposition 11; the event `A³` of Claim 6, p.31): `Prop10Cond3`
with every `≥` replaced by `>`. -/
def Ineq50Strict (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  (∀ i j k, IsT xb yb zb G i j k → xb i = false → yb j = true → zb k = true →
    phiX xb yb zb G i < lhs50x xb yb zb G i j k) ∧
  (∀ i j k, IsT xb yb zb G i j k → yb j = false → xb i = true → zb k = true →
    phiY xb yb zb G j < lhs50y xb yb zb G i j k) ∧
  (∀ i j k, IsT xb yb zb G i j k → zb k = false → xb i = true → yb j = true →
    phiZ xb yb zb G k < lhs50z xb yb zb G i j k)

end RankOneBTF


