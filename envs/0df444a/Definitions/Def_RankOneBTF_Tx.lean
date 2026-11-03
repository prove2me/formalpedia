-- Prove2me | Definitions.Def_RankOneBTF_Tx
-- name    : RankOneBTF_Tx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:16.550206+00:00
-- url     : https://prove2.me/theorems/6523d64b-f3be-4864-a6e3-0271c7ffad87
-- title:
--   Counting parameters $T^{x,i}_{rs}$, $F^{x,i}_{rs}$, $T^{x,y,i,j}_r$, $T^{x,i}_{rst}$, $\bar T^{x,y}_1$ and their symmetric versions
-- statement:
--   Fix the ground truth $\bar x,\bar y,\bar z$ and an input tensor $\mathcal G$, with uncorrupted set $\mathcal T$ and corrupted set $\mathcal F$. For $i\in[n]$ and $r,s\in\{0,1\}$,
--   $$
--   T^{x,i}_{rs}=\bigl|\{(j,k): \bar y_j=r,\ \bar z_k=s,\ (i,j,k)\in\mathcal T\}\bigr|,\qquad
--   F^{x,i}_{rs}=\bigl|\{(j,k): \bar y_j=r,\ \bar z_k=s,\ (i,j,k)\in\mathcal F\}\bigr|,
--   $$
--   and $F^{x,i}=F^{x,i}_{00}+F^{x,i}_{10}+F^{x,i}_{01}+F^{x,i}_{11}$. The parameters $T^{y,j}_{rs},F^{y,j}_{rs}$ (pairs $(i,k)$ with $\bar x_i=r$, $\bar z_k=s$) and $T^{z,k}_{rs},F^{z,k}_{rs}$ (pairs $(i,j)$ with $\bar x_i=r$, $\bar y_j=s$) are defined in the same way. For the flower LP,
--   $$
--   T^{x,y,i,j}_r=|\{k:\bar z_k=r,\ (i,j,k)\in\mathcal T\}|,\quad
--   T^{x,z,i,k}_r=|\{j:\bar y_j=r,\ (i,j,k)\in\mathcal T\}|,\quad
--   T^{y,z,j,k}_r=|\{i:\bar x_i=r,\ (i,j,k)\in\mathcal T\}|,
--   $$
--   $$
--   T^{x,i}_{rst}=\bigl|\{(j,k,i'): \bar y_j=r,\ \bar z_k=s,\ \bar x_{i'}=t,\ (i,j,k)\in\mathcal T,\ (i',j,k)\in\mathcal T\}\bigr|,
--   $$
--   with $T^{y,j}_{rst}$ (triples $(i,k,j')$, $\bar x_i=r,\bar z_k=s,\bar y_{j'}=t$, $(i,j,k),(i,j',k)\in\mathcal T$) and $T^{z,k}_{rst}$ likewise, and the averages
--   $$
--   \bar T^{x,y}_1=\frac1{nm}\sum_{i,j}T^{x,y,i,j}_1,\qquad \bar T^{x,z}_1=\frac1{nl}\sum_{i,k}T^{x,z,i,k}_1,\qquad \bar T^{y,z}_1=\frac1{ml}\sum_{j,k}T^{y,z,j,k}_1 .
--   $$
--   The module also fixes the weighted corruption counts $\varphi^{x,i}=\tfrac13F^{x,i}_{00}+\tfrac12(F^{x,i}_{01}+F^{x,i}_{10})+F^{x,i}_{11}$ and their $y$, $z$ versions, which appear in (50) and in $\bar\gamma_{ijk}$.
--
--   These counts are the language of the deterministic recovery conditions (Propositions 7, 10, 11) and of the probabilistic claims.
--
--   **Formalization Note** Every count is a real number (a cast cardinality); $r,s,t\in\{0,1\}$ are Booleans.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, p.16 (T^{x,i}_{rs}, F^{x,i}_{rs}, T^{x,i}, F^{x,i}), p.24 (T^{x,y,i,j}_r, T^{x,i}_{rst}, T̄^{x,y}_1), pp.24–25 (weighted counts in (50) and γ̄_ijk)

import Mathlib
import Definitions.Def_RankOneBTF_groundTruth

namespace RankOneBTF

variable {n m l : ℕ}

/-! Counting parameters of Del Pia, Khajavirad, *Rank-one Boolean tensor factorization and
the multilinear polytope*, arXiv:2202.07053v3, p.16 and p.24. They depend on the ground truth
`x̄, ȳ, z̄` and the input tensor `G` (through `𝒯 = {g_ijk = x̄_i ȳ_j z̄_k}` and
`ℱ = {g_ijk = 1 − x̄_i ȳ_j z̄_k}`).

**Formalization Note** Every count is a real number (the cast of a `Finset.card`); the
indices `r, s, t ∈ {0,1}` are `Bool`s (`false` = 0, `true` = 1). -/

/-- `T^{x,i}_{rs} := |{(j,k) ∈ [m]×[l] : ȳ_j = r, z̄_k = s, (i,j,k) ∈ 𝒯}|`
(arXiv:2202.07053v3, p.16). -/
def Tx (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s : Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun jk : Fin m × Fin l =>
      yb jk.1 = r ∧ zb jk.2 = s ∧ IsT xb yb zb G i jk.1 jk.2).card : ℝ)

/-- `F^{x,i}_{rs} := |{(j,k) ∈ [m]×[l] : ȳ_j = r, z̄_k = s, (i,j,k) ∈ ℱ}|`
(arXiv:2202.07053v3, p.16). -/
def Fx (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s : Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun jk : Fin m × Fin l =>
      yb jk.1 = r ∧ zb jk.2 = s ∧ ¬ IsT xb yb zb G i jk.1 jk.2).card : ℝ)

/-- `T^{y,j}_{rs} := |{(i,k) ∈ [n]×[l] : x̄_i = r, z̄_k = s, (i,j,k) ∈ 𝒯}|` ("similarly
defined", arXiv:2202.07053v3, p.16). -/
def Ty (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s : Bool) (j : Fin m) : ℝ :=
  ((Finset.univ.filter fun ik : Fin n × Fin l =>
      xb ik.1 = r ∧ zb ik.2 = s ∧ IsT xb yb zb G ik.1 j ik.2).card : ℝ)

/-- `F^{y,j}_{rs} := |{(i,k) ∈ [n]×[l] : x̄_i = r, z̄_k = s, (i,j,k) ∈ ℱ}|`
(arXiv:2202.07053v3, p.16). -/
def Fy (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s : Bool) (j : Fin m) : ℝ :=
  ((Finset.univ.filter fun ik : Fin n × Fin l =>
      xb ik.1 = r ∧ zb ik.2 = s ∧ ¬ IsT xb yb zb G ik.1 j ik.2).card : ℝ)

/-- `T^{z,k}_{rs} := |{(i,j) ∈ [n]×[m] : x̄_i = r, ȳ_j = s, (i,j,k) ∈ 𝒯}|`
(arXiv:2202.07053v3, p.16). -/
def Tz (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s : Bool) (k : Fin l) : ℝ :=
  ((Finset.univ.filter fun ij : Fin n × Fin m =>
      xb ij.1 = r ∧ yb ij.2 = s ∧ IsT xb yb zb G ij.1 ij.2 k).card : ℝ)

/-- `F^{z,k}_{rs} := |{(i,j) ∈ [n]×[m] : x̄_i = r, ȳ_j = s, (i,j,k) ∈ ℱ}|`
(arXiv:2202.07053v3, p.16). -/
def Fz (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s : Bool) (k : Fin l) : ℝ :=
  ((Finset.univ.filter fun ij : Fin n × Fin m =>
      xb ij.1 = r ∧ yb ij.2 = s ∧ ¬ IsT xb yb zb G ij.1 ij.2 k).card : ℝ)

/-- `F^{x,i} = F^{x,i}_{00} + F^{x,i}_{10} + F^{x,i}_{01} + F^{x,i}_{11}`
(arXiv:2202.07053v3, p.16). -/
def FxTot (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (i : Fin n) : ℝ :=
  Fx xb yb zb G false false i + Fx xb yb zb G true false i + Fx xb yb zb G false true i +
    Fx xb yb zb G true true i

/-- `F^{y,j} = F^{y,j}_{00} + F^{y,j}_{10} + F^{y,j}_{01} + F^{y,j}_{11}`
(arXiv:2202.07053v3, p.16). -/
def FyTot (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (j : Fin m) : ℝ :=
  Fy xb yb zb G false false j + Fy xb yb zb G true false j + Fy xb yb zb G false true j +
    Fy xb yb zb G true true j

/-- `F^{z,k} = F^{z,k}_{00} + F^{z,k}_{10} + F^{z,k}_{01} + F^{z,k}_{11}`
(arXiv:2202.07053v3, p.16). -/
def FzTot (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (k : Fin l) : ℝ :=
  Fz xb yb zb G false false k + Fz xb yb zb G true false k + Fz xb yb zb G false true k +
    Fz xb yb zb G true true k

/-- `T^{x,y,i,j}_r = |{k ∈ [l] : z̄_k = r, (i,j,k) ∈ 𝒯}|` (arXiv:2202.07053v3, p.24). -/
def Txy (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r : Bool) (i : Fin n) (j : Fin m) : ℝ :=
  ((Finset.univ.filter fun k : Fin l => zb k = r ∧ IsT xb yb zb G i j k).card : ℝ)

/-- `T^{x,z,i,k}_r = |{j ∈ [m] : ȳ_j = r, (i,j,k) ∈ 𝒯}|` ("similarly defined",
arXiv:2202.07053v3, p.24). -/
def Txz (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r : Bool) (i : Fin n) (k : Fin l) : ℝ :=
  ((Finset.univ.filter fun j : Fin m => yb j = r ∧ IsT xb yb zb G i j k).card : ℝ)

/-- `T^{y,z,j,k}_r = |{i ∈ [n] : x̄_i = r, (i,j,k) ∈ 𝒯}|` ("similarly defined",
arXiv:2202.07053v3, p.24). -/
def Tyz (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r : Bool) (j : Fin m) (k : Fin l) : ℝ :=
  ((Finset.univ.filter fun i : Fin n => xb i = r ∧ IsT xb yb zb G i j k).card : ℝ)

/-- `T^{x,i}_{rst} = |{(j,k,i') ∈ [m]×[l]×[n] : ȳ_j = r, z̄_k = s, x̄_{i'} = t,
(i,j,k) ∈ 𝒯, (i',j,k) ∈ 𝒯}|` (arXiv:2202.07053v3, p.24). -/
def Tx3 (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s t : Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun q : Fin m × Fin l × Fin n =>
      yb q.1 = r ∧ zb q.2.1 = s ∧ xb q.2.2 = t ∧ IsT xb yb zb G i q.1 q.2.1 ∧
        IsT xb yb zb G q.2.2 q.1 q.2.1).card : ℝ)

/-- `T^{y,j}_{rst} = |{(i,k,j') ∈ [n]×[l]×[m] : x̄_i = r, z̄_k = s, ȳ_{j'} = t,
(i,j,k) ∈ 𝒯, (i,j',k) ∈ 𝒯}|` ("similarly defined", arXiv:2202.07053v3, p.24). -/
def Ty3 (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s t : Bool) (j : Fin m) : ℝ :=
  ((Finset.univ.filter fun q : Fin n × Fin l × Fin m =>
      xb q.1 = r ∧ zb q.2.1 = s ∧ yb q.2.2 = t ∧ IsT xb yb zb G q.1 j q.2.1 ∧
        IsT xb yb zb G q.1 q.2.2 q.2.1).card : ℝ)

/-- `T^{z,k}_{rst} = |{(i,j,k') ∈ [n]×[m]×[l] : x̄_i = r, ȳ_j = s, z̄_{k'} = t,
(i,j,k) ∈ 𝒯, (i,j,k') ∈ 𝒯}|` ("similarly defined", arXiv:2202.07053v3, p.24). -/
def Tz3 (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (r s t : Bool) (k : Fin l) : ℝ :=
  ((Finset.univ.filter fun q : Fin n × Fin m × Fin l =>
      xb q.1 = r ∧ yb q.2.1 = s ∧ zb q.2.2 = t ∧ IsT xb yb zb G q.1 q.2.1 k ∧
        IsT xb yb zb G q.1 q.2.1 q.2.2).card : ℝ)

/-- `T̄^{x,y}_1 = (1/(nm)) Σ_{i,j} T^{x,y,i,j}_1` (arXiv:2202.07053v3, p.24). -/
noncomputable def TbarXY (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l) :
    ℝ :=
  1 / ((n : ℝ) * m) * ∑ i, ∑ j, Txy xb yb zb G true i j

/-- `T̄^{x,z}_1 = (1/(nl)) Σ_{i,k} T^{x,z,i,k}_1` ("similarly defined", arXiv:2202.07053v3,
p.24). -/
noncomputable def TbarXZ (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l) :
    ℝ :=
  1 / ((n : ℝ) * l) * ∑ i, ∑ k, Txz xb yb zb G true i k

/-- `T̄^{y,z}_1 = (1/(ml)) Σ_{j,k} T^{y,z,j,k}_1` ("similarly defined", arXiv:2202.07053v3,
p.24). -/
noncomputable def TbarYZ (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l) :
    ℝ :=
  1 / ((m : ℝ) * l) * ∑ j, ∑ k, Tyz xb yb zb G true j k

/-- The weighted corruption count `(1/3)F^{x,i}_{00} + (1/2)(F^{x,i}_{01} + F^{x,i}_{10}) +
F^{x,i}_{11}`, the right-hand side of (50) and the bracket in `γ̄_ijk`
(arXiv:2202.07053v3, pp.24–25). -/
noncomputable def phiX (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (i : Fin n) : ℝ :=
  (1 / 3) * Fx xb yb zb G false false i +
    (1 / 2) * (Fx xb yb zb G false true i + Fx xb yb zb G true false i) +
    Fx xb yb zb G true true i

/-- `(1/3)F^{y,j}_{00} + (1/2)(F^{y,j}_{01} + F^{y,j}_{10}) + F^{y,j}_{11}`
(arXiv:2202.07053v3, pp.24–25). -/
noncomputable def phiY (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (j : Fin m) : ℝ :=
  (1 / 3) * Fy xb yb zb G false false j +
    (1 / 2) * (Fy xb yb zb G false true j + Fy xb yb zb G true false j) +
    Fy xb yb zb G true true j

/-- `(1/3)F^{z,k}_{00} + (1/2)(F^{z,k}_{01} + F^{z,k}_{10}) + F^{z,k}_{11}`
(arXiv:2202.07053v3, pp.24–25). -/
noncomputable def phiZ (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (G : BTensor n m l)
    (k : Fin l) : ℝ :=
  (1 / 3) * Fz xb yb zb G false false k +
    (1 / 2) * (Fz xb yb zb G false true k + Fz xb yb zb G true false k) +
    Fz xb yb zb G true true k

end RankOneBTF


