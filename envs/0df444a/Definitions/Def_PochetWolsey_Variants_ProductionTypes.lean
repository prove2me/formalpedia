-- Prove2me | Definitions.Def_PochetWolsey_Variants_ProductionTypes
-- name    : PochetWolsey_Variants_ProductionTypes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:32.237303+00:00
-- url     : https://prove2.me/theorems/5886f8f1-b430-4230-b55d-e26e8cbce55e
-- title:
--   Multiple production types and generalized lot-sizing cuts
-- statement:
--   Let $n,K\ge1$, let $d_t\ge0$, and let $M>0$ satisfy $M\ge\sum_t d_t$. Variables are production $x_t^k$, setups $y_t^k$, and stock $s_t$ for $0\le t\le n$. The original set satisfies
--   $$s_{t-1}+\sum_kx_t^k=d_t+s_t,\quad 0\le x_t^k\le My_t^k,\quad s_t\ge0,\quad s_0=0,\quad y_t^k\in\{0,1\}.$$
--   Its continuous base replaces the binary domain by $0\le y_t^k\le1$. For every prefix $L_\ell=\{1,\dots,\ell\}$ and each family $S_k\subseteq L_\ell$, define the generalized cuts by
--   $$\sum_k\sum_{j\in S_k}x_j^k+\sum_k\sum_{j\in L_\ell\setminus S_k}d_{j\ell}y_j^k\ge d_{1\ell},\qquad d_{j\ell}=\sum_{r=j}^{\ell}d_r.$$
--
--   These are the independent original constraints and cut family for the hull claim. There is no constraint $\sum_k y_t^k\le1$ in the displayed uncapacitated model.
--
--   **Formalization Note** Production and setups use finite zero-based indices; inventory includes both endpoints. Only $s_0$ is fixed in this definition, exactly as in the displayed set on printed page 345; $s_n$ is nonnegative and free. No cost assumptions enter this feasible-set result.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 345 (PDF 358), Section 11.5, displayed definition of XLS-U-CP and Proposition 11.6; DOI 10.1007/0-387-33477-7

import Mathlib

open scoped BigOperators

namespace PochetWolsey.Variants

abbrev CPPoint (n K : ℕ) :=
  (Fin K → Fin n → ℝ) × (Fin K → Fin n → ℝ) × (Fin (n + 1) → ℝ)

structure ProductionTypes (n K : ℕ) where
  d : Fin n → ℝ
  M : ℝ

def ProductionTypes.Standing {n K : ℕ} (D : ProductionTypes n K) : Prop :=
  0 < n ∧ 0 < K ∧ (∀ t, 0 ≤ D.d t) ∧ 0 < D.M ∧ (∑ t, D.d t) ≤ D.M

def ProductionTypes.base {n K : ℕ} (D : ProductionTypes n K)
    (w : CPPoint n K) : Prop :=
  (∀ k t, 0 ≤ w.1 k t ∧ 0 ≤ w.2.1 k t ∧ w.2.1 k t ≤ 1 ∧
    w.1 k t ≤ D.M * w.2.1 k t) ∧
  (∀ t, 0 ≤ w.2.2 t) ∧ w.2.2 0 = 0 ∧
  (∀ t : Fin n, w.2.2 t.castSucc + (∑ k, w.1 k t) =
    D.d t + w.2.2 t.succ)

def ProductionTypes.feasible {n K : ℕ} (D : ProductionTypes n K) : Set (CPPoint n K) :=
  {w | D.base w ∧ ∀ k t, w.2.1 k t = 0 ∨ w.2.1 k t = 1}

def ProductionTypes.cuts {n K : ℕ} (D : ProductionTypes n K)
    (w : CPPoint n K) : Prop :=
  ∀ (l : Fin n) (S : Fin K → Finset (Fin n)),
    (∀ k, S k ⊆ Finset.univ.filter (fun j => j ≤ l)) →
    (∑ j ∈ Finset.univ.filter (fun j => j ≤ l), D.d j) ≤
      (∑ k, ∑ j ∈ S k, w.1 k j) +
      ∑ k, ∑ j ∈ (Finset.univ.filter (fun j => j ≤ l)) \ S k,
        (∑ r ∈ Finset.univ.filter (fun r => j ≤ r ∧ r ≤ l), D.d r) * w.2.1 k j

end PochetWolsey.Variants


