-- Prove2me | Definitions.Def_PochetWolsey_Capacities_Model
-- name    : PochetWolsey_Capacities_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:14.707983+00:00
-- url     : https://prove2.me/theorems/b9882113-e8ba-41d1-9bae-9d45048c584f
-- title:
--   Constant-capacity lot-sizing sets and common stock/setup space
-- statement:
--   Let $n$ be the number of periods, $C$ the constant capacity, and $d_t$ demand in period $t$. The admissible-data predicate requires $n>0$, $C>0$, and $0\le d_t\le C$ for every period. Write $d_{kt}=\sum_{u=k}^t d_u$. The discrete and initial-stock feasible sets are
--   $$
--   X^{\mathrm{DLS-CC}}=\{y\in\{0,1\}^n:C\sum_{u=1}^t y_u\ge d_{1t}\ (1\le t\le n)\},
--   $$
--   $$
--   X^{\mathrm{DLSI-CC}}=\{(s_0,y)\in\mathbb R_+\times\{0,1\}^n:s_0+C\sum_{u=1}^t y_u\ge d_{1t}\ (1\le t\le n)\}.
--   $$
--   In the common space $\mathbb R^{n+1}\times\mathbb R^n$, define
--   $$
--   X^{\mathrm{WW-CC}}=\{(s,y)\in\mathbb R_+^{n+1}\times\{0,1\}^n:s_{k-1}+C\sum_{u=k}^t y_u\ge d_{kt}\ (1\le k\le t\le n)\}.
--   $$
--   For each $k$, the component $X_k^{\mathrm{DLSI-CC}}$ retains all stock nonnegativity and binary setup conditions, but only the displayed covering rows with that fixed $k$. These original feasible sets provide the common objects for the hull theorems; no hull description is part of their definition.
--
--   **Formalization Note** `Fin n` coordinate $j$ represents printed period $j+1$; stocks use `Fin (n+1)` with their printed indices unchanged. Thus `k.castSucc` is the stock entering period $k+1$. Initial and final stocks are not fixed. The set definitions are total for arbitrary data; `Model` records the chapter's admissible data separately.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, pp. 273, 276, 279, 281, 283 (PDF 286, 289, 292, 294, 296), Eqs. (9.1)–(9.6) and Section 9.5.2

import Mathlib

namespace PochetWolsey.Capacities

/-- Standing data conventions of Chapter 9. Fin n represents periods 1,...,n. -/
def Model (n : ℕ) (C : ℝ) (d : Fin n → ℝ) : Prop :=
  0 < n ∧ 0 < C ∧ ∀ t, 0 ≤ d t ∧ d t ≤ C

/-- Equations (9.1)-(9.2), in the real setup space. -/
def discreteSet {n : ℕ} (C : ℝ) (d : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ u, y u = 0 ∨ y u = 1) ∧
    ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u}

/-- Equations (9.3)-(9.4): one initial stock coordinate and n setups. -/
def initialStockSet {n : ℕ} (C : ℝ) (d : Fin n → ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
    ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ p.1 + C * ∑ u ∈ Finset.Iic t, p.2 u}

/-- Equations (9.5)-(9.6); stock indices remain 0,...,n. -/
def wagnerWhitinSet {n : ℕ} (C : ℝ) (d : Fin n → ℝ) :
    Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
    ∀ k t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
      p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u}

/-- The fixed-k component on p. 283, embedded in the entire (s,y) space. -/
def componentSet {n : ℕ} (C : ℝ) (d : Fin n → ℝ) (k : Fin n) :
    Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
    ∀ t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
      p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u}

end PochetWolsey.Capacities


