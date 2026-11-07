-- Prove2me | Definitions.Def_CFLOutliers_RInst
-- name    : CFLOutliers_RInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:17.771577+00:00
-- url     : https://prove2.me/theorems/db2f7a5f-758a-433f-9810-ee6091658a79
-- title:
--   Explicitly represented rational instances
-- statement:
--   An **explicit rational instance** lists $m$, $n$, $q$, the opening costs $f_0,\dots,f_{m-1}\in\mathbb Q$, the capacities $u_0,\dots,u_{m-1}\in\mathbb N$, and the full $(m+n)\times(m+n)$ rational distance matrix in row-major order, facilities first. It is **shaped** if the lists have lengths $m$, $m$ and $(m+n)^2$, and **well formed** if it is shaped and its real instance satisfies the standing assumptions (a pseudometric, $f\ge 0$, $q\le n$).
--
--   This is the input of Theorem 1.1: "explicitly represented unit-demand clients" with a binary input length.
--
--   **Formalization Note** The real instance casts the entries to $\mathbb R$; missing entries of a list that is too short read as $0$, which only matters for inputs that are not shaped.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_CFLOutliers_Inst

namespace CFLOutliers

/-- **An explicitly represented rational instance** (the input of Theorem 1.1, p.2: "binary input
length … for explicitly represented unit-demand clients").

* `m`, `n`, `q`: numbers of facilities and clients, and the quota;
* `f`: the opening costs `f_0, …, f_{m−1}`; `u`: the capacities;
* `c`: the `(m + n) × (m + n)` distance matrix in row-major order, facilities first (point `i`
  for facility `i`, point `m + j` for client `j`).

**Formalization Note.** Lengths are not built in; `RInst.Shaped` states them. -/
structure RInst where
  /-- number of facilities -/
  m : ℕ
  /-- number of clients -/
  n : ℕ
  /-- the quota -/
  q : ℕ
  /-- opening costs -/
  f : List ℚ
  /-- capacities -/
  u : List ℕ
  /-- distance matrix, row-major, facilities first -/
  c : List ℚ

namespace RInst

/-- The matrix index of a point: facility `i ↦ i`, client `j ↦ m + j`. -/
def idx (I : RInst) : Fin I.m ⊕ Fin I.n → ℕ
  | Sum.inl i => i
  | Sum.inr j => I.m + j

/-- **The real instance of a rational input**: the entries cast to `ℝ` (entries missing from a
too-short list read as `0`; this only matters for inputs that are not `Shaped`). -/
def toInst (I : RInst) : Inst where
  m := I.m
  n := I.n
  c x y := ((I.c.getD (I.idx x * (I.m + I.n) + I.idx y) 0 : ℚ) : ℝ)
  f i := ((I.f.getD i 0 : ℚ) : ℝ)
  u i := I.u.getD i 0
  q := I.q

/-- The lists have the lengths `m`, `m` and `(m + n)²`. -/
def Shaped (I : RInst) : Prop :=
  I.f.length = I.m ∧ I.u.length = I.m ∧ I.c.length = (I.m + I.n) * (I.m + I.n)

/-- **A well-formed input**: shaped, and its real instance satisfies the standing assumptions of
p.2 (a pseudometric, `f ≥ 0`, `q ≤ n`). -/
def WellFormed (I : RInst) : Prop := I.Shaped ∧ I.toInst.Std

end RInst

end CFLOutliers


