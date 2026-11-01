-- Prove2me | Definitions.Def_ColumnRandLP_StandardLP
-- name    : ColumnRandLP_StandardLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:21.051816+00:00
-- url     : https://prove2.me/theorems/36ffe80b-77f3-4ed2-b314-88caf2276aae
-- title:
--   Standard-form LP $\min\{c^Tx\mid Ax=b,\ x\ge 0\}$, its value, its dual and basic dual solutions
-- statement:
--   Let $A$ be an $m\times N$ real matrix, $b\in\mathbb R^m$ and $c\in\mathbb R^N$. The **standard-form linear program**
--   $$
--   \min\{c^Tx \mid Ax=b,\ x\ge 0\}
--   $$
--   has feasible region $F=\{x\in\mathbb R^N \mid Ax=b,\ x\ge 0\}$. It is **feasible** if $F\neq\emptyset$ and **bounded** if $c^Tx$ is bounded below on $F$; its **optimal value** is $v=\inf\{c^Tx\mid x\in F\}$.
--
--   Its **dual** is $\max\{p^Tb\mid p^TA\le c^T\}$. A vector $p\in\mathbb R^m$ is **dual feasible** if $p^TA\le c^T$ componentwise, and an **optimal dual solution** if in addition $q^Tb\le p^Tb$ for every dual feasible $q$.
--
--   A **basis** is a set $B\subseteq[N]$ of size $m$ with $A_B$ nonsingular, i.e. the columns $\{A_j\}_{j\in B}$ are linearly independent. The **basic dual solution** for $B$ is the vector $p$ with $p^T=c_B^TA_B^{-1}$; it need not be dual feasible.
--
--   These are the objects of §3.1: the complete problem $P$ and its dual $D$, the column-randomized problem $P_J$ and its dual $D_J$, and the problems $z(b)$, $z(b')$ of Lemma EC.3 are all instances.
--
--   **Formalization Note** Indices are 0-based (`Fin m`, `Fin N`). The optimal value is the real infimum `sInf`; Lean returns $0$ for the infimum of an empty set or of a set unbounded below, so every statement that uses `lpValue` carries hypotheses that make the LP feasible and bounded below (then the infimum is attained). A basis is encoded as an injective `β : Fin m → Fin N` with linearly independent columns, and $p^T=c_B^TA_B^{-1}$ as the $m$ equations $p^TA_{\beta k}=c_{\beta k}$, which determine $p$ uniquely.
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, §3.1, (2), pp.5–6 (standard form, feasible and bounded, v(P′), F(P′), dual D, basis, basic dual solution pᵀ = c_BᵀA_B⁻¹); Lemma EC.3, p.ec7 (optimal dual solution)

import Mathlib

open Matrix

namespace ColumnRandLP

/-- Feasible set `F = {x | A x = b, x ≥ 0}` of a standard-form linear program
`min {cᵀx | Ax = b, x ≥ 0}` with an `m × N` constraint matrix (Akchen–Mišić,
arXiv:2007.10461v5, §3.1, (2), p.5). Used for the complete problem `P` (`N = n`), the
column-randomized problem `P_J` (`N = K`, Definition 1, (3), p.6 and (4), p.7) and the
problems `z(b)` of Lemma EC.3 (p.ec7).

**Formalization Note** Rows are indexed by `Fin m` and columns by `Fin N` (0-based; the paper's
`[m]`, `[n]` are 1-based). -/
def feasSet {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (b : Fin m → ℝ) : Set (Fin N → ℝ) :=
  {x | A *ᵥ x = b ∧ 0 ≤ x}

/-- The LP `min {cᵀx | Ax = b, x ≥ 0}` is feasible (Akchen–Mišić, arXiv:2007.10461v5, §3.1,
p.6). -/
def IsFeasible {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (b : Fin m → ℝ) : Prop :=
  (feasSet A b).Nonempty

/-- The objective of `min {cᵀx | Ax = b, x ≥ 0}` is bounded below on the feasible set
("bounded", Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6). -/
def IsBoundedBelow {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (b : Fin m → ℝ) (c : Fin N → ℝ) :
    Prop :=
  BddBelow ((fun x => c ⬝ᵥ x) '' feasSet A b)

/-- Optimal value `v = inf {cᵀx | Ax = b, x ≥ 0}` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6:
"we denote its optimal objective value by v(P′)").

**Formalization Note** This is the real infimum `sInf`. Lean's `sInf` is `0` on the empty set
and on sets unbounded below, so `lpValue` is the paper's `v` only when the LP is feasible and
bounded below; every statement that uses it carries hypotheses that guarantee both (and then the
infimum is attained, so it is the minimum). -/
noncomputable def lpValue {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (b : Fin m → ℝ)
    (c : Fin N → ℝ) : ℝ :=
  sInf ((fun x => c ⬝ᵥ x) '' feasSet A b)

/-- Dual feasibility for `max {pᵀb | pᵀA ≤ cᵀ}`, the dual of `min {cᵀx | Ax = b, x ≥ 0}`
(Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6, dual problems `D` and `D_J`): `pᵀA ≤ cᵀ`
componentwise. -/
def IsDualFeasible {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (c : Fin N → ℝ) (p : Fin m → ℝ) :
    Prop :=
  p ᵥ* A ≤ c

/-- `p` is an optimal solution of the dual `max {pᵀb | pᵀA ≤ cᵀ}` (Akchen–Mišić,
arXiv:2007.10461v5, §3.1, p.6; "optimal dual solution", Lemma EC.3, p.ec7; "optimal solution p
of problem D_J", Proposition EC.3, p.ec7): `p` is dual feasible and attains the dual maximum. -/
def IsDualOptimal {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (b : Fin m → ℝ) (c : Fin N → ℝ)
    (p : Fin m → ℝ) : Prop :=
  IsDualFeasible A c p ∧ ∀ q, IsDualFeasible A c q → q ⬝ᵥ b ≤ p ⬝ᵥ b

/-- A **basic solution of the dual** `D : max {pᵀb | pᵀA ≤ cᵀ}` (Akchen–Mišić,
arXiv:2007.10461v5, §3.1, p.6): for a basis `B ⊆ [n]`, `|B| = m`, with `A_B` nonsingular, the
vector `p` with `pᵀ = c_Bᵀ A_B⁻¹`. Dual feasibility `pᵀA ≤ cᵀ` is **not** required.

**Formalization Note** The basis is an injective `β : Fin m → Fin n` (an enumeration of `B`)
whose columns `A_{β 0}, …, A_{β (m-1)}` are linearly independent (so `A_B` is nonsingular), and
`pᵀ = c_Bᵀ A_B⁻¹` is written without the inverse as the `m` equations `pᵀ A_{β k} = c_{β k}`,
which determine `p` uniquely. Injectivity is implied by linear independence and is kept to
mirror `|B| = m`. -/
def IsBasicDualSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (p : Fin m → ℝ) : Prop :=
  ∃ β : Fin m → Fin n, Function.Injective β ∧
    LinearIndependent ℝ (fun k : Fin m => fun i : Fin m => A i (β k)) ∧
    ∀ k, (p ᵥ* A) (β k) = c (β k)

end ColumnRandLP


