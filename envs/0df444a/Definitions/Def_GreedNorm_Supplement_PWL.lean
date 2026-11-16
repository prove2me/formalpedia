-- Prove2me | Definitions.Def_GreedNorm_Supplement_PWL
-- name    : GreedNorm_Supplement_PWL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:49:27.525798+00:00
-- url     : https://prove2.me/theorems/b4467756-9d63-40a5-8fb9-bda6d464ec82
-- title:
--   Explicit nondecreasing piecewise-linear load data $f_i:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$
-- statement:
--   In GLB with piecewise-linear loads (§4.1), machine $i$ turns its total processing time $z=\sum_{j:\sigma(j)=i}p_{ij}$ into the load $f_i(z)$, where $f_i:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ is nondecreasing and left-continuous. An algorithm must read $f_i$, so $f_i$ is given explicitly by finitely many pieces.
--
--   The data of one function are a number $K\ge0$ of breakpoints $b_0,\dots,b_{K-1}$ and $K+1$ affine pieces $z\mapsto a_k+s_kz$ ($k=0,\dots,K$). The function is
--
--   $$
--   f(z)=a_{k(z)}+s_{k(z)}\,z,\qquad k(z)=\min\{k<K : z\le b_k\}\ \ (\text{and } k(z)=K \text{ if no such } k).
--   $$
--
--   Each piece is used on an interval open on the left and closed on the right, so $f$ is left-continuous; jumps at breakpoints and $f(0)>0$ are allowed. Every nondecreasing left-continuous function with finitely many affine pieces arises this way.
--
--   This is the representation of the loads in Theorems 1.4 and 4.6 of the supplement; their input size counts the breakpoints $\sum_i K_i$.
--
--   **Formalization Note** The fields `brk`, `icpt`, `slope` are functions on $\mathbb N$ of which only the first $K$, $K+1$, $K+1$ values are read. Monotonicity and nonnegativity on $[0,\infty)$ are hypotheses of the theorems, not part of the data.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §4.1, p.11 (PDF 13); Theorem 1.4, p.2 (PDF 4)

import Mathlib

namespace GreedNorm

/-- **Explicit data of a nondecreasing piecewise-linear load function** `f_i : ℝ_{≥0} → ℝ_{≥0}`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), §4.1 "GLB with Piecewise Linear Load Functions", p.11 (PDF 13): "each load function loadi
has the form loadi(σ) = fi(Σ_{j∈J:σ(j)=i} pij) where fi : R≥0 → R≥0 is a nondecreasing,
left-continuous function"; Theorem 1.4, p.2 (PDF 4): "GLB with piecewise-linear loads".

The data are a number `K` of finite breakpoints `brk 0, …, brk (K-1)` and `K + 1` affine pieces
`z ↦ icpt k + slope k * z` (`k = 0, …, K`). Only `brk k` for `k < K` and `icpt k`, `slope k`
for `k ≤ K` are data; the other values of the functions `ℕ → ℝ` are never read.

**Formalization Note** The function is `Supplement.PWL.eval`: at `z` it uses the piece of the
least `k < K` with `z ≤ brk k`, and piece `K` if there is none. Each piece is used on a
left-open, right-closed interval, so `eval` is left-continuous by construction, possibly with
jumps at breakpoints and with `eval 0` arbitrary. Monotonicity and nonnegativity on `[0, ∞)`
are hypotheses of the theorems, not part of the data. -/
structure Supplement.PWL where
  /-- the number of finite breakpoints -/
  K : ℕ
  /-- the breakpoints `brk k`, `k < K` -/
  brk : ℕ → ℝ
  /-- the intercepts `icpt k`, `k ≤ K` -/
  icpt : ℕ → ℝ
  /-- the slopes `slope k`, `k ≤ K` -/
  slope : ℕ → ℝ

namespace Supplement.PWL

/-- The index of the piece used at `z`: the least `k < K` with `z ≤ brk k`, else `K`. -/
noncomputable def piece (D : PWL) (z : ℝ) : ℕ := by
  classical
  exact if h : ∃ k, k < D.K ∧ z ≤ D.brk k then Nat.find h else D.K

/-- The value `f(z) = icpt k + slope k · z` with `k = piece D z`. -/
noncomputable def eval (D : PWL) (z : ℝ) : ℝ :=
  D.icpt (D.piece z) + D.slope (D.piece z) * z

end Supplement.PWL

end GreedNorm


