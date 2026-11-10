-- Prove2me | Definitions.Def_NashOrTriangle_inputKT
-- name    : NashOrTriangle_inputKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:34.511331+00:00
-- url     : https://prove2.me/theorems/85834b8f-40f7-418e-8952-b7dc28e1cbec
-- title:
--   Input of $\mathrm{NorT}(k,t)$
-- statement:
--   The input of $\mathrm{NorT}(k, t)$: memory cell $0$ holds $k$, cell $1$ holds $t$, all other cells hold $0$.
--
--   **Formalization Note** The paper gives $k$ and $t$ in unary, which matters only for polynomial-time statements; Theorem 2.1's bounds are explicit functions of $k$ and $t$.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Definition 1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle

/-- The input memory of `NorT(k, t)`: cell `0` holds `k`, cell `1` holds `t`, all other cells `0`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Definition 1.1, printed p. 3 (PDF p. 4): "Given k, t ≥ 2 in unary".

**Formalization Note** "In unary" matters only for polynomial-time statements; the bounds of
Theorem 2.1 are explicit functions of `k` and `t`, so the numbers are given as cell values. -/
noncomputable def inputKT (k t : ℕ) : ℤ → ℝ :=
  fun i => if i = 0 then (k : ℝ) else if i = 1 then (t : ℝ) else 0

end NashOrTriangle


