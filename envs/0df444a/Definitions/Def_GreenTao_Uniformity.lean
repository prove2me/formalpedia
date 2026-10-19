-- Prove2me | Definitions.Def_GreenTao_Uniformity
-- name    : GreenTao_Uniformity
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T20:52:36.433067+00:00
-- url     : https://prove2.me/theorems/e7b3827e-f4bd-44ac-af8b-7cfa51420d98
-- title:
--   Real Gowers cube averages and multilinear progression averages
-- statement:
--   For a positive modulus $m$, a real function $f$ on $G=\mathbb Z/m\mathbb Z$, and $d\ge0$, define the cube average
--
--   $$C_d(f)=\mathbb E_{x\in G}\mathbb E_{h\in G^d}\prod_{\omega\in\{0,1\}^d}f(x+\omega\cdot h),\qquad \omega\cdot h=\sum_{i=1}^d\omega_i h_i.$$
--
--   For real functions $F_0,\ldots,F_{k-1}$ on $G$, define
--
--   $$T_k(F_0,\ldots,F_{k-1})=\mathbb E_{x,r\in G}\prod_{j=0}^{k-1}F_j(x+jr).$$
--
--   The first expression is the real Gowers inner product with all entries equal. For $d\ge1$, it is the $2^d$-th power of the $U^d$ norm. The second expression is the multilinear progression statistic in the generalized von Neumann estimate; constant tuples recover the existing progression count. Both averages include all shifts, including zero shifts. These definitions extend the project's existing uniform-average and pseudorandomness interface.
--
--   **Formalization Note.** Uniformity thresholds below are stated using $|C_d(f)|$, avoiding fractional powers. The definition also permits dimension zero, where the cube average is the mean.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 Definition 5.1, equations (5.1) and (5.4), and the mixed progression expression in Proposition 5.3 (with consecutive coefficients c_j=j).

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace GreenTao

/-- The real Gowers cube average (the `2^d`-th power of the `U^d` norm for `d ≥ 1`),
as in Green--Tao, Definition 5.1, equations (5.1) and (5.4). -/
noncomputable def cubeAvg (d : ℕ) {m : ℕ+} (f : ZMod (m : ℕ) → ℝ) : ℝ :=
  avg fun x => avg fun h : Fin d → ZMod (m : ℕ) =>
    ∏ ω : Fin d → Bool, f (x + ∑ i : Fin d, if ω i then h i else 0)

/-- The multilinear progression average, with the consecutive coefficients `0,...,k-1`.
This is the expression in Green--Tao, Proposition 5.3. -/
noncomputable def mixedAPAvg (k : ℕ) {m : ℕ+}
    (F : Fin k → ZMod (m : ℕ) → ℝ) : ℝ :=
  avg fun x => avg fun r => ∏ j : Fin k, F j (x + (j.val : ZMod (m : ℕ)) * r)

end GreenTao


