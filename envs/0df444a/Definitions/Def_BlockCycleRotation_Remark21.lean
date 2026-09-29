-- Prove2me | Definitions.Def_BlockCycleRotation_Remark21
-- name    : BlockCycleRotation_Remark21
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:35:19.673091+00:00
-- url     : https://prove2.me/theorems/8bddf234-43e2-407c-af31-8a203120bb8f
-- title:
--   Remark21: The series of Remark 21 and $\zeta(3)$
-- statement:
--   Defines the auxiliary series $S$, the zeta values $\zeta(3)$ and $\zeta(2,1)$, and the harmonic partial sums used to evaluate them, supporting the closed form $C = \tfrac12 - S/(2\zeta(3))$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean

-- Generated from BlockCycleRotation/Remark21.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Remark 21

The paper rewrites the constant `C` of equation (const-c) as

```
C = 1/2 - S/(2·ζ(3)),     S = ∑_{a > a' ≥ 1} 1/(a'·(a+a')²),
```

equation (const-c-alternative).  The argument has three steps.

1. The summand `(2a+a')/(2a²(a+a')²)` equals `(1/(2a'))(1/a² - 1/(a+a')²)`.
2. Multiplying by `ζ(3) = ∑_d 1/d³` removes the coprimality condition, because
   the summand is homogeneous of degree `-3` and every pair `A > A' ≥ 1`
   factors uniquely as `A = d·a`, `A' = d·a'` with `d = gcd(A,A')`.
3. Euler's formula `ζ(2,1) = ζ(3)` for the resulting `∑_{a>a'≥1} 1/(a'a²)`.

The paper cites step 3; Mathlib has no multiple-zeta-value theory, so it is
proved here from scratch in `Euler.lean`.
-/


namespace BlockCycleRotation

open Finset

/-! ## The three series over all pairs

Each is supported on `a > a' ≥ 1` and extended by zero, in the style of
`cTerm`. -/

/-- `cTerm` without the coprimality condition. -/
noncomputable def gTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then
    (2 * (p.1 : ℝ) + (p.2 : ℝ)) / (2 * (p.1 : ℝ) ^ 2 * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2)
  else 0

/-- The summand of `ζ(2,1) = ∑_{a > a' ≥ 1} 1/(a'·a²)`. -/
noncomputable def zTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then 1 / ((p.2 : ℝ) * (p.1 : ℝ) ^ 2) else 0

/-- The summand of `S = ∑_{a > a' ≥ 1} 1/(a'·(a+a')²)`. -/
noncomputable def eTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then 1 / ((p.2 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2) else 0











/-! ## Convergence

Bounding row by row in the *first* index needs a harmonic sum; bounding in the
second index does not, since `∑_{a > a'} 1/a² ≤ 1/a'` is the tail bound
`sum_inv_sq_tail_le`.  So the sums are taken columnwise. -/















/-- `ζ(2,1) = ∑_{a > a' ≥ 1} 1/(a'·a²)`. -/
noncomputable def zeta21 : ℝ := ∑' p, zTerm p

/-- `S = ∑_{a > a' ≥ 1} 1/(a'·(a+a')²)`, the series of eq. (const-c-alternative). -/
noncomputable def sConst : ℝ := ∑' p, eTerm p

/-- `ζ(3) = ∑_{d ≥ 1} 1/d³`. -/
noncomputable def zeta3 : ℝ := ∑' d : ℕ, 1 / ((d : ℝ) + 1) ^ 3



/-! ## Step 2: removing the coprimality condition

`gTerm` is homogeneous of degree `-3`, and every pair `A > A' ≥ 1` is uniquely
`(d·a, d·a')` with `d = gcd(A,A')` and `gcd(a,a') = 1`.  So multiplying the
coprime sum by `ζ(3) = ∑_d 1/d³` gives the sum over all pairs. -/

/-- `1/(d+1)³`, the summand of `ζ(3)`. -/
noncomputable def uTerm (d : ℕ) : ℝ := 1 / ((d : ℝ) + 1) ^ 3



















/-! ## Step 3: Euler's `ζ(2,1) = ζ(3)`

Mathlib has no multiple-zeta-value theory, so the formula the paper cites is
proved here.  Writing `n = a'` and `k = a - a'`, the point is the identity

```
1/(n(n+k)²) + 1/(k(n+k)²) = 1/(n·k·(n+k)),
```

whose left side is `ζ(2,1)`'s summand plus the same with `n` and `k` swapped.
So the right side sums to `2·ζ(2,1)`.  Summing it instead over `k` first uses
only the telescoping `∑_k 1/(k(n+k)) = H_n/n`, giving `∑_n H_n/n² = ζ(2,1) +
ζ(3)`.  Hence `2·ζ(2,1) = ζ(2,1) + ζ(3)`. -/

open Filter Topology

/-- `harm a = ∑_{i=1}^{a-1} 1/i`. -/
noncomputable def harm (a : ℕ) : ℝ := ∑ i ∈ Finset.Ico 1 a, (1 : ℝ) / (i : ℝ)













/-! ### The two symmetric series -/



/-- `1/(n(n+k)²)` at `n = i+1`, `k = j+1`. -/
noncomputable def pTerm (q : ℕ × ℕ) : ℝ :=
  1 / (((q.1 : ℝ) + 1) * (((q.1 : ℝ) + 1) + ((q.2 : ℝ) + 1)) ^ 2)











/-- `1/(n·k·(n+k))` at `n = i+1`, `k = j+1`. -/
noncomputable def qTerm (q : ℕ × ℕ) : ℝ :=
  1 / ((((q.2 : ℝ) + 1) * ((q.1 : ℝ) + 1)) * (((q.1 : ℝ) + 1) + ((q.2 : ℝ) + 1)))















/-! ### The rows of `ζ(2,1)` -/











/-! ### Euler's formula -/



/-! ## Step 4: equation (const-c-alternative) -/









end BlockCycleRotation


