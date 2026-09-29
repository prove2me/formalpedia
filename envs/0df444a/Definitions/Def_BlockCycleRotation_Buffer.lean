-- Prove2me | Definitions.Def_BlockCycleRotation_Buffer
-- name    : BlockCycleRotation_Buffer
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:42:24.059505+00:00
-- url     : https://prove2.me/theorems/42db44e1-6e01-4e29-bfb6-caafe541b4ee
-- title:
--   Buffer: Buffered rotation: $\psi_\beta$, $f_\beta$ and $\mu$
-- statement:
--   Defines the buffered cost functions $\psi_\beta$ and $f_\beta$, the segment sequence they recurse on, and the continuous upper bound $\mu(N,\ell,\beta)$ of equation (integral).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean

-- Generated from BlockCycleRotation/Buffer.lean by skeleton subtraction (Def bundle).
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib
/-
# The buffered variant

The closing remark of §3 introduces `f_β(x) := μ(1,x,β)`, the number of moves
per element when the algorithm may use a buffer of size `β·n`.  Equation
(def-mu-nu) is the recursion

```
μ(N,ℓ,β) - N  =  ℓ                            if ℓ ≤ β,
                 2ℓ + μ(N',ℓ',β) - N'         otherwise,
```

so with `ψ_β(x) := μ(1,x,β) - 1` and the relative maps of `Theorem10.lean`,

```
ψ_β(x) = x                              if x ≤ β,
         2x + Out(x)·ψ_{β/Out(x)}(In(x)) otherwise,
```

the buffer being of fixed absolute size, hence of relative size `β/Out(x)` in
the subproblem.  Since `Out ≤ 2/3`, the relative buffer grows geometrically, so
for `β > 0` the recursion terminates: unlike `ψ`, `ψ_β` is a *finite* sum.

Writing `segᵢ(x)` for the relative size of the `i`-th segment — the `i`-th term
of the Euclidean remainder sequence, divided by `n` — the recursion unravels to

```
ψ_β(x) = 2·∑_{i < T} segᵢ(x) + seg_T(x),    T = least i with segᵢ(x) ≤ β,
```

which is how `psiBuf` is defined here.  For `β = 0` the same formula with
`T = ∞` is `ψ`, and indeed `ψ - ψ_β ≤ 6β`.
-/


namespace BlockCycleRotation

open Filter Topology

/-! ## Segments -/

/-- The relative size of the `i`-th segment.  At `x = k/n` this is `kᵢ/n`. -/
noncomputable def seg (x : ℝ) (i : ℕ) : ℝ :=
  (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Inn^[i] x











/-! ## The buffered cost -/

/-- The index of the first segment that fits into the buffer. -/
noncomputable def bufDepth (β x : ℝ) : ℕ := sInf {i | seg x i ≤ β}

/-- **The buffered relative cost** `ψ_β`. -/
noncomputable def psiBuf (β x : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range (bufDepth β x), seg x i) + seg x (bufDepth β x)

/-- **`f_β(x) = μ(1,x,β)`**, the number of moves per element with a buffer of
relative size `β`. -/
noncomputable def fCostBuf (β x : ℝ) : ℝ := 1 + psiBuf β x















/-! ## Comparison with the unbuffered cost -/













/-! ## The relative cost with a buffer -/





/-! ## Two-step decay

The *one*-step ratio of segments is exactly `{1/y}` at `y = Inⁱ(x)`:
`Out(y)·In(y) = y·{1/y}`, and `{1/y}` can be arbitrarily close to `1` (take `y`
just below `1/m`).  So segments need not shrink from one step to the next.

Over *two* steps they do.  Writing `g = {1/y}`, the next ratio is `{1/In(y)}`,
and `1/In(y) = 1/g + 1`, so it is `{1/g}`.  The two-step ratio is therefore
`g·{1/g} = 1 - g⌊1/g⌋`, and with `m = ⌊1/g⌋ ≥ 1` and `g > 1/(m+1)` one has
`g·m > m/(m+1) ≥ 1/2`.  Hence `seg_{i+2} ≤ seg_i/2` — the classical fact that
Euclidean remainders halve every two steps. -/













/-! ## The buffered cost converges to the unbuffered one

Because segments halve every two steps, the tail past the cut-off is at most
`2(seg_T + seg_{T+1}) ≤ 4β`, so `ψ - ψ_β ≤ 8β`.  This is the paper's
`μ(N,ℓ) = lim_{β→0+} μ(N,ℓ,β)`. -/









/-! ## The remark

"The algorithm takes advantage of the buffer even in cases where neither the
bottom nor the top segment fits into the buffer.  The algorithm makes use of
the buffer as soon as the recursion leads to a subproblem that benefits from
the use of the buffer."

At `x = 2/5` with `β = 1/4` neither segment fits — `β < 2/5` and `β < 3/5` —
but the *second* segment does: the segments are `2/5` and `1/5`, and
`1/5 ≤ 1/4`.  So the recursion stops one step early and `f_β(2/5) = 2` instead
of `f(2/5) = 11/5`. -/















/-! ## The paper's `μ(N,ℓ,β)`

The paper works with the three-variable cost `μ(N,ℓ,β)` and reduces to the
relative function by homogeneity.  Here the reduction is the definition, and
the paper's recursion (def-mu-nu), its homogeneity, the bound `μ ≤ 3N` and the
monotonicity in `β` are recovered from it. -/

/-- **`μ(N,ℓ,β)`**, the idealised move count for rotating `N` items by `ℓ`
with a buffer of size `β`. -/
noncomputable def muCost (N l b : ℝ) : ℝ := N * (1 + psiBuf (b / N) (l / N))













/-! ## The 50% buffer

The figure's caption records that at a buffer size of `50%` the expected cost
is exactly `1.25` moves per element: the shorter segment always fits, so the
recursion stops immediately and `f_{1/2}(x) = 1 + x`. -/







/-! ## The buffered algorithm, equation (integral)

Equation (integral) of the paper defines `Cost(n, k, β)`, the number of moves
the block cycle method makes when rotating an array of `n` elements by `k`
places with an auxiliary buffer of `β` elements, by the recursion

  `Cost(n,k,β) = 0`                                     if `k = 0`,
  `Cost(n,k,β) = n + k`                                  if `k ≤ β`,
  `Cost(n,k,β) = (⌊n/k⌋+1)k + Cost(n', k', β)`           otherwise,

with `k' = n - ⌊n/k⌋k = n % k` and `n' = n - (⌊n/k⌋-1)k = k + n % k`.  This is
the same recursion as the continuous `μ` of equation (continuous), except that
the discrete algorithm also stops when the remainder vanishes; that extra base
case is exactly what makes item 3 of the Corollary an inequality. -/

/-- **Equation (integral).**  The number of moves with a buffer of `b`. -/
def costB (n k b : ℕ) : ℕ :=
  if h : k = 0 then 0
  else if k ≤ b then n + k
  else (n / k + 1) * k + costB (k + n % k) (n % k) b
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

















end BlockCycleRotation


