-- Prove2me | Definitions.Def_BlockCycleRotation_Theorem10
-- name    : BlockCycleRotation_Theorem10
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:36:39.672873+00:00
-- url     : https://prove2.me/theorems/a7e4371b-25a1-4b3f-a018-5d5d5bb7109f
-- title:
--   Theorem10: The cost functions $\psi$ and $f$, and the uniform law on $[0,\tfrac12]$
-- statement:
--   Defines the continuous-parameter cost functions $\psi$ and $f = 1+\psi$ by their self-similar recursion, their extension $\bar f$ to the unit box for the Riemann-integrability statement, and the uniform probability measure on $[0,\tfrac12]$ used for the moment computation.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Theorem 8* means **Theorem 7**; *Theorem 10* means **Theorem 9**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean

-- Generated from BlockCycleRotation/Theorem10.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Theorem 10 and Theorem 8

Theorem 10 states that `avgCost n / n` converges, and identifies the limit as
`2∫₀^{1/2} f` where `f` is the *relative cost*: the number of moves per element
the algorithm uses to rotate by a fraction `x` of the array.

`f = 1 + ψ` on `[0,1/2]`, where `ψ` is defined by the recursion the block cycle
algorithm follows.  Writing `{t}` for the fractional part, the recursion is

```
ψ(x) = 2x + Out(x)·ψ(In(x)),   Out(x) = x(1+{1/x}),  In(x) = {1/x}/(1+{1/x}),
```

with `In 0 = Out 0 = 0`.  This is the paper's `(k,n) ↦ (n mod k, k + n mod k)`
recursion in relative coordinates: at `x = k/n` one has `Out(x) = n'/n` and
`In(x) = k'/n'`.

Unravelled, `ψ` is the series `2x + 2∑_{i≥1} Out(x)···Out(Inⁱ⁻¹(x))·Inⁱ(x)`,
which converges uniformly because `In` maps into `[0,1/2)` and `Out ≤ 2/3`
there.  That is Theorem 8's convergence; continuity at irrationals follows
since `In` and `Out` are continuous away from `1/x ∈ ℤ` and preserve
irrationality.
-/


namespace BlockCycleRotation

open Filter Topology

/-! ## The two maps -/

/-- `In(x) = {1/x}/(1+{1/x})`, the relative shift of the next subproblem. -/
noncomputable def Inn (x : ℝ) : ℝ :=
  if x = 0 then 0 else Int.fract (1 / x) / (1 + Int.fract (1 / x))

/-- `Out(x) = x(1+{1/x})`, the relative size of the next subproblem. -/
noncomputable def Outt (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * (1 + Int.fract (1 / x))













/-! ## The series for `ψ`

`ψ(x) = 2x + 2∑_{i≥1} Out(x)···Out(Inⁱ⁻¹(x))·Inⁱ(x)`.  Every iterate after the
first lies in `[0,1/2)`, where `Out ≤ 2/3`, so the `i`-th term is at most
`(2/3)ⁱ` and the series converges uniformly. -/

/-- The `i`-th term of the series for `ψ`. -/
noncomputable def psiTerm (x : ℝ) (i : ℕ) : ℝ :=
  2 * (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Inn^[i] x)











/-- **The relative type-A cost.**  `ψ(x)` is the number of type-A moves per
element when rotating by a fraction `x ≤ 1/2` of the array. -/
noncomputable def psi (x : ℝ) : ℝ := ∑' i, psiTerm x i









/-! ## The bridge to the Euclidean algorithm

At `x = k/n` the recursion for `ψ` is exactly the algorithm's
`(k, n) ↦ (n mod k, k + n mod k)`. -/













/-! ## The relative cost `f`

`f(x) = 1 + ψ(min x (1-x))` is the number of moves per element.  The `min`
records that the algorithm rotates by the shorter of the two segments. -/

/-- **The relative cost.** -/
noncomputable def fCost (x : ℝ) : ℝ := 1 + psi (min x (1 - x))







/-! ## Theorem 8: continuity at the irrationals

`In` and `Out` are continuous wherever `1/x` is not an integer, and `In`
preserves irrationality.  So each partial sum of the series is continuous at an
irrational point, and the uniform convergence transfers continuity to `ψ`. -/





















/-- The partial sums of the series for `ψ`. -/
noncomputable def psiPartial (N : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range N, psiTerm x i

/-! ### The sharp bound `ψ ≤ 2`

The paper's Observation `μ(N,ℓ,β) ≤ 3N` says the algorithm never uses more than
three moves per element, i.e. `ψ ≤ 2`.  The series bound `∑ (2/3)ⁱ = 3` only
gives `ψ ≤ 3`; the sharp value comes from the recursion, since
`x + Out(x) = 2x + 1 - x⌊1/x⌋ ≤ 1` exactly because `⌊1/x⌋ ≥ 2` on `[0,1/2]`. -/



















/-! ## Integrability

`f` is bounded and continuous off a countable set, so it is integrable. -/

open MeasureTheory
open scoped ENNReal

/-- `f` cut down to `[0,1]`, so that it is globally bounded. -/
noncomputable def fBar (x : ℝ) : ℝ := if 0 ≤ x ∧ x ≤ 1 then fCost x else 1

















/-! ## Theorem 8, second half: Riemann integrability

The paper's Theorem 8 concludes that `f` is *Riemann integrable*.  In Mathlib
that is `BoxIntegral.HasIntegral I IntegrationParams.Riemann`, i.e. convergence
of the tagged-partition sums over all subdivisions whose mesh is below a
constant threshold.  The Riemann–Lebesgue criterion
`BoxIntegral.AEContinuous.hasBoxIntegral` supplies it from boundedness and a.e.
continuity, and identifies the value with the Lebesgue integral. -/

open BoxIntegral

/-- The unit box `[0,1]`, as a box in `Fin 1 → ℝ`. -/
def unitBox : Box (Fin 1) := ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num⟩

/-- `f` as a function of one coordinate. -/
noncomputable def FBar (v : Fin 1 → ℝ) : ℝ := fBar (v 0)











/-! ### Instantiating Riemann integrability at the evenly spaced subdivision -/















/-! ## The `gcd` term is negligible -/





/-! ## Theorem 10 -/





/-! ## The paper's form: `2∫₀^{1/2} f` -/















/-! ## Higher moments

The corollary after Theorem 8: if `X` is uniform on `[0,1/2]` then the `j`-th
moment of `f(X)` is `(∫₀^{1/2} f^j)/(1/2)`, and moments of all orders exist.

Existence is Theorem 8 again: `f^j` is bounded by `4^j` and continuous wherever
`f` is, so it is Riemann integrable by the same criterion.  The formula is the
normalisation of the uniform measure, which here is `2 • volume` restricted to
`(0,1/2]` — the measure with constant density `2` on `[0,1/2]`. -/







/-- **The uniform distribution on `[0,1/2]`**: density `2` there, zero elsewhere. -/
noncomputable def unifHalf : Measure ℝ := (2 : ℝ≥0∞) • volume.restrict (Set.Ioc 0 (1 / 2))

instance isProbabilityMeasure_unifHalf : IsProbabilityMeasure unifHalf := by
  constructor
  rw [unifHalf, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, smul_eq_mul]
  rw [show (1 : ℝ) / 2 - 0 = 1 / 2 by ring]
  rw [show ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
  rw [ENNReal.mul_div_cancel'] <;> norm_num













end BlockCycleRotation


