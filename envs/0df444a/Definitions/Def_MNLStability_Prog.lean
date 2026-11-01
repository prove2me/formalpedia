-- Prove2me | Definitions.Def_MNLStability_Prog
-- name    : MNLStability_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:24.144529+00:00
-- url     : https://prove2.me/theorems/99c8385c-4d94-4001-8033-10867f3c6bd5
-- title:
--   Instrumented randomized programs and the unit-cost model
-- statement:
--   A **program** returning values of type $\alpha$ is a probability distribution over pairs (result, number of unit operations charged), built as a state monad over probability mass functions. Randomness enters only through two draws, and successive draws are independent.
--
--   The **cost model** is the unit-cost real RAM:
--
--   1. one unit for each $+,-,\times,/$, comparison, $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$, $\log$, operation on a natural number, list or array cell access, and loop dispatch;
--   2. one unit for a draw of the geometric law $\Pr[k]=(1-g)^kg$;
--   3. $\ell+1$ units for a draw from a categorical law given by $\ell$ masses (a scan).
--
--   The running time of a program is the counter at the end of a run. Loop combinators charge one dispatch per iteration (`foldP`, nested loops `foldProd`, loops over sublists, bounded compositions and non-increasing integer sequences), and `powP` computes $x^m$ by repeated squaring.
--
--   **Formalization Note** The paper fixes no machine model; this one is the standard model for its algorithm. A geometric draw at unit cost lets a simulated run skip the customers who buy nothing, so the cost of a simulation does not depend on the value of $M$.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.3, p.13 and Theorem 1, pp.5–6 (running times); cost model not fixed in the source

import Mathlib

open scoped ENNReal

namespace MNLStability

/-- Instrumented randomized programs: a probability distribution over the pair (result, number of
unit operations charged). Randomness enters only through `drawGeom` and `drawCat`, and successive
draws are independent, being `PMF` binds.

**Formalization Note (cost model).** SSRN:3498325 fixes no machine model. The mission uses the
unit-cost real RAM: one unit for each `+ − × /`, comparison, `⌊·⌋`, `⌈·⌉`, `Real.log`, operation on
a natural number, array or list cell read or write, and loop dispatch; one unit for a geometric
draw; `ℓ` units for a categorical draw over `ℓ` masses (a scan). The running time of a program is
the counter at the end of the run. -/
abbrev Prog (α : Type) : Type := StateT ℕ PMF α

/-- Charge `k` unit operations. -/
noncomputable def charge (k : ℕ) : Prog Unit := modify (· + k)

/-- A straight-line block of at most `k` unit operations with result `a`. -/
noncomputable def opn {α : Type} (k : ℕ) (a : α) : Prog α := do
  charge k
  pure a

/-- A loop over a list: one charged dispatch per iteration, threading an accumulator. -/
noncomputable def foldP {α β : Type} : List α → (β → α → Prog β) → β → Prog β
  | [], _, b => pure b
  | a :: l, f, b => do
    charge 1
    let b' ← f b a
    foldP l f b'

/-- Nested loops over a product of lists (an odometer): the body runs once per element of the
product, in lexicographic order, with one charged dispatch per step of each loop. -/
noncomputable def foldProd {α β : Type} : List (List α) → (β → List α → Prog β) → β → Prog β
  | [], f, b => f b []
  | c :: cs, f, b => foldP c (fun b a => foldProd cs (fun b' r => f b' (a :: r)) b) b

/-- The geometric law with success probability `g`: mass `(1 − g)^k · g` at `k`, the number of
failures before the first success, when these masses sum to `1` (that is, `0 < g ≤ 1`); otherwise
the point mass at `0`. -/
noncomputable def geomPMF (g : ℝ) : PMF ℕ :=
  if h : ∑' k, ENNReal.ofReal ((1 - g) ^ k * g) = 1 then
    ⟨fun k => ENNReal.ofReal ((1 - g) ^ k * g), h ▸ ENNReal.summable.hasSum⟩
  else PMF.pure 0

/-- One draw of the geometric law `geomPMF g`, at cost `1`. -/
noncomputable def drawGeom (g : ℝ) : Prog ℕ := do
  charge 1
  StateT.lift (geomPMF g)

/-- The categorical law with masses `p₀, p₁, …, p_{ℓ−1}` (index `k` has mass `p_k`), when they are
non-negative and sum to `1`; otherwise the point mass at `0`. -/
noncomputable def catPMF (p : List ℝ) : PMF ℕ :=
  if h : ∑' k, ENNReal.ofReal (p.getD k 0) = 1 then
    ⟨fun k => ENNReal.ofReal (p.getD k 0), h ▸ ENNReal.summable.hasSum⟩
  else PMF.pure 0

/-- One draw of an index from the finite probability vector `p`, at cost `p.length + 1` (a scan). -/
noncomputable def drawCat (p : List ℝ) : Prog ℕ := do
  charge (p.length + 1)
  StateT.lift (catPMF p)

/-- A loop over all sublists of `l` (each subset of the entries, in the order of `l`): one charged
dispatch per node of the binary inclusion tree. -/
noncomputable def foldSubsets {α β : Type} : List α → (β → List α → Prog β) → β → Prog β
  | [], f, b => f b []
  | a :: l, f, b => do
    charge 1
    let b' ← foldSubsets l f b
    foldSubsets l (fun b'' s => f b'' (a :: s)) b'

/-- A loop over all lists of `k` natural numbers with sum at most `B` (lexicographic order), one
charged dispatch per iteration of each nested loop. -/
noncomputable def foldComps {β : Type} : ℕ → ℕ → (β → List ℕ → Prog β) → β → Prog β
  | 0, _, f, b => f b []
  | k + 1, B, f, b =>
    foldP (List.range (B + 1)) (fun b x => foldComps k (B - x) (fun b' s => f b' (x :: s)) b) b

/-- The integers `lo, lo + 1, …, hi` (empty if `hi < lo`). -/
def intRange (lo hi : ℤ) : List ℤ := (List.range (hi - lo + 1).toNat).map fun k => lo + k

/-- A loop over all non-increasing lists of `k` integers with values in `[lo, hi]`, one charged
dispatch per iteration of each nested loop. -/
noncomputable def foldNoninc {β : Type} : ℕ → ℤ → ℤ → (β → List ℤ → Prog β) → β → Prog β
  | 0, _, _, f, b => f b []
  | k + 1, lo, hi, f, b =>
    foldP (intRange lo hi) (fun b x => foldNoninc k lo x (fun b' s => f b' (x :: s)) b) b

/-- `x ^ m` by repeated squaring: `⌊log₂ m⌋ + 1` rounds of at most `3` operations. -/
noncomputable def powP (x : ℝ) (m : ℕ) : Prog ℝ :=
  if _h : m = 0 then opn 1 1
  else do
    let y ← powP x (m / 2)
    opn 3 (if m % 2 = 0 then y * y else y * y * x)
termination_by m
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by norm_num)

end MNLStability


