-- Prove2me | Definitions.Def_RandOrderSort_Supplement_RandOnlineAlg
-- name    : RandOrderSort_Supplement_RandOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:00:48.984949+00:00
-- url     : https://prove2.me/theorems/06236029-3bf2-4d5a-b522-2ce8328a22d7
-- title:
--   Randomized measurable online algorithms with full numerical values, their legality, cost and ratio
-- statement:
--   This is the algorithm class of the paper's lower bounds, which allow unrestricted auxiliary storage and access to the full numerical values rather than only comparisons.
--
--   A **randomized measurable online algorithm** $A$ consists of
--
--   1. a tape space: a measurable space $\Omega$ with a probability law $\mu$ (the law of the internal random tape $\zeta$); a deterministic algorithm is the case of a one-point tape;
--   2. a placement rule: for each input size $n$, arrival time $t$ (counted from $0$), tape $\zeta\in\Omega$ and values $X_0,\dots,X_t$ of the arrivals so far, a cell $\mathrm{place}_n^t(\zeta;X_0,\dots,X_t)\in\mathbb N$ for arrival $t$;
--   3. measurability: for each $n$ and $t$ the map $(\zeta,X_0,\dots,X_t)\mapsto\mathrm{place}_n^t(\zeta;X_0,\dots,X_t)$ is measurable.
--
--   Since the cell of arrival $t$ depends only on the tape and on the first $t+1$ values, placements are irrevocable and made before the next value is seen. The algorithm is **legal on size $n$** if for every tape $\zeta$ and every stream $(X_0,\dots,X_{n-1})\in[0,1]^n$ the $n$ arrivals go to $n$ distinct cells among $0,\dots,n-1$: every placement uses an empty cell of an array with exactly $n$ cells.
--
--   For the completed array $A[0],\dots,A[n-1]$ (cell $c$ holds the value of the arrival placed there), display (1) defines
--   $$\mathrm{cost}(A)=\sum_{i=0}^{n-2}\bigl|A[i+1]-A[i]\bigr|,\qquad \rho(A)=\begin{cases}\mathrm{cost}(A)/\mathrm{OPT}(X), & \mathrm{OPT}(X)>0,\\ 1, & \mathrm{OPT}(X)=0,\end{cases}$$
--   with $\mathrm{OPT}(X)=\max X-\min X$ the input range.
--
--   These objects are the setting of Theorems 1.3 and 1.4, the lower bounds matching the upper tail of Theorem 1.1.
--
--   **Formalization Note** The tape space may live in any universe. Legality is required only on inputs in $[0,1]^n$, where both lower bounds draw their values; this makes the class at least as large as the paper's. Cells are 0-based ($A[i]$ of the paper is cell $i-1$). $\mathrm{OPT}$ is the base mission's published `RandOrderSort.OPT`; the cost and ratio of the base mission are tied to its comparison-only class, so they are restated here with the same formula.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §1.1 display (1), p.3; "Matching lower bounds" and Theorem 1.3, p.4; §5.1, p.40 (model of the algorithm)

import Mathlib
import Definitions.Def_RandOrderSort_OnlineCmpAlg

namespace RandOrderSort

namespace Supplement

open MeasureTheory

/-! # Randomized measurable online algorithms with full numerical values (lower-bound model)

M. Kang, C. Fan, *Optimal High Probability Bounds for Random Order Online Sorting*,
arXiv:2610.15438 (version of 2026-11-01), §1.1, p.4 ("The lower bounds allow unrestricted auxiliary
storage and access to the full numerical values, rather than just comparisons"), and §5.1, p.40
("Fix an online algorithm A with random tape ζ independent of the input. Each placement is a
measurable function of (n, ζ, X_1, …, X_t), uses an empty cell, and is irrevocable. The algorithm
may use the full numerical values."). The cost and the ratio are display (1), p.3.

**Formalization Note.**
* The tape space `Ω` is an arbitrary measurable space (in any universe) carrying an arbitrary
  probability law `μ`; a deterministic algorithm is the case of a one-point tape.
* Arrivals and cells are 0-based. `place n t ζ v` is the cell of arrival `t`, computed from `n`, the
  tape `ζ` and the full real values `v 0, …, v t` of arrivals `0, …, t`. Seeing the whole prefix
  gives unrestricted auxiliary storage. Irrevocability holds by construction: the cell of a past
  arrival is a function of that arrival's own prefix only.
* Measurability (the paper's hypothesis): for each `n, t` the map `(ζ, v) ↦ place n t ζ v` is
  measurable, `ℕ` carrying its discrete σ-algebra.
* `LegalOn A n` ("uses an empty cell", "exactly n cells"): for every tape and every input vector
  in `[0,1]^n` the `n` arrivals go to `n` distinct cells among `0, …, n − 1`. Nothing is required
  outside `[0,1]^n`, where both lower bounds draw their inputs.
* `cost` and `ratio` are display (1) on the completed array; `OPT` is the published
  `RandOrderSort.OPT` (`max − min`); `ratio` is `cost/OPT` if `OPT > 0` and `1` otherwise.
-/

/-- **A possibly randomized measurable online algorithm** with access to the full numerical values
(Theorem 1.3, p.4; §5.1, p.40). -/
structure RandOnlineAlg.{u} where
  /-- The tape space. -/
  Ω : Type u
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The tape law. -/
  μ : Measure Ω
  /-- The tape law is a probability measure. -/
  [isProb : IsProbabilityMeasure μ]
  /-- `place n t ζ v`: the cell of arrival `t` on an input of size `n`, from the tape `ζ` and the
  values `v` of arrivals `0, …, t`. -/
  place : (n t : ℕ) → Ω → (Fin (t + 1) → ℝ) → ℕ
  /-- Each placement is a measurable function of the tape and the values seen so far. -/
  measurable_place : ∀ n t, Measurable (fun p : Ω × (Fin (t + 1) → ℝ) => place n t p.1 p.2)

attribute [instance] RandOnlineAlg.mΩ RandOnlineAlg.isProb

namespace RandOnlineAlg

universe u

variable (A : RandOnlineAlg.{u})

/-- The values of arrivals `0, …, t` of the stream `x`. -/
def prefixVals {n : ℕ} (x : Fin n → ℝ) (t : Fin n) : Fin (t.1 + 1) → ℝ :=
  fun a => x ⟨a.1, by have := a.2; have := t.2; omega⟩

/-- The cell into which `A` places arrival `t` of the stream `x` with tape `ζ`. -/
def cell {n : ℕ} (ζ : A.Ω) (x : Fin n → ℝ) (t : Fin n) : ℕ :=
  A.place n t.1 ζ (prefixVals x t)

/-- **Legality on size `n`**: for every tape and every stream in `[0,1]^n`, the `n` arrivals go to
`n` distinct cells, all among `0, …, n − 1`. -/
def LegalOn (n : ℕ) : Prop :=
  ∀ (ζ : A.Ω) (x : Fin n → ℝ), (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
    Function.Injective (A.cell ζ x) ∧ ∀ t, A.cell ζ x t < n

/-- The arrival stored in cell `c`, if any. -/
noncomputable def occupant {n : ℕ} (ζ : A.Ω) (x : Fin n → ℝ) (c : ℕ) : Option (Fin n) :=
  by classical exact if h : ∃ t, A.cell ζ x t = c then some (Classical.choose h) else none

/-- The completed array `A[c]`: the value stored in cell `c` (`0` for an empty cell, which a legal
run never leaves). -/
noncomputable def outVal {n : ℕ} (ζ : A.Ω) (x : Fin n → ℝ) (c : ℕ) : ℝ :=
  match A.occupant ζ x c with
  | some t => x t
  | none => 0

/-- `cost(A) = ∑_{i=1}^{n−1} |A[i+1] − A[i]|` (display (1)), in 0-based cells. -/
noncomputable def cost {n : ℕ} (ζ : A.Ω) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n - 1), |A.outVal ζ x (i + 1) - A.outVal ζ x i|

/-- The realized competitive ratio `ρ(A)` of (1) on the stream `x`: `cost/OPT` if `OPT > 0`, and
`1` if `OPT = 0` (`OPT` of the stream is that of its multiset). -/
noncomputable def ratio {n : ℕ} (ζ : A.Ω) (x : Fin n → ℝ) : ℝ :=
  if 0 < OPT x then A.cost ζ x / OPT x else 1

end RandOnlineAlg

end Supplement

end RandOrderSort


