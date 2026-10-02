-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization
-- name    : ProcessingNetworks_ProportionalFairness_PFOptimization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:11:59.100248+00:00
-- url     : https://prove2.me/theorems/dd53fa67-8b9d-4b05-821b-7c6c0bf5687b
-- title:
--   The concave PF optimization problem: domain, objective, maximizer, and ψ
-- statement:
--   **Section 10.1's concave optimization problem.** Fix a bounded, closed, convex, monotone,
--   nontrivial set $\mathcal A \subset \mathbb R^I_+$ (`IsPFDomain`). For $z \in \mathbb R^I_+$,
--   $f(z,x) := \sum_i z_i \log(x_i)$ (Eq. 10.2), with the convention $\log(0) = -\infty$,
--   $0\log(0) = 0$. The **PF allocation function** $\psi(z) := \operatorname{argmax}_{x\in\mathcal
--   A} f(z,x)$ (Eqs. 10.4-10.5).
--
--   **Formalization note.** `f` is `EReal`-valued via `extLog` (`Real.log` at `0` is `0` in
--   Mathlib, not `-∞`, so it cannot be used directly without corrupting the boundary behavior
--   Lemma 10.1 depends on). `EReal`'s built-in `0 * y = 0` convention (for every `y`, including
--   `⊥`) automatically reproduces `0 log(0) = 0` with no extra case split.
--   `IsPFMaximizer`/`psi` avoid `sSup`/`⨆` entirely, per this series' junk-value-avoidance
--   convention (mission III onward).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 183-184, Section 10.1, Eqs. (10.1),(10.2),(10.4),(10.5)

import Mathlib

namespace ProcessingNetworks.ProportionalFairness

open Classical

/-- The concave-optimization-problem domain (Section 10.1, before Eq. (10.1)): `A ⊂ ℝ^I_+` is
bounded, closed, convex, monotone (10.1) (downward-closed among nonnegative vectors), and
nontrivial (contains a strictly positive point). -/
def IsPFDomain {I : ℕ} (AllocSet : Set (Fin I → ℝ)) : Prop :=
  Bornology.IsBounded AllocSet ∧ IsClosed AllocSet ∧ Convex ℝ AllocSet ∧
    (∀ x ∈ AllocSet, ∀ y : Fin I → ℝ, (∀ i, 0 ≤ y i) → y ≤ x → y ∈ AllocSet) ∧
    ∃ x ∈ AllocSet, ∀ i, 0 < x i

/-- The extended logarithm implementing the book's convention `log(0) = -∞` (Eq. 10.2), as an
`EReal` rather than `Real.log` (whose Mathlib value at `0` is `0`, not `-∞`, and so would silently
misrepresent the boundary behaviour the optimization problem (10.3)-(10.4) depends on). -/
noncomputable def extLog (x : ℝ) : EReal :=
  if x = 0 then ⊥ else (Real.log x : EReal)

/-- The objective `f(z,x) := ∑_i z_i log(x_i)` (Eq. 10.2), `EReal`-valued via `extLog`. Because
`EReal`'s multiplication satisfies `0 * y = 0` for every `y` (including `y = ⊥`), the term for
coordinate `i` automatically evaluates to `0` when `z_i = 0`, matching the book's own convention
`0 log(0) = 0` without any extra case split. -/
noncomputable def f {I : ℕ} (z x : Fin I → ℝ) : EReal :=
  ∑ i, (z i : EReal) * extLog (x i)

/-- `x` is a maximizer of `f(z,·)` over `AllocSet` — the content of (10.4)'s `argmax`, phrased as
"feasible and dominates every feasible alternative" rather than via an explicit `sSup`/`⨆`
expression, avoiding any junk-value risk (the convention this series has followed since
mission III). -/
def IsPFMaximizer {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (z x : Fin I → ℝ) : Prop :=
  x ∈ AllocSet ∧ ∀ y ∈ AllocSet, f z y ≤ f z x

/-- The PF allocation function `ψ` (Eqs. 10.4-10.5): an arbitrary maximizer of `f(z,·)` over
`AllocSet`, with every coordinate `i` such that `z_i = 0` forced to `0` per the convention (10.5)
(well-defined regardless of which maximizer is chosen on those coordinates, since `f`'s value does
not depend on them). Junk value `0` at every coordinate when no maximizer exists. -/
noncomputable def psi {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (z : Fin I → ℝ) : Fin I → ℝ :=
  fun i =>
    if 0 < z i then
      (if h : ∃ x, IsPFMaximizer AllocSet z x then (Classical.choose h) i else 0)
    else 0

end ProcessingNetworks.ProportionalFairness


