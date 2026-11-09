-- Prove2me | Definitions.Def_PerturbedWF_MetricAllocation
-- name    : PerturbedWF_MetricAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:38:14.343586+00:00
-- url     : https://prove2.me/theorems/bf7ae1d5-67c6-4340-b8b4-51eafeaafb9e
-- title:
--   Metric allocation: reduced requests $F_t(x)=f_t(x_{r_t})$, separable requests, the work function (4.1) and $\mathrm{OPT}$
-- statement:
--   In **metric allocation** the configuration space is the simplex $\mathcal C=\{x\in[0,1]^n:\sum_ix_i=1\}$ and the request at time $t$ is a service cost $F_t:\mathcal C\to\mathbb R_{\ge0}$. After the reduction of [BC22] the paper analyzes requests supported at one point:
--   $$F_t(x)=f_t(x_{r_t}),\qquad r_t\in[n],$$
--   with $f_t:[0,1]\to\mathbb R_{\ge0}$ convex, continuous and monotone (non-decreasing or non-increasing; the direction may change from one time step to the next). A **separable** request is $F_t(x)=\sum_if_{t,i}(x_i)$ with every $f_{t,i}:[0,1]\to\mathbb R_{\ge0}$ convex and continuous.
--
--   Given an initial configuration $x_0\in\mathcal C$, the **work function** is $W_0(x)=\|x-x_0\|$ and
--   $$W_t(x)=\min_{y\in\mathcal C}\{W_{t-1}(y)+F_t(y)+\|x-y\|\},\qquad(4.1)$$
--   the cheapest offline cost of serving $F_1,\dots,F_t$ and ending at $x$. The optimal offline cost after $N$ requests is $\mathrm{OPT}=\min_{x\in\mathcal C}W_N(x)$.
--
--   **Formalization Note.** Requests are sequences indexed by $t\ge1$ (index $0$ unused). `maCost r f t x = f t (x (r t))` is the reduced service cost; `IsMAReq f` and `IsSepReq F` are the two request classes (only values on $[0,1]$, resp. on the simplex, are used). `workFn d x₀ F t` takes a general sequence of service costs $F$ and is a real infimum over the nonempty simplex; for nonnegative costs it is bounded below by $0$ and the infimum is attained, as in (4.1). `OPT` is the real infimum of $W_N$ over the simplex.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §2 'Work functions', p.6 (PDF p.7); §4 'Problem definition', 'Reduction' (footnote 1), 'Work function', eq. (4.1), pp.11–12 (PDF pp.12–13)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF

/-!
# Metric allocation: requests, the work function (4.1) and OPT

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §2 "Work functions", p.6 (PDF p.7); §4 "Problem
definition", "Reduction" (with footnote 1) and "Work function", pp.11–12 (PDF pp.12–13), eq. (4.1).

**Formalization Note.**
* The configuration space is `simplex ι`. Requests are in the reduced form the paper analyzes
  ("we can assume without loss of generality that `F_t(x) = f_t(x_{r_t})` … We thus design and
  analyze our algorithm for this version of the problem", p.12): a point `r t` and a function
  `f t : [0, 1] → ℝ_{≥0}` that is convex, continuous and monotone, where the direction of
  monotonicity may differ between time steps (footnote 1). Requests are sequences
  `r : ℕ → ι`, `f : ℕ → ℝ → ℝ` used at times `t = 1, …, N` (index `0` is unused); only the values
  of `f t` on `[0, 1]` are ever used.
* `maCost r f t x = f t (x (r t))` is the reduced service cost `F_t(x)`. The work function takes
  a general sequence of service costs `F : ℕ → (ι → ℝ) → ℝ` (evaluated on the simplex only), so
  that Appendix B's separable requests `F_t(x) = ∑_i f_{t,i}(x_i)` (`IsSepReq`, real-valued
  `f_{t,i}` as in the flow model of p.33, where arc costs are real) can be stated as well.
* `workFn d x₀ F t x` is `W_t(x)`: `W_0(x) = ‖x − x₀‖` and
  `W_t(x) = min_{y ∈ C} {W_{t−1}(y) + F_t(y) + ‖x − y‖}` (4.1), written as a real infimum over the
  nonempty simplex; for nonnegative requests it is bounded below by `0` and attained. The value is only
  used at points of the simplex (where every `transNorm` argument is zero-sum).
* `OPT d x₀ F N = min_{x ∈ C} W_N(x)`, a real infimum over the simplex.
-/

/-- A valid metric-allocation request function `f : [0, 1] → ℝ_{≥0}`: convex, continuous,
monotone (non-decreasing or non-increasing) and nonnegative on `[0, 1]`. -/
def IsMAReq (f : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc 0 1) f ∧ ContinuousOn f (Set.Icc 0 1) ∧
    (MonotoneOn f (Set.Icc 0 1) ∨ AntitoneOn f (Set.Icc 0 1)) ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f s

/-- The service costs of reduced requests: `F_t(x) = f_t(x_{r_t})`. -/
def maCost {ι : Type} (r : ℕ → ι) (f : ℕ → ℝ → ℝ) : ℕ → (ι → ℝ) → ℝ :=
  fun t x => f t (x (r t))

/-- A real-valued separable convex service cost on the simplex (§4, p.11; Appendix B, p.33):
`F(x) = ∑_i f_i(x_i)` on the simplex with every `f_i : [0, 1] → ℝ_{≥0}` convex and continuous. -/
def IsSepReq {ι : Type} [Fintype ι] (F : (ι → ℝ) → ℝ) : Prop :=
  ∃ g : ι → ℝ → ℝ, (∀ i, ConvexOn ℝ (Set.Icc 0 1) (g i) ∧ ContinuousOn (g i) (Set.Icc 0 1) ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g i s) ∧ ∀ x ∈ simplex ι, F x = ∑ i, g i (x i)

/-- The metric-allocation work function for service costs `F t` (`t ≥ 1`):
`W_0(x) = ‖x − x₀‖` and (4.1) `W_{t+1}(x) = inf_{y ∈ C} {W_t(y) + F_{t+1}(y) + ‖x − y‖}`. -/
noncomputable def workFn {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (x₀ : ι → ℝ)
    (F : ℕ → (ι → ℝ) → ℝ) : ℕ → (ι → ℝ) → ℝ
  | 0, x => transNorm d (x - x₀)
  | t + 1, x => ⨅ y : simplex ι,
      workFn d x₀ F t y + F (t + 1) (y : ι → ℝ) + transNorm d (x - y)

/-- The optimal offline cost `OPT = min_{x ∈ C} W_N(x)` after `N` requests. -/
noncomputable def OPT {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (x₀ : ι → ℝ)
    (F : ℕ → (ι → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ⨅ x : simplex ι, workFn d x₀ F N x

end PerturbedWF


