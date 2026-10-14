-- Prove2me | Definitions.Def_GreedyRS_Greedy_Setting
-- name    : GreedyRS_Greedy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:26.135533+00:00
-- url     : https://prove2.me/theorems/b76659c1-dd8e-4d6f-9ab0-380ead5ab43a
-- title:
--   §2, Procedures 1–2, §3.2, §4.1, §5.2 — normal observation array, (explore-first) greedy procedure, PCS, running minimum and crossing times, C(x), C(x; n0)
-- statement:
--   This file fixes the model and the objects of Li, Fan and Hong's analysis of the greedy procedure for fixed-budget ranking and selection (R&S).
--
--   **Observations and running averages.** There are $k$ alternatives, indexed $0,1,\dots,k-1$; index $0$ is the paper's alternative 1, the unique best. An observation array $x=(x_{ij})$ records the $(j+1)$-th observation $x_{ij}$ of alternative $i$. The running average of alternative $i$ after $n\ge 1$ observations is
--   $$\bar X_i(n)=\frac1n\sum_{j=0}^{n-1}x_{ij}.$$
--
--   **The (explore-first) greedy procedure.** Given current sample sizes $s=(s_i)$, the *leader* is the smallest index $i<k$ whose running average $\bar X_i(s_i)$ is maximal among alternatives $0,\dots,k-1$. The explore-first greedy procedure with $n_0$ initial observations per alternative and total budget $B$ starts from $s_i=n_0$ for all $i$ and performs $B-n_0k$ greedy steps (none if $B\le n_0k$), each of which gives one more observation to the current leader; it then selects the final leader. The greedy procedure (Procedure 1 of the paper) is the case $n_0=1$: one observation from each alternative, then always sample the current sample-best, until $\sum_i n_i=B$, and select the sample-best.
--
--   **The normal model and the PCS.** An array of random variables $X_{ij}$ on a probability space $(\Omega,P)$ is a *normal array* with means $\mu_i$ and variances $v_i=\sigma_i^2$ if each $X_{ij}$ is measurable with law $N(\mu_i,\sigma_i^2)$ and the whole family $\{X_{ij}\}_{i,j}$ is mutually independent. The probability of correct selection of problem $k$ with budget $B$ is
--   $$\mathrm{PCS}=P\{\text{the procedure run on }(X_{ij}(\omega))\text{ selects alternative }0\}.$$
--
--   **Running minimum, argmin and boundary crossing.** For a real sequence $y(1),y(2),\dots$ and $n_0\ge1$:
--   1. "$\min_{n\ge n_0}y(n)>a$" means that $y$ is bounded below on $\{n\ge n_0\}$ and $\inf_{n\ge n_0}y(n)>a$;
--   2. the boundary is $\bar X^*(n_0)=\inf_{n\ge n_0}y(n)$;
--   3. $N^*(n_0)$ is the first index $m\ge n_0$ at which $y(m)=\min_{n\ge n_0}y(n)$, and $+\infty$ if the minimum is not attained;
--   4. the boundary-crossing time of a level $b$ is $N(b;n_0)=\inf\{n\ge n_0: y(n)<b\}$, and $+\infty$ if $y$ never drops below $b$.
--
--   **The standard normal running average and $C(x)$.** Let $Z_1,Z_2,\dots$ be i.i.d. $N(0,1)$ and $\bar Z(n)=\frac1n\sum_{j=1}^nZ_j$. The crossing time is $\tilde N(x;n_0)=\inf\{n\ge n_0:\bar Z(n)<x\}\in\{n_0,n_0+1,\dots\}\cup\{\infty\}$, with $\tilde N(x)=\tilde N(x;1)$, and $C(x;n_0)=\mathrm E[\tilde N(x;n_0)]\in[0,\infty]$. Finally, with $\Phi$ the standard normal distribution function,
--   $$C(x)=\exp\Bigl(\sum_{n=1}^\infty\frac1n\,\Phi(-\sqrt n\,x)\Bigr),$$
--   which is finite for $x>0$.
--
--   These objects are shared by the four missions drawn from the paper: the greedy procedure's sample optimality (Theorem 1) and its tightness (Theorem 2), the consistency of the explore-first greedy procedure (Theorem 4), and the decay of its greedy-phase budget (Lemma 6). All of them compare the boundary-crossing times of the inferior alternatives with the crossing time $\tilde N$ of the standard normal running average.
--
--   **Formalization Note** Crossing times and argmins take values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), so that "never crosses" is $\infty$ rather than a junk $0$. "$\min>a$" carries the bounded-below condition, because a Lean infimum of an unbounded-below set is $0$. Ties in every arg max go to the smallest index; under normality ties have probability zero. The number of greedy steps $B-n_0k$ uses truncated subtraction, so the procedure is total for $B<n_0k$. Running averages are only meaningful for $n\ge1$ (Lean gives $\bar X_i(0)=0$), so every statement takes $n_0\ge1$. Lean's `tsum` returns $0$ for a divergent series, so $C(x)$ is only meaningful for $x>0$; every statement of the mission applies it at a positive argument. The law $N(\mu,v)$ is Mathlib's `gaussianReal μ v` with variance $v\ge0$; the i.i.d. standard normal sequence is the infinite product measure `Measure.infinitePi`.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, pp. 8–14: §2 (p. 8), Procedure 1 (p. 10), §3.2 (pp. 11–12), §4.1 (pp. 13–14, Ñ(x) and C(x)); Procedure 2 (p. 21) and C(x; n0) (p. 22) for the n0-generalization

import Mathlib

namespace GreedyRS.Greedy

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ### Observations, running averages and the greedy procedure (§2, Procedure 1) -/

/-- Running average of alternative `i` after `n` observations: `X̄_i(n) = (1/n) ∑_{j<n} x i j`.
Only used for `n ≥ 1`. -/
noncomputable def runMean (x : ℕ → ℕ → ℝ) (i n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, x i j) / n

/-- Some alternative among `0, …, k-1` has a maximal running average (`k > 0`). -/
theorem exists_leader (k : ℕ) (hk : 0 < k) (x : ℕ → ℕ → ℝ) (s : ℕ → ℕ) :
    ∃ i, i < k ∧ ∀ j < k, runMean x j (s j) ≤ runMean x i (s i) := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range k)
    (fun i => runMean x i (s i)) ⟨0, Finset.mem_range.2 hk⟩
  exact ⟨i, Finset.mem_range.1 hi, fun j hj => hmax j (Finset.mem_range.2 hj)⟩

open Classical in
/-- The current leader among alternatives `0, …, k-1` given sample sizes `s`: the smallest index whose
running average is maximal (`0` when `k = 0`). -/
noncomputable def leader (k : ℕ) (x : ℕ → ℕ → ℝ) (s : ℕ → ℕ) : ℕ :=
  if h : 0 < k then Nat.find (exists_leader k h x s) else 0

/-- Sample sizes after `m` greedy steps of the explore-first greedy procedure started with `n0`
observations from each alternative: each step gives one more observation to the current leader. -/
noncomputable def efgSizes (k n0 : ℕ) (x : ℕ → ℕ → ℝ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => n0
  | m + 1 =>
    let s := efgSizes k n0 x m
    Function.update s (leader k x s) (s (leader k x s) + 1)

/-- The alternative selected by the explore-first greedy procedure with total budget `B`: the leader
after the `B - n0 * k` greedy steps of the loop "while ∑ n_i < B". -/
noncomputable def efgSelect (k n0 B : ℕ) (x : ℕ → ℕ → ℝ) : ℕ :=
  leader k x (efgSizes k n0 x (B - n0 * k))

/-- The greedy procedure (Procedure 1) is the explore-first greedy procedure with `n0 = 1`. -/
noncomputable def greedySelect (k B : ℕ) (x : ℕ → ℕ → ℝ) : ℕ :=
  efgSelect k 1 B x

/-! ### The normal observation model and the PCS (§2) -/

/-- The observation array `X i j` (the `(j+1)`-th observation of alternative `i`) is a mutually
independent family of measurable random variables with `X i j ∼ N(μ i, v i)`. -/
structure NormalArray {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) : Prop where
  meas : ∀ i j, Measurable (X i j)
  law : ∀ i j, P.map (X i j) = gaussianReal (μ i) (v i)
  indep : iIndepFun (fun p : ℕ × ℕ => X p.1 p.2) P

/-- Probability of correct selection of the explore-first greedy procedure on problem `k` (alternatives
`0, …, k-1`, alternative `0` the best) with budget `B`. -/
noncomputable def pcs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (k n0 B : ℕ) : ℝ≥0∞ :=
  P {ω | efgSelect k n0 B (fun i j => X i j ω) = 0}

/-! ### The standard normal running average, crossing times and `C(x)` (§4.1) -/

/-- The law of an i.i.d. `N(0,1)` sequence `Z_1, Z_2, …` on `ℕ → ℝ`. -/
noncomputable def stdNormalSeq : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- Running average `Z̄(n) = (1/n) ∑_{j<n} z j`. -/
noncomputable def zbar (z : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, z j) / n

/-- Crossing time `Ñ(x; n0) = inf {n ≥ n0 : Z̄(n) < x}`, equal to `⊤` when the walk never crosses. -/
noncomputable def crossTime (x : ℝ) (n0 : ℕ) (z : ℕ → ℝ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : n0 ≤ n ∧ zbar z n < x), (n : ℕ∞)

/-- `C(x; n0) = E[Ñ(x; n0)] ∈ [0, ∞]`. -/
noncomputable def Cn0 (x : ℝ) (n0 : ℕ) : ℝ≥0∞ :=
  ∫⁻ z, ((crossTime x n0 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq

/-- The standard normal cumulative distribution function `Φ`. -/
noncomputable def Phi (t : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) t

/-- `C(x) = exp(∑_{n ≥ 1} (1/n) Φ(-√n x))`. The series converges only for `x > 0`; every use is at a
positive argument. -/
noncomputable def Cfun (x : ℝ) : ℝ :=
  Real.exp (∑' n : ℕ, Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1))

/-! ### Running minimum, argmin and boundary crossing of a path (§3.2) -/

/-- "`min_{n ≥ n0} y(n) > a`": the path is bounded below from `n0` on and its infimum exceeds `a`. -/
def AboveFrom (y : ℕ → ℝ) (n0 : ℕ) (a : ℝ) : Prop :=
  BddBelow (Set.range fun n => y (n0 + n)) ∧ a < ⨅ n, y (n0 + n)

/-- The boundary `X̄_1^*(n0) = min_{n ≥ n0} y(n)` (as an infimum). -/
noncomputable def boundary (y : ℕ → ℝ) (n0 : ℕ) : ℝ :=
  ⨅ n, y (n0 + n)

/-- `N_1^*(n0)`: the first index `m ≥ n0` at which the minimum of `y` over `n ≥ n0` is attained;
`⊤` if it is never attained. -/
noncomputable def argminFrom (y : ℕ → ℝ) (n0 : ℕ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : n0 ≤ m ∧ ∀ n, n0 ≤ n → y m ≤ y n), (m : ℕ∞)

/-- Boundary-crossing time `N_i(b; n0) = inf {n ≥ n0 : y(n) < b}`; `⊤` if it never happens. -/
noncomputable def crossBelow (y : ℕ → ℝ) (b : ℝ) (n0 : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : n0 ≤ n ∧ y n < b), (n : ℕ∞)

end GreedyRS.Greedy


