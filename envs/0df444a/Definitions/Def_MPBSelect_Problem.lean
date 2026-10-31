-- Prove2me | Definitions.Def_MPBSelect_Problem
-- name    : MPBSelect_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:38.896982+00:00
-- url     : https://prove2.me/theorems/2be9bf3c-d428-40fd-8e28-046a318b635a
-- title:
--   The most-probable-best problem with known means and variances, and the preference probability $\sum_b p_b\mathbf 1\{i=i^b\}$
-- statement:
--   There are $k$ simulated **solutions** $i=1,\dots,k$ and $B$ **input parameters** $\theta_1,\dots,\theta_B$, which form the finite support of the input distribution $\pi$:
--   $$
--   \pi=\{p_1,\dots,p_B\},\qquad p_b>0,\qquad \sum_{b=1}^B p_b=1 .
--   $$
--   For each solution $i$ and parameter $\theta_b$, $y_i(\theta_b)$ is the conditional mean of the simulation output of $i$ given $\theta_b$ (smaller is better), and $\lambda_i(\theta_b)>0$ is the standard deviation of the simulation error, so that the output is $N(y_i(\theta_b),\lambda_i^2(\theta_b))$.
--
--   1. The **conditional optimum** at $\theta_b$ is $i^b=\arg\min_i y_i(\theta_b)$.
--   2. The **preference probability** of solution $i$ is
--   $$
--   \sum_{b=1}^B p_b\,\mathbf 1\{i=i^b\}=\mathrm P_\pi(\Theta_i),\qquad \Theta_i=\{\theta_b: i=i^b\},
--   $$
--   the probability of its **favorable set** $\Theta_i$.
--   3. The **most probable best** (MPB) $i^*$ is the solution with the largest preference probability.
--
--   The standing assumptions of the paper are: (i) for each $\theta_b$, the means $y_i(\theta_b)$, $i=1,\dots,k$, are pairwise distinct (so $i^b$ is unique), and (ii) $i^*$ is unique. The data of a problem are $k\ge 2$, $B$, $p$, $y$, $\lambda$, together with $i^b$ and $i^*$, each pinned down by its defining property.
--
--   These are the objects on which the relaxed budget-allocation problem (20) and its optimality conditions (Theorem 3) are built.
--
--   **Formalization Note** Solutions are indexed by `Fin k`, parameters by `Fin B` (only the index of $\theta_b$ matters). `ib` and `istar` are fields characterized uniquely by `ib_spec` (strict minimizer of $y_\cdot(\theta_b)$) and `istar_spec` (strict maximizer of the preference probability, which is assumption (ii) together with definition (2)). `lam` is the standard deviation: the paper calls $\lambda_i(\theta)$ "the simulation error variance", but its Model (4) writes the variance as $\lambda_i^2(\theta)$ and every formula uses $\lambda^2$. The readings $k\ge2$ (for $k=1$ the objective of (20) is a minimum over an empty set), $p_b>0$ ($\Theta$ is the support of $\pi$; (17) divides by $p_b$) and $\lambda>0$ are recorded on the theorem items.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §2, pp.6–7, (1)–(3) and assumptions (i)–(ii); §3, Model (4), p.8

import Mathlib

namespace MPBSelect

open Finset

/-- **Preference probability of solution `i`.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, §2, (2), p.7: under
assumptions (i)–(ii) "(2) further simplifies to i∗ = arg max_{1≤i≤k} Σ_{b=1}^B pb 1{i = i^b}".

`prefProb p ib i = Σ_b p_b 1{i = i^b}` is the probability, under the weights `p`, of the set of
parameters at which `i` is the conditional optimum, i.e. `P_π(Θ_i)` for the favorable set (3).

**Formalization Note** Solutions are indexed by `Fin k`, parameters `θ_1, …, θ_B` by `Fin B`
(only the index of `θ_b` matters), and the conditional optima `i^b` are passed as a function
`ib : Fin B → Fin k`. -/
def prefProb {k B : ℕ} (p : Fin B → ℝ) (ib : Fin B → Fin k) (i : Fin k) : ℝ :=
  ∑ b, if ib b = i then p b else 0

/-- **The most-probable-best (MPB) selection problem with known means and variances.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, §2, pp.6–7, and
Model (4), p.8.

The data are `k` solutions and `B` parameters `θ_1, …, θ_B` forming the finite support of the
input distribution `π = {p_1, …, p_B | Σ_b p_b = 1}` (p.7); the conditional mean
`y_i(θ_b) = y i b` of solution `i` at `θ_b` ("smaller is better": "i^b := arg min_i yi(θb) is the
conditional optimum at θb", p.7); and the simulation-error standard deviations
`λ_i(θ_b) = lam i b` (Model (4): `Y_i(θ) ∼ N(η_i(θ), λ²_i(θ))`, p.8). The standing assumptions
of p.7 are carried as fields: "(i) for each θb, yi(θb) ≠ yj(θb) holds for all i ≠ j, which
implies i^b is unique for each θb; and (ii) i∗ is unique".

Fields:
* `ib b` is the conditional optimum `i^b` at `θ_b`, characterized by `ib_spec` (the strict
  minimizer of `y · b`);
* `istar` is the MPB `i*`, characterized by `istar_spec` (the strict maximizer of the
  preference probability, definition (2) together with assumption (ii));
* `two_le_k`: there are at least two solutions;
* `p_pos`, `p_sum`: `p` is a probability vector with positive entries (`Θ` is the support);
* `y_injective`: assumption (i);
* `lam_pos`: the standard deviations are positive.

**Formalization Note**
1. `k ≥ 2` is a reading: for `k = 1` the set `Ξ` of problem (20) is empty and its objective is
   undefined; the paper compares "all k solutions".
2. `p_b > 0` is a reading: `Θ` is the *support* of `π`, and (17) divides by `p_b`.
3. `lam` is a **standard deviation**: the page calls `λ_i(θ)` "the simulation error variance",
   but Model (4) writes the variance as `λ²_i(θ)` and every formula uses `λ²`. `lam > 0` is a
   reading (the formulas divide by `λ²`).
4. `i^b` and `i*` are data fields pinned down uniquely by `ib_spec` and `istar_spec`. -/
structure Problem (k B : ℕ) where
  /-- weights `p_b = π(θ_b)` of the parameters -/
  p : Fin B → ℝ
  /-- conditional means `y_i(θ_b)` -/
  y : Fin k → Fin B → ℝ
  /-- simulation-error standard deviations `λ_i(θ_b)` -/
  lam : Fin k → Fin B → ℝ
  /-- conditional optimum `i^b` at `θ_b` -/
  ib : Fin B → Fin k
  /-- the most probable best `i*` -/
  istar : Fin k
  two_le_k : 2 ≤ k
  p_pos : ∀ b, 0 < p b
  p_sum : ∑ b, p b = 1
  /-- assumption (i), p.7 -/
  y_injective : ∀ b, Function.Injective (fun i => y i b)
  /-- `i^b = arg min_i y_i(θ_b)` -/
  ib_spec : ∀ b j, j ≠ ib b → y (ib b) b < y j b
  /-- `i* = arg max_i Σ_b p_b 1{i = i^b}`, unique (assumption (ii)) -/
  istar_spec : ∀ j, j ≠ istar → prefProb p ib j < prefProb p ib istar
  lam_pos : ∀ i b, 0 < lam i b

end MPBSelect


