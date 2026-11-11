-- Prove2me | Definitions.Def_FullForesight_Randomized_IntervalSelection
-- name    : FullForesight_Randomized_IntervalSelection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:06.628056+00:00
-- url     : https://prove2.me/theorems/f0257869-0777-4fe5-bb8b-f9210313ae94
-- title:
--   Interval selection, the adaptivity gap $\Gamma(\ell, r, p)$, nonincreasing consecutive intervals and equalizing distributions (Definitions 2.2, 2.3)
-- statement:
--   The **interval-selection problem** (§2.4–2.5).
--
--   1. (Definition 2.2) An instance is a family of intervals $[\ell_0, r_0], \dots, [\ell_N, r_N]$ with $0 \le \ell_i \le r_i$ ($N \ge 0$) and a probability distribution $p = (p_0, \dots, p_N)$ on the indices.
--   2. If interval $i$ is chosen and interval $j$ is realized, the value is
--   $$v(i, j) = \ell_j + \big|[\ell_i, r_i] \cap [\ell_j, \infty)\big| = \ell_j + \max\big(0,\ r_i - \max(\ell_i, \ell_j)\big).$$
--   3. The **adaptivity gap** is
--   $$\Gamma(\ell, r, p) = \frac{\max_{i} \mathbb E_{j\sim p}[v(i, j)]}{\mathbb E_{j \sim p}[\max_{i} v(i, j)]},$$
--   with $\Gamma(\ell, r, p) = 1$ when the denominator is zero (footnote ¶).
--   4. (Definition 2.3) The intervals are **nonincreasing consecutive** if $\ell_0 = 0$, $\ell_{i+1} = r_i$ for $i < N$, and $r_0 - \ell_0 \ge \dots \ge r_N - \ell_N > 0$.
--   5. $p$ is **equalizing** if every fixed interval $i$ has the same expected value $\mathbb E_{j\sim p}[v(i, j)]$.
--
--   The numerator is the best value of a choice fixed before the draw; the denominator is the value of the best choice in hindsight.
--
--   **Formalization Note** Indices are `Fin (N+1)`; $\ell, r, p$ are real vectors. `val` uses the length $\max(0, r_i - \max(\ell_i, \ell_j))$ of the intersection, `fixedValue` is $\mathbb E_{j\sim p}[v(i,j)]$, `adaptiveValue` is the denominator, maxima are `Finset.sup'` over the nonempty index set, and `gap` returns $1$ exactly when `adaptiveValue` is $0$. "Nonincreasing" is `Antitone` of $i \mapsto r_i - \ell_i$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 8, Definition 2.2 and footnote ¶; p. 9, Definition 2.3

import Mathlib

/-!
# Interval selection and its adaptivity gap (Definitions 2.2 and 2.3)

Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, *Consistent
Submodular Maximization with Full Foresight*, STOC 2027 submission, p. 8 (Definition 2.2 and
footnote ¶), p. 9 (Definition 2.3).

* An interval-selection instance: intervals `[ℓ i, r i]`, `i = 0, …, N`, with `0 ≤ ℓ i ≤ r i`,
  and a probability distribution `p` on the indices.
* `val ℓ r i j = v(i, j) = ℓ_j + |[ℓ_i, r_i] ∩ [ℓ_j, ∞)| = ℓ_j + max(0, r_i − max(ℓ_i, ℓ_j))`.
* `gap ℓ r p = Γ(ℓ, r, p) = max_i E_{j∼p}[v(i, j)] / E_{j∼p}[max_i v(i, j)]`, and `1` when the
  denominator is zero.
* Nonincreasing consecutive intervals: `ℓ₀ = 0`, `ℓ_{i+1} = r_i`, and
  `r₀ − ℓ₀ ≥ ⋯ ≥ r_N − ℓ_N > 0`; `p` is equalizing if `E_{j∼p}[v(i, j)]` does not depend on `i`.
-/

namespace FullForesight.Randomized

variable {N : ℕ}

/-- An interval-selection instance: `0 ≤ ℓ i ≤ r i` and `p` a probability distribution. -/
def IsIntervalInstance (ℓ r p : Fin (N + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ r i) ∧ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- `v(i, j) = ℓ_j + |[ℓ_i, r_i] ∩ [ℓ_j, ∞)|` (the length of the intersection). -/
def val (ℓ r : Fin (N + 1) → ℝ) (i j : Fin (N + 1)) : ℝ :=
  ℓ j + max 0 (r i - max (ℓ i) (ℓ j))

/-- `E_{j∼p}[v(i, j)]`, the expected value of the fixed interval `i`. -/
def fixedValue (ℓ r p : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  ∑ j, p j * val ℓ r i j

/-- `E_{j∼p}[max_i v(i, j)]`, the expected value in hindsight. -/
noncomputable def adaptiveValue (ℓ r p : Fin (N + 1) → ℝ) : ℝ :=
  ∑ j, p j * Finset.univ.sup' Finset.univ_nonempty (fun i => val ℓ r i j)

/-- The adaptivity gap `Γ(ℓ, r, p)`, with `Γ = 1` when the denominator is zero (footnote ¶). -/
noncomputable def gap (ℓ r p : Fin (N + 1) → ℝ) : ℝ :=
  if adaptiveValue ℓ r p = 0 then 1
  else Finset.univ.sup' Finset.univ_nonempty (fixedValue ℓ r p) / adaptiveValue ℓ r p

/-- Nonincreasing consecutive intervals (Definition 2.3): `ℓ₀ = 0`, `ℓ_{i+1} = r_i` for `i < N`,
and `r₀ − ℓ₀ ≥ ⋯ ≥ r_N − ℓ_N > 0`. -/
def IsNonincConsecutive (ℓ r : Fin (N + 1) → ℝ) : Prop :=
  ℓ 0 = 0 ∧ (∀ i : Fin N, ℓ i.succ = r i.castSucc) ∧ Antitone (fun i => r i - ℓ i) ∧
    ∀ i, 0 < r i - ℓ i

/-- `p` is equalizing (Definition 2.3): every fixed interval has the same expected value. -/
def IsEqualizing (ℓ r p : Fin (N + 1) → ℝ) : Prop :=
  ∀ i i', fixedValue ℓ r p i = fixedValue ℓ r p i'

end FullForesight.Randomized


