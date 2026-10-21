-- Prove2me | Definitions.Def_MatrixAnalytic_LogReduction_Passage
-- name    : MatrixAnalytic_LogReduction_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:29.222984+00:00
-- url     : https://prove2.me/theorems/3d0b1b2f-1c02-4b48-b022-4b875da1a123
-- title:
--   First-passage matrices G, Ĝ and the taboo probabilities of (8.37), (8.45)–(8.48) as path sums
-- statement:
--   Let $P$ be a transition matrix on the level–phase states $\mathbb N\times\iota$ and $\{X_t\}$ the chain. With $\gamma(i)=\inf\{t\ge1:X_t\in\ell(i)\}$ and $\delta(k)=\gamma(2^k)=\inf\{t\ge0:X_t\in\ell(2^k)\}$ (8.38), every probability below is a matrix indexed by the initial phase $i$ and the phase $j$ at the stopping epoch, defined as a sum over finite trajectories of products of one-step transition probabilities (values in $[0,\infty]$).
--
--   1. **First entrance**: for a set $T$, $\mathrm P[\sigma<\infty\ \&\ X_\sigma=y\mid X_0=x]$ with $\sigma=\inf\{t\ge1:X_t\in T\}$; and the same restricted to trajectories that visit a set $W$ at some epoch $0\le s<\sigma$.
--   2. $G_{ij}=\mathrm P[\gamma(0)<\infty\ \&\ X_{\gamma(0)}=(0,j)\mid X_0=(1,i)]$ (8.3), and $\hat G$, the matrix $G$ of the level-reversed QBD (8.25) in which $A_0$ and $A_2$ exchange roles.
--   3. $\mathrm P[\delta(k+1)<\gamma(0)\ \&\ X_{\delta(k+1)}\mid X_0\in\ell(2^k)]$ and $\mathrm P[\gamma(0)<\delta(k+1)\ \&\ X_{\gamma(0)}\mid X_0\in\ell(2^k)]$, the right-hand sides of (8.45) and (8.46).
--   4. $\mathrm P[\delta(k+1)<\gamma(0)\ \&\ X_{\delta(k+1)}\mid X_0\in\ell(1)]$ and $\mathrm P[\delta(k)<\gamma(0)<\delta(k+1)\ \&\ X_{\gamma(0)}\mid X_0\in\ell(1)]$, the right-hand sides of (8.47) and (8.48); the latter is also the $k$-th term of (8.37).
--
--   **Formalization Note** "Reaching $\ell(a)$ before $\ell(b)$, recorded with the phase" is encoded as the first entrance into $\ell(a)\cup\ell(b)$ occurring in $\ell(a)$. The boundary block of the level-reversed QBD is not specified on the page; a first passage from $\ell(1)$ to $\ell(0)$ never uses a transition out of $\ell(0)$, so it is taken to be $0$. None of these matrices is defined through an equation of the chapter.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 167, Eq. (8.3); p. 176, Eq. (8.25); p. 190, Eqs. (8.37)–(8.38); pp. 191–192, Eqs. (8.45)–(8.48)

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_QBD

namespace MatrixAnalytic.LogReduction

noncomputable section

open scoped ENNReal

/-!
The first-passage matrices of §8.1 and §8.4 of Latouche & Ramaswami (pp. 167, 190–192) for a
Markov chain with transition matrix `P` on the level–phase states `ℕ × ι`. With
`γ(i) = inf{t ≥ 1 : X_t ∈ ℓ(i)}` (p. 167) and `δ(k) = γ(2^k) = inf{t ≥ 0 : X_t ∈ ℓ(2^k)}` (8.38),
each probability `P[… & X_τ | X₀ ∈ ℓ(n)]` is the matrix indexed by the initial and the final
phase, written as a sum, over finite trajectories, of products of one-step transition
probabilities, with values in `ℝ≥0∞`. None of them is defined through an equation of the
chapter.
-/

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : ℕ × ι → ℕ × ι → ℝ) {t : ℕ} (ω : Fin (t + 1) → ℕ × ι) : ℝ≥0∞ :=
  ∏ m : Fin t, ENNReal.ofReal (P (ω m.castSucc) (ω m.succ))

open Classical in
/-- First entrance into a set `T`: `P[σ < ∞ and X_σ = y | X_0 = x]` where
`σ = inf{t ≥ 1 : X_t ∈ T}`, i.e. the sum over `t ≥ 1` of the probabilities of the trajectories
`x = ω₀, ω₁, …, ω_t = y` with `y ∈ T` and `ω₁, …, ω_{t-1} ∉ T`. -/
def firstEntrance (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- First entrance into `T` after a visit to `W`: `P[σ_W < σ and σ < ∞ and X_σ = y | X_0 = x]`
where `σ = inf{t ≥ 1 : X_t ∈ T}` and `σ_W = inf{t ≥ 0 : X_t ∈ W}`, i.e. the sum over the
trajectories counted by `firstEntrance P T x y` that visit `W` at some epoch `0 ≤ s < σ`. -/
def firstEntranceAfter (P : ℕ × ι → ℕ × ι → ℝ) (T W : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T) ∧
        ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ ω s ∈ W
    then pathWeightE P ω else 0

/-- `G` (8.3), p. 167: `G_{ij} = P[γ(0) < ∞ & X_{γ(0)} = (0, j) | X₀ = (1, i)]`, the probability,
starting from `(1, i)`, of reaching `ℓ(0)` in a finite time and doing so first in `(0, j)`. -/
def matG (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0) (1, i) (0, j)

/-- `Ĝ`, the matrix `G` of the level-reversed QBD (8.25), p. 176, whose transition matrix has
`A₂` in the place of `A₀` and `A₀` in the place of `A₂`. Its boundary block `B̂₁` is not
specified on the page, and a first passage from `ℓ(1)` to `ℓ(0)` never uses a transition out of
`ℓ(0)`, so the boundary block is taken to be `0`. -/
def matGhat (A₀ A₁ A₂ : ι → ι → ℝ) : ι → ι → ℝ≥0∞ :=
  matG (qbdP (fun _ _ => 0) A₂ A₁ A₀)

/-- The right-hand side of (8.45), p. 191:
`P[δ(k+1) < γ(0) & X_{δ(k+1)} | X₀ ∈ ℓ(2^k)]`, i.e. `[hitUp P k]_{ij}` is the probability,
starting from `(2^k, i)`, that the first visit to `ℓ(0) ∪ ℓ(2^{k+1})` is a visit to
`(2^{k+1}, j)`. -/
def hitUp (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level (2 ^ (k + 1))) (2 ^ k, i) (2 ^ (k + 1), j)

/-- The right-hand side of (8.46), p. 191:
`P[γ(0) < δ(k+1) & X_{γ(0)} | X₀ ∈ ℓ(2^k)]`, i.e. `[hitDown P k]_{ij}` is the probability,
starting from `(2^k, i)`, that the first visit to `ℓ(0) ∪ ℓ(2^{k+1})` is a visit to `(0, j)`. -/
def hitDown (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level (2 ^ (k + 1))) (2 ^ k, i) (0, j)

/-- The right-hand side of (8.47), p. 192:
`P[δ(k+1) < γ(0) & X_{δ(k+1)} | X₀ ∈ ℓ(1)]`, i.e. the probability, starting from `(1, i)`, that
the first visit to `ℓ(0) ∪ ℓ(2^{k+1})` is a visit to `(2^{k+1}, j)`. -/
def hitUpFromOne (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level (2 ^ (k + 1))) (1, i) (2 ^ (k + 1), j)

/-- The right-hand side of (8.48), p. 192, and the `k`-th term of (8.37), p. 190:
`P[δ(k) < γ(0) < δ(k+1) & X_{γ(0)} | X₀ ∈ ℓ(1)]`, i.e. the probability, starting from `(1, i)`,
that the first visit to `ℓ(0) ∪ ℓ(2^{k+1})` is a visit to `(0, j)` and that the level `2^k` is
visited before it (for `k = 0` this holds at time `0`). -/
def hitDownInBand (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntranceAfter P (level 0 ∪ level (2 ^ (k + 1))) (level (2 ^ k)) (1, i) (0, j)

end

end MatrixAnalytic.LogReduction


