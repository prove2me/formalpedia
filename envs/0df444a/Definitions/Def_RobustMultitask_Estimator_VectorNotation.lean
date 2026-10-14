-- Prove2me | Definitions.Def_RobustMultitask_Estimator_VectorNotation
-- name    : RobustMultitask_Estimator_VectorNotation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:01.970448+00:00
-- url     : https://prove2.me/theorems/47be7abb-eb81-4645-a7dd-7235bebc8cab
-- title:
--   §2, p. 8 — vector notation: ℓ¹, ℓ^∞, squared ℓ², ℓ⁰ and the restriction β_I
-- statement:
--   This file fixes the vector notation of §2 of Xu and Bastani. All vectors are indexed by a finite set $[d]=\{1,\dots,d\}$.
--
--   1. The $\ell^1$ norm $\|v\|_1=\sum_{i\in[d]}|v_{(i)}|$.
--   2. The $\ell^\infty$ norm $\|v\|_\infty=\max_{i\in[d]}|v_{(i)}|$.
--   3. The squared Euclidean norm $\|v\|_2^2=\sum_i v_{(i)}^2$.
--   4. The $\ell^0$ "norm" $\|v\|_0=|\{i : v_{(i)}\neq 0\}|$, the number of nonzero entries.
--   5. For an index set $I\subseteq[d]$, the vector $\beta_I$ obtained from $\beta$ by replacing the entries whose index is not in $I$ with $0$:
--   $$(\beta_I)_{(i)}=\begin{cases}\beta_{(i)}, & i\in I,\\ 0, & i\notin I.\end{cases}$$
--
--   These are the norms in which the paper measures sparsity ($\|\delta^j\|_0\le s$), estimation error ($\|\widehat\beta^j_{RM}-\beta^j\|_1$) and the noise event of Lemma 1 ($\|X^{j\top}\epsilon^j\|_\infty$).
--
--   **Formalization Note** Vectors are functions `Fin d → ℝ`, so the paper's index $i$ is Lean `i − 1`. The $\ell^\infty$ norm is a supremum over the finite index set, which equals the maximum for $d\ge 1$ and is $0$ for $d=0$. The squared norm is written `l2sq` and is also used for vectors of length $n_j$.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 8, §2 (Notation)

import Mathlib

namespace RobustMultitask.Estimator

/-- The ℓ¹ norm `‖v‖₁ = ∑ᵢ |v_(i)|` of a vector `v ∈ ℝᵈ`. -/
def l1 {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, |v i|

/-- The ℓ^∞ norm `‖v‖_∞ = maxᵢ |v_(i)|` of a vector `v ∈ ℝᵈ`. For `d ≥ 1` the supremum of the finite
family is its maximum; for `d = 0` (the empty vector) it is `0`. -/
noncomputable def linf {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ⨆ i, |v i|

/-- The squared Euclidean norm `‖v‖₂² = ∑ᵢ v_(i)²`. -/
def l2sq {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- The ℓ⁰ "norm" `‖v‖₀`: the number of nonzero entries of `v`. -/
noncomputable def l0 {d : ℕ} (v : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- `β_I` (§2, p. 8): the vector obtained from `β` by replacing the entries whose index is not in
`I` with `0`. -/
noncomputable def restrict {d : ℕ} (I : Finset (Fin d)) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if i ∈ I then v i else 0

end RobustMultitask.Estimator


