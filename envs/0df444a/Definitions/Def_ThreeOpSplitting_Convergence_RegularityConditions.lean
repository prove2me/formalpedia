-- Prove2me | Definitions.Def_ThreeOpSplitting_Convergence_RegularityConditions
-- name    : ThreeOpSplitting_Convergence_RegularityConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:47:37.787292+00:00
-- url     : https://prove2.me/theorems/6274e2b1-7bc1-4f94-ada8-5597197f20e7
-- title:
--   Uniform monotonicity on bounded sets and demiregularity
-- statement:
--   Let $H$ be a real inner product space, $A : H \to 2^H$ and $C : H \to H$.
--
--   1. $A$ is **uniformly monotone on a set $S$** if there is a nondecreasing function $\varphi : [0, \infty) \to [0, +\infty]$ with $\varphi(0) = 0$ that vanishes only at $0$, such that
--   $$\langle x - y, u - v\rangle \ge \varphi(\|x - y\|) \quad \text{for all } x, y \in S,\ u \in Ax,\ v \in Ay.$$
--   2. $A$ is **uniformly monotone on every nonempty bounded subset of $\operatorname{dom}(A)$** if for each such subset $S$ there is such a $\varphi$ (which may depend on $S$).
--   3. $C$ is **demiregular at $x$** if every sequence $(x^k)$ with $x^k \rightharpoonup x$ and $Cx^k \to Cx$ (strongly) satisfies $x^k \to x$ (strongly).
--
--   These are the three alternative hypotheses (a), (b), (c) under which Theorem 2.1, Part 2 upgrades weak convergence of Algorithm 1 to strong convergence.
--
--   **Formalization Note** Footnote 2 of the paper asks only that $\varphi$ be increasing with $\varphi(0) = 0$; the proof of Theorem 2.1 (p. 837) uses a $\varphi$ that "vanishes only at 0", which is required here (without it $\varphi \equiv 0$ is allowed and Part 2(a) is false). "Increasing" is read as nondecreasing. The comparison of the real inner product with the extended value $\varphi(\cdot)$ is made in $[-\infty, +\infty]$. Footnote 3 is stated for set-valued $C$; since $C$ is single-valued here, $u = Cx$ and $u^k = Cx^k$.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 835, footnotes 2 and 3 of Theorem 2.1; p. 837 (φ vanishes only at 0)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace Filter Topology NNReal ENNReal

namespace ThreeOpSplitting.Convergence

/-- `A` is uniformly monotone on the set `S`: there is a nondecreasing
`φ : [0, ∞) → [0, +∞]` with `φ 0 = 0` that vanishes only at `0`, such that
`⟪x - y, u - v⟫ ≥ φ(‖x - y‖)` for all `x, y ∈ S`, `u ∈ A x`, `v ∈ A y`. -/
def IsUniformlyMonotoneOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (S : Set H) : Prop :=
  ∃ φ : ℝ≥0 → ℝ≥0∞, Monotone φ ∧ φ 0 = 0 ∧ (∀ t, φ t = 0 → t = 0) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ u ∈ A x, ∀ v ∈ A y,
      ((φ ‖x - y‖₊ : ℝ≥0∞) : EReal) ≤ ((⟪x - y, u - v⟫_ℝ : ℝ) : EReal)

/-- `A` is uniformly monotone on every nonempty bounded subset of `dom(A)`
(the function `φ` may depend on the subset). -/
def IsUniformlyMonotoneOnBounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) : Prop :=
  ∀ S : Set H, S ⊆ dom A → S.Nonempty → Bornology.IsBounded S → IsUniformlyMonotoneOn A S

/-- A single-valued operator `C` is demiregular at `x`: every sequence `x k ⇀ x` with
`C (x k) → C x` (strongly) converges strongly to `x`. -/
def IsDemiregularAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → H) (x : H) : Prop :=
  ∀ xs : ℕ → H, WeakTendsto xs x → Tendsto (fun k => C (xs k)) atTop (𝓝 (C x)) →
    Tendsto xs atTop (𝓝 x)

end ThreeOpSplitting.Convergence


