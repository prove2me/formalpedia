-- Prove2me | Definitions.Def_WassChanceCvx_pessimisticSet
-- name    : WassChanceCvx_pessimisticSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:26:08.233678+00:00
-- url     : https://prove2.me/theorems/5acad531-a69a-4f30-9150-5616a9f25f63
-- title:
--   Feasible region $\mathcal X^p$ of the pessimistic chance constraint (P-CC)
-- statement:
--   Let $E$ be a finite-dimensional real normed space (the space $\mathbb R^q$ of the uncertain vector $\xi$, with the norm of the Wasserstein distance), $\mathbb P$ a probability measure on $E$, $\delta,\epsilon\in\mathbb R$, and let $A(x)$ (rows $a_i(x)$, functionals on $E$) and $b(x)\in\mathbb R^k$ depend affinely on $x\in\mathbb R^n$. The **Wasserstein ambiguity set** is
--
--   $$
--   \mathcal P=\{\mathbb Q \text{ Borel probability measure on } E:\ d_W(\mathbb Q,\mathbb P)\le\delta\},\qquad d_W(\mathbb Q,\mathbb P)=\inf_{\pi\in\Pi(\mathbb Q,\mathbb P)}\int\|\xi-\xi'\|\,d\pi ,
--   $$
--
--   and the feasible region of the pessimistic chance constraint is
--
--   $$
--   \mathcal X^p=\Bigl\{x\in\mathbb R^n:\ \inf_{\mathbb Q\in\mathcal P}\mathbb Q\bigl[A(x)\xi\le b(x)\bigr]\ge1-\epsilon\Bigr\}.
--   $$
--
--   It is the set of decisions whose safety conditions hold with probability at least $1-\epsilon$ under every distribution within Wasserstein distance $\delta$ of the reference distribution $\mathbb P$.
--
--   **Formalization Note** The ball is the published `WassersteinDRO.StrongDuality.ambiguityBall δ 1 P univ` (type-1 distance, support $\Xi=E$), whose distance is valued in $[0,\infty]$, so the ball contains every Borel probability measure at finite distance $\le\delta$, with no moment condition. The infimum is taken in $[0,\infty]$ and compared with $1-\epsilon$; since all values lie in $[0,1]$ this is the real infimum of the paper.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, (1) and (P-CC), p.3; Notation, p.4; (CC), p.1

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_ambiguityBall
import Definitions.Def_WassChanceCvx_safeSet

open MeasureTheory

namespace WassChanceCvx

/-- **The feasible region `𝒳^p` of the pessimistic chance constraint (P-CC).**
Shen, Jiang, arXiv:2111.02486v2, p.3: "`𝒫 := {ℚ ∈ 𝒫₀ : d_W(ℚ, ℙ) ≤ δ}`, where `𝒫₀` is the set of
all probability distributions, `δ > 0` is a pre-specified radius of `𝒫`", with `d_W` the type-1
Wasserstein distance (1); (P-CC): "`inf_{ℚ∈𝒫} ℚ[A(x)ξ ≤ b(x)] ≥ 1 − ϵ`"; Notation, p.4: "`𝒳^p` …
the feasible region of (P-CC)". `A(x) ∈ ℝ^{m×q}` and `b(x) ∈ ℝ^m` are affine in `x` (p.1).

`pessimisticSet A b P δ ϵ = {x ∈ ℝⁿ : inf_{ℚ ∈ 𝒫} ℚ(𝒮(x)) ≥ 1 − ϵ}`, where `𝒫` is the type-1
Wasserstein ball of radius `δ` around `P`, `ambiguityBall δ 1 P univ`.

**Formalization Note.** The ball is the published `WassersteinDRO.StrongDuality.ambiguityBall`
with `p = 1` and support `Ξ = E`: all Borel probability measures `ℚ` on `E` with
`W₁(ℚ, P) ≤ δ`, where `W₁(ℚ, P) = inf_{π ∈ Π(ℚ, P)} ∫ ‖ξ − ξ'‖ dπ ∈ [0, ∞]` for the norm of `E`. No
moment condition restricts the ball. The infimum is taken in `[0, ∞]` (`⨅`), where it is the real
infimum of the paper (all values lie in `[0, 1]`; the ball contains `P`). The decision space is
`ℝⁿ = Fin n → ℝ`; `A` is an affine map into `k`-tuples of continuous linear functionals on `E`. -/
def pessimisticSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {n k : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → StrongDual ℝ E))
    (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ)) (P : Measure E) (δ ϵ : ℝ) : Set (Fin n → ℝ) :=
  {x | ENNReal.ofReal (1 - ϵ) ≤
    ⨅ Q ∈ WassersteinDRO.StrongDuality.ambiguityBall δ 1 P Set.univ, Q (safeSet (A x) (b x))}

end WassChanceCvx


