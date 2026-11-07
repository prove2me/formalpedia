-- Prove2me | Definitions.Def_TTTSampling_mixPrefix
-- name    : TTTSampling_mixPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:04.827307+00:00
-- url     : https://prove2.me/theorems/0c3c24fa-a2eb-4181-9279-dd10a05dc115
-- title:
--   Mean density $\bar\eta$ of a class, consistency filter, ratio denominator, Bernoulli coin, next-symbol law
-- statement:
--   Let $\mathcal G$ be a finite class of distributions on $\Sigma^n$, $\hat\mu$ an oracle and $R>0$.
--
--   1. The **mean density** is $\bar\eta(x)=\frac1{|\mathcal G|}\sum_{\eta\in\mathcal G}\eta(x)$ at every prefix $x$, and its conditional is $\bar\eta(x'\mid x)=\bar\eta(x')/\bar\eta(x)$.
--   2. A density $\eta$ is **consistent** with $\hat\mu$ at $x$ if $\frac1R\le\frac{\hat\mu(x)}{\eta(x)}\le R$.
--   3. For a stage start $u$ and a node $x$, the **denominator** of the ratio tests of Algorithm 2 is $\hat\mu(u)\cdot\bar\eta(x\mid u)$.
--   4. $\mathrm{Ber}(q)$ is the Bernoulli coin with parameter $q\in[0,1]$.
--   5. The **next symbol** at $v$ is drawn from $\bar\eta(\cdot\mid v)$: $y$ with probability $\bar\eta(v\circ y)/\bar\eta(v)$.
--
--   These are the building blocks of Algorithm 2 (Lines 3, 6–7, 9–10, 13–14, 16, 18) and of the sets (10), (P1), (P2).
--
--   **Formalization Note** The mean of the empty class is $0$. Consistency is multiplicative ($\eta(x)\le R\hat\mu(x)$ and $\hat\mu(x)\le R\eta(x)$), as are all ratio tests, realizing $0/0=1$. Coin parameters are clamped to $[0,1]$, a no-op on reachable states. The next symbol is drawn proportionally to $\bar\eta(v\circ y)$, which is $\bar\eta(\cdot\mid v)$ because the children's masses sum to $\bar\eta(v)$; if all are $0$ (unreachable when $\mu^\star$ is in the class) the draw returns "none" and the trial ends.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Algorithm 2, p.11 (PDF p.13); (10), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_TTTSampling_prefixMass

open Classical

namespace TTTSampling

/-- The **mean density** `η̄ = (1/|𝒢|) Σ_{η∈𝒢} η` of a finite class `𝒢`, evaluated at a prefix.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Algorithm 2, Lines 3
and 16, printed p.11 (PDF p.13), and the mean `η̄_{t−1,w′}` after (10), printed p.19 (PDF p.21).
`mixPrefix 𝒢 x = (1/|𝒢|) Σ_{η∈𝒢} η(x)` with `η(x)` the prefix marginal (`prefixMass`).

**Formalization Note** For the empty class the value is `0` (Lean's `0⁻¹ = 0`); the paper never
forms the mean of an empty class on a reachable state, because the target `µ⋆` is never filtered
out. The conditional `η̄(x′ | x)` of the paper is `mixPrefix 𝒢 x′ / mixPrefix 𝒢 x`. -/
noncomputable def mixPrefix {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (G : Finset (PMF (Fin n → α))) (x : List α) : ℝ :=
  (G.card : ℝ)⁻¹ * ∑ η ∈ G, prefixMass η x

/-- **Consistency** of a density `η` with the oracle at a node `x`, the class filter
`1/R ≤ µ̂(x)/η(x) ≤ R` of Algorithm 2, Lines 3 and 16 (p.11) and of (10) (p.19), stated
multiplicatively: `η(x) ≤ R·µ̂(x)` and `µ̂(x) ≤ R·η(x)` (so `0/0 = 1` and `a/0 = ∞` for `a > 0`,
as in footnote 12, p.18). -/
def Consistent {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (R : ℝ) (μh : List α → NNReal)
    (η : PMF (Fin n → α)) (x : List α) : Prop :=
  prefixMass η x ≤ R * (μh x : ℝ) ∧ (μh x : ℝ) ≤ R * prefixMass η x

/-- The **denominator** `µ̂(u)·η̄(x | u)` of every ratio test of Algorithm 2 (Lines 6, 9, 10, 13,
14, 18, p.11) and of (P1), (P2) (p.19), for the stage start `u` and the class `𝒢`:
`den µ̂ 𝒢 u x = µ̂(u) · (η̄(x)/η̄(u))`.

**Formalization Note** Every ratio test `µ̂(x)/den ≤ M`, `< 1/M`, `> M` is written
multiplicatively (`µ̂(x) ≤ M·den`, `M·µ̂(x) < den`, `M·den < µ̂(x)`), which realizes `a/0 = ∞` for
`a > 0` and `0/0 = 1`. On reachable states `den > 0`. -/
noncomputable def den {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (μh : List α → NNReal)
    (G : Finset (PMF (Fin n → α))) (u x : List α) : ℝ :=
  (μh u : ℝ) * (mixPrefix G x / mixPrefix G u)

/-- A **Bernoulli coin** `Ber(q)` with real parameter, clamped to `[0,1]`.

**Formalization Note** Algorithm 2 (Lines 10, 14, 18) and Algorithm 3 (Line 13) flip coins whose
parameters lie in `[0,1]` on every reachable state (proof of (15), printed p.23; the `min{1,·}` of
Line 13); the clamp `max 0 (min 1 q)` is a no-op there. -/
noncomputable def bern (q : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal (max 0 (min 1 q))
      else ENNReal.ofReal (1 - max 0 (min 1 q))) (by
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add (le_max_left _ _)
      (by have := min_le_left 1 q; have := max_le (zero_le_one' ℝ) (min_le_left 1 q); linarith)]
    simp)

/-- **Next symbol** `y ∼ η̄(· | v)` (Algorithm 2, Line 7, p.11): `some y` with probability
proportional to `η̄(v∘y)`, which equals `η̄(v∘y)/η̄(v) = η̄(y | v)` because the children's masses
sum to the parent's. If every child has mean mass `0` (unreachable when `µ⋆` lies in the class,
since the walk only visits nodes of positive mean mass) the result is `none`, and the trial ends
with nothing added. -/
noncomputable def nextSym {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (G : Finset (PMF (Fin n → α))) (v : List α) : PMF (Option α) :=
  if h : (∑ y : α, ENNReal.ofReal (mixPrefix G (v ++ [y]))) ≠ 0 then
    (PMF.normalize (fun y : α => ENNReal.ofReal (mixPrefix G (v ++ [y])))
        (by rwa [tsum_fintype])
        (by rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))).map
      some
  else PMF.pure none

end TTTSampling


