-- Prove2me | Definitions.Def_WassChanceCvx_IsAlphaConcaveOn
-- name    : WassChanceCvx_IsAlphaConcaveOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:18.172691+00:00
-- url     : https://prove2.me/theorems/57d30cf8-cbb2-4cda-9c7b-c5ef96a432b9
-- title:
--   α-concave function on a set (Definition 1)
-- statement:
--   Let $V$ be a real vector space (in the paper $V=\mathbb R^n$), $D\subseteq V$ and $\alpha\in[-\infty,+\infty]$. A function $f:V\to\mathbb R$ is **α-concave on $D$** if $f\ge0$ on $D$ and, for all $x,y\in D$ and $\theta\in[0,1]$,
--
--   $$
--   f(\theta x+(1-\theta)y)\ \ge\ m_\alpha\bigl(f(x),f(y);\theta\bigr).
--   $$
--
--   For $\alpha=0$ this is log-concavity and for $\alpha=-\infty$ quasi-concavity. The notion is used for the probability function $x\mapsto\mathbb P[A\xi\le b(x)]$ (Proposition 3) and for shifted functions (Lemma 8).
--
--   **Formalization Note** The domain $\mathrm{dom}\,f$ of Definition 1 is the set $D$; values of $f$ off $D$ are irrelevant. Definition 1 presupposes that $D$ is convex; this is not part of the predicate, and statements assume or conclude the convexity of $D$ separately.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Definition 1, p.5

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean

namespace WassChanceCvx

/-- **α-concave function on a set.**
Shen, Jiang, arXiv:2111.02486v2, Definition 1, p.5: "A nonnegative function `f` defined on a
convex subset of `ℝⁿ` is said to be α-concave with `α ∈ ℝ̄` if for all `x, y ∈ dom f` and
`θ ∈ [0, 1]`, `f(θx + (1 − θ)y) ≥ m_α(f(x), f(y); θ)`."

`IsAlphaConcaveOn α D f` says that `f` is nonnegative on `D` and that
`f(θx + (1 − θ)y) ≥ m_α(f(x), f(y); θ)` for all `x, y ∈ D` and `θ ∈ [0, 1]`.

`m_α(a, b; θ)` is the published generalized mean `KallMayerSLP.GenConcave.genMean α θ a b` (the
same cases as Definition 1: `0` if `ab = 0`, else `a^θ b^(1−θ)`, `max`, `min`, or the power mean;
the weight `θ` on the first argument).

**Formalization Note.** The domain `dom f` is the set `D`; `f` is a total function and its values
off `D` play no role. The convexity of `D`, which Definition 1 presupposes, is not part of the
predicate: statements that use it assume or conclude `Convex ℝ D` separately. The ambient space
is any real vector space `V` (`ℝⁿ` in the paper). -/
def IsAlphaConcaveOn {V : Type*} [AddCommGroup V] [Module ℝ V] (α : EReal) (D : Set V)
    (f : V → ℝ) : Prop :=
  (∀ x ∈ D, 0 ≤ f x) ∧
    ∀ x ∈ D, ∀ y ∈ D, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      KallMayerSLP.GenConcave.genMean α θ (f x) (f y) ≤ f (θ • x + (1 - θ) • y)

end WassChanceCvx


