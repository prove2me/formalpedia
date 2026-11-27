-- Prove2me | Definitions.Def_BeliefDominance_Supplement_StronglyConsistent
-- name    : BeliefDominance_Supplement_StronglyConsistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:29:45.124658+00:00
-- url     : https://prove2.me/theorems/997e63ed-87be-4729-9341-9c7abadaf251
-- title:
--   Strong consistency of a two-period preference ordering
-- statement:
--   Let $X$ be the strategy set of a two-period decision space: a strategy $x=(x_1,x_2(Y))$ is a first-period action $x_1\in X_1$ together with a second-period action $x_2(y)\in X_{2,x_1,y}$ for every signal $y$. Let $\preceq$ be a preference relation on strategies and, for each $x_1$ and $y$, let $\preceq_{x_1,y}$ be a preference relation on second-period actions. Write $\prec$, $\prec_{x_1,y}$ for the strict parts ($a\prec b$ means $a\preceq b$ and not $b\preceq a$) and $\sim$, $\sim_{x_1,y}$ for the symmetric parts ($a\sim b$ means $a\preceq b$ and $b\preceq a$).
--
--   The pair $(\preceq,\preceq_{\cdot,\cdot})$ is **strongly consistent** if, for all $x,\tilde x\in X$, every signal $y$ and every $\hat x_2\in X_{2,\tilde x_1,y}$, the modified strategy $\hat x=(\tilde x_1,\hat x_2,\tilde x_2(Y\neq y))$, which follows $\tilde x$ except that it plays $\hat x_2$ after $y$, satisfies:
--
--   1. if $\tilde x\not\prec x$ and $\hat x_2\not\prec_{\tilde x_1,y}\tilde x_2(y)$, then $\hat x\not\prec x$;
--   2. if $\tilde x\succeq x$ and $\hat x_2\succ_{\tilde x_1,y}\tilde x_2(y)$, then $\hat x\succ x$;
--   3. if $\tilde x\sim x$ and $\hat x_2\sim_{\tilde x_1,y}\tilde x_2(y)$, then $\hat x\sim x$.
--
--   The comparison strategy $x$ is any strategy of $X$, possibly with a different first-period action from $\tilde x$. This is what lets strong consistency speak about strategies with differing first-period actions and rule out fallible inconsistency; for incomplete orderings, $\tilde x\not\prec x$ is weaker than $\tilde x\succeq x$.
--
--   **Formalization Note** `le x x'` means $x\preceq x'$ and `le₂ x₁ y a b` means $a\preceq_{x_1,y}b$; strict parts are the published `strictPart`. The modified strategy is quantified as any strategy $\hat x\in X$ with $\hat x_1=\tilde x_1$ that agrees with $\tilde x$ at every signal other than $y$; its action at $y$ is $\hat x_2$. This is equivalent to the printed quantification over $\hat x_2\in X_{2,\tilde x_1,y}$. The printed domain "$X_{\tilde x_1,y}$" omits the period subscript; it is the second-period action set $X_{2,\tilde x_1,y}$ of p. 4, as in the proof of Theorem 4 (p. 11). No order axiom is part of the definition.
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, doi:10.1287/mnsc.2020.3908, §3.3, definition 2 (strong consistency), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace

namespace BeliefDominance.Supplement

/-- Strong consistency (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic Consistency*,
Management Science, doi:10.1287/mnsc.2020.3908, §3.3, definition 2, p.6 (PDF p.7)): given
`x, x̃ ∈ X`, `y ∈ 𝒴` and `x̂₂ ∈ X_{2,x̃₁,y}`, with `x̂ = (x̃₁, x̂₂, x̃₂(Y ≠ y))`,
(a) if `x̃ ⊀ x` and `x̂₂ ⊀_{x̃₁,y} x̃₂(y)`, then `x̂ ⊀ x`;
(b) if `x̃ ≽ x` and `x̂₂ ≻_{x̃₁,y} x̃₂(y)`, then `x̂ ≻ x`;
(c) if `x̃ ~ x` and `x̂₂ ~_{x̃₁,y} x̃₂(y)`, then `x̂ ~ x`.

**Formalization Note** `le x x'` means `x ≼ x'` and `le₂ x₁ y a b` means `a ≼_{x₁,y} b`; the strict
relations are `strictPart`, and `~` is the symmetric part (`≼` both ways), in both periods. The
modified strategy `x̂` is quantified as any strategy of `X` whose first-period action is `x̃₁` and
which agrees with `x̃` off the signal `y`; its action at `y` is `x̂₂ = x̂.2 y`. Since `x̂ ∈ X`
forces `x̂₂ ∈ X_{2,x̃₁,y}`, and every `x̂₂ ∈ X_{2,x̃₁,y}` gives such a strategy, this is the
printed quantification (whose domain `X_{x̃₁,y}` is the action set `X_{2,x̃₁,y}` of p.4). The
strategy `x` ranges over all of `X` and may have a different first-period action from `x̃`. No
order axiom is part of the definition. -/
def StronglyConsistent {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop) : Prop :=
  ∀ x ∈ D.strategies, ∀ xt ∈ D.strategies, ∀ y : Y, ∀ xh ∈ D.strategies,
    xh.1 = xt.1 → (∀ y' : Y, y' ≠ y → xh.2 y' = xt.2 y') →
      (¬ strictPart le xt x → ¬ strictPart (le₂ xt.1 y) (xh.2 y) (xt.2 y) →
          ¬ strictPart le xh x) ∧
      (le x xt → strictPart (le₂ xt.1 y) (xt.2 y) (xh.2 y) → strictPart le x xh) ∧
      (le x xt ∧ le xt x → le₂ xt.1 y (xh.2 y) (xt.2 y) ∧ le₂ xt.1 y (xt.2 y) (xh.2 y) →
          le x xh ∧ le xh x)

end BeliefDominance.Supplement


