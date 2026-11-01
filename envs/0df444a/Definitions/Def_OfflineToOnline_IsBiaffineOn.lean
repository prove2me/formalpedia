-- Prove2me | Definitions.Def_OfflineToOnline_IsBiaffineOn
-- name    : OfflineToOnline_IsBiaffineOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:59.291831+00:00
-- url     : https://prove2.me/theorems/7d66e803-88f1-4416-a587-743c69e5a105
-- title:
--   Biaffine vector payoff $p:\mathcal X\times\mathcal Y\to\mathbb R^d$
-- statement:
--   In a Blackwell sequential game $(\mathcal X,\mathcal Y,\boldsymbol p)$ the players' actions are vectors $x\in\mathcal X\subseteq\mathbb R^m$ and $y\in\mathcal Y\subseteq\mathbb R^k$, and the vector payoff is $\boldsymbol p(x,y)\in\mathbb R^d$. The payoff is **biaffine** on $\mathcal X\times\mathcal Y$ if $\boldsymbol p(x,\cdot)$ is affine on $\mathcal Y$ for every $x\in\mathcal X$ and $\boldsymbol p(\cdot,y)$ is affine on $\mathcal X$ for every $y\in\mathcal Y$:
--
--   $$
--   \boldsymbol p(a x+(1-a)x',y)=a\,\boldsymbol p(x,y)+(1-a)\,\boldsymbol p(x',y),\qquad \boldsymbol p(x,a y+(1-a)y')=a\,\boldsymbol p(x,y)+(1-a)\,\boldsymbol p(x,y')
--   $$
--
--   for all $x,x'\in\mathcal X$, $y,y'\in\mathcal Y$ and $a\in[0,1]$.
--
--   Biaffinity is the structural assumption on the payoff of every Blackwell game in the paper; it is what lets an average of payoffs be written as the payoff of averaged actions.
--
--   **Formalization Note** "Affine on a convex set" is stated as preservation of two-point convex combinations of points of the set. Vectors are functions `Fin n → ℝ`.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, §2.3, p.11

import Mathlib

namespace OfflineToOnline

/-- Biaffine vector payoff (p.11): `p : X × Y → ℝ^d` is biaffine if for any `x ∈ X`, `p(x, ·)` is
affine on `Y`, and for any `y ∈ Y`, `p(·, y)` is affine on `X`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, §2.3, p.11 ("Function p(·,·) is biaffine if …").

Formalization Note: actions are vectors in `Fin m → ℝ` and `Fin k → ℝ`, payoffs in `Fin d → ℝ`.
"Affine on a convex set" is read as preservation of two-point convex combinations of points of
that set. -/
def IsBiaffineOn {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
    (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) : Prop :=
  (∀ y ∈ Y, ∀ x ∈ X, ∀ x' ∈ X, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      p (a • x + (1 - a) • x') y = a • p x y + (1 - a) • p x' y) ∧
  (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      p x (a • y + (1 - a) • y') = a • p x y + (1 - a) • p x y')

end OfflineToOnline


