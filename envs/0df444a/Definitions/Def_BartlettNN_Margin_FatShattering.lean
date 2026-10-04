-- Prove2me | Definitions.Def_BartlettNN_Margin_FatShattering
-- name    : BartlettNN_Margin_FatShattering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:46:45.953155+00:00
-- url     : https://prove2.me/theorems/ea772800-120a-47ee-aa79-ae12e76b740f
-- title:
--   γ-shattering and the fat-shattering dimension fat_H(γ) (§II)
-- statement:
--   Let $H$ be a class of real-valued functions on a set $X$ and $\gamma>0$. A sequence $(x_1,\dots,x_m)$ of points of $X$ is **$\gamma$-shattered** by $H$ if there is $r=(r_1,\dots,r_m)\in\mathbb R^m$ such that for every $b=(b_1,\dots,b_m)\in\{-1,1\}^m$ some $h\in H$ satisfies
--   $$
--   (h(x_i)-r_i)\,b_i\ \ge\ \gamma\qquad (i=1,\dots,m).
--   $$
--   The **fat-shattering dimension** of $H$ is the function
--   $$
--   \operatorname{fat}_H(\gamma)=\max\{m : H \text{ } \gamma\text{-shatters some } x\in X^m\}.
--   $$
--   This scale-sensitive dimension, introduced by Kearns and Schapire, replaces the VC dimension in the paper's bounds.
--
--   **Formalization Note** The maximum is a supremum in $\mathbb N\cup\{\infty\}$ (`ℕ∞`): it equals $\infty$ when $H$ $\gamma$-shatters sequences of every length, and $0$ when $H$ is empty. Sign vectors are `Bool`-valued and read through `pm` ($+1$ for `true`). The shattering inequality is non-strict, as on the page.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 526, Section II (γ-shattering, fat_H(γ))

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification

namespace BartlettNN.Margin

/-- A sequence `x = (x_1, …, x_m)` of points of `X` is `γ`-shattered by `H` (p. 526) if there is
`r ∈ ℝ^m` such that for every sign vector `b ∈ {−1, 1}^m` some `h ∈ H` has
`(h(x_i) − r_i) b_i ≥ γ` for all `i`. Signs are `Bool`, read through `pm`. -/
def GammaShatters {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) {m : ℕ} (x : Fin m → X) : Prop :=
  ∃ r : Fin m → ℝ, ∀ b : Fin m → Bool, ∃ h ∈ H, ∀ i, γ ≤ (h (x i) - r i) * pm (b i)

/-- The fat-shattering dimension `fat_H(γ) = max{m : H γ-shatters some x ∈ X^m}` (p. 526), valued
in `ℕ∞`: it is `⊤` when `H` `γ`-shatters sequences of every length, and `0` when `H` is empty. -/
noncomputable def fat {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) : ℕ∞ :=
  ⨆ (m : ℕ) (x : Fin m → X) (_ : GammaShatters H γ x), (m : ℕ∞)

end BartlettNN.Margin


