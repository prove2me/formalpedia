-- Prove2me | Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
-- name    : OnlineSaddlePoint_IsLipschitzPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:17.881527+00:00
-- url     : https://prove2.me/theorems/9b61b2a0-3e3d-4763-9a90-41f534ecdc8b
-- title:
--   $G$-Lipschitz payoff on $X\times Y$
-- statement:
--   Let $G\ge0$. A function $\mathcal L : X\times Y\to\mathbb R$ is **$G$-Lipschitz** if for all $x_1,x_2\in X$ and $y_1,y_2\in Y$
--
--   $$
--   |\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G\big(\|x_1-x_2\|+\|y_1-y_2\|\big).
--   $$
--
--   The constant $G$ bounds how much one round's payoff can change when the players move, and appears in every regret bound of the paper.
--
--   **Formalization Note** The paper writes $G\|[x_1;y_1]-[x_2;y_2]\|$ for a norm on the stacked vector. Every norm with $\|[a;b]\|\le\|a\|+\|b\|$ (all $\ell_p$ norms) makes the paper's condition imply this one, and this is the form its proofs use. It is not Lipschitz continuity on $E\times F$ with the max norm, which would be a stronger assumption.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, §3, p.5

import Mathlib

namespace OnlineSaddlePoint

/-- **`G`-Lipschitz payoff.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, §3, p.5: "We say a
function `𝓛(x, y)` is `G`-Lipschitz continuous with respect to norm `‖·‖`, if
`|𝓛(x₁, y₁) − 𝓛(x₂, y₂)| ≤ G‖[x₁; y₁] − [x₂; y₂]‖`."

**Formalization Note.** The bound is stated as `|f x₁ y₁ − f x₂ y₂| ≤ G (‖x₁ − x₂‖ + ‖y₁ − y₂‖)` for
`x₁, x₂ ∈ X`, `y₁, y₂ ∈ Y`, which is the form the paper's proofs use (pp.7, 9, 10). It is implied by
the paper's `G‖[x₁; y₁] − [x₂; y₂]‖` for every norm on the stacked vector with
`‖[a; b]‖ ≤ ‖a‖ + ‖b‖` (all `ℓ_p` norms), so it is a weaker hypothesis. It is *not* Mathlib's
`LipschitzOnWith` on `E × F`, which uses the max norm and would be a stronger hypothesis than the
paper's `ℓ₂` case. The constant is required to be nonnegative, as a Lipschitz constant is. -/
def IsLipschitzPayoff {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (X : Set E) (Y : Set F) (G : ℝ) (f : E → F → ℝ) : Prop :=
  0 ≤ G ∧ ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ y₁ ∈ Y, ∀ y₂ ∈ Y,
    |f x₁ y₁ - f x₂ y₂| ≤ G * (‖x₁ - x₂‖ + ‖y₁ - y₂‖)

end OnlineSaddlePoint


