-- Prove2me | Definitions.Def_BartlettNN_Margin_Squash
-- name    : BartlettNN_Margin_Squash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:27:33.930242+00:00
-- url     : https://prove2.me/theorems/b038e8dd-3056-42d8-843c-5e5573ed9686
-- title:
--   Squashing π_γ, the squashed class π_γ(H), and the quantization Q_α
-- statement:
--   For $\gamma>0$ the piecewise-linear **squashing function** $\pi_\gamma:\mathbb R\to\mathbb R$ is
--   $$
--   \pi_\gamma(\alpha)=\begin{cases}\gamma, & \alpha\ge\gamma,\\ -\gamma, & \alpha\le-\gamma,\\ \alpha, & \text{otherwise},\end{cases}
--   $$
--   and for a class $H$ of real functions on $X$, $\pi_\gamma(H)=\{\pi_\gamma\circ h : h\in H\}$. For $\alpha>0$ the **quantization function** $Q_\alpha:\mathbb R\to\mathbb R$ is
--   $$
--   Q_\alpha(x)=\Bigl\lceil \frac{x-\alpha/2}{\alpha}\Bigr\rceil\,\alpha ,
--   $$
--   which rounds $x$ to a multiple of $\alpha$ with $x-\alpha/2\le Q_\alpha(x)<x+\alpha/2$.
--
--   Squashing and quantization reduce a real-valued class to a finite-valued one, to which a combinatorial covering bound applies.
--
--   **Formalization Note** $\pi_\gamma(\alpha)$ is written `max (-γ) (min γ α)`, equal to the three-case formula for $\gamma\ge 0$. $\lceil\cdot\rceil$ is `Int.ceil`. Every theorem using these assumes $\gamma>0$.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 527 (π_γ, π_γ(H)) and p. 528, proof of Theorem 2 (Q_α)

import Mathlib

namespace BartlettNN.Margin

/-- The squashing function `π_γ(α) = γ` if `α ≥ γ`, `−γ` if `α ≤ −γ`, and `α` otherwise
(p. 527). For `γ ≥ 0` this equals `max (−γ) (min γ α)`. -/
noncomputable def squash (γ α : ℝ) : ℝ := max (-γ) (min γ α)

/-- The squashed class `π_γ(H) = {π_γ ∘ h : h ∈ H}` (p. 527). -/
def squashClass {X : Type*} (γ : ℝ) (H : Set (X → ℝ)) : Set (X → ℝ) :=
  (fun h => squash γ ∘ h) '' H

/-- The quantization function `Q_α(x) = ⌈(x − α/2)/α⌉ α` (proof of Theorem 2, p. 528). -/
noncomputable def quantize (α x : ℝ) : ℝ := (⌈(x - α / 2) / α⌉ : ℝ) * α

end BartlettNN.Margin


