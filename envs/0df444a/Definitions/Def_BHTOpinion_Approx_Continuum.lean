-- Prove2me | Definitions.Def_BHTOpinion_Approx_Continuum
-- name    : BHTOpinion_Approx_Continuum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:19.810535+00:00
-- url     : https://prove2.me/theorems/95e95ef9-b726-4197-9d2d-f9b7bb92106f
-- title:
--   The embedding G of Section 4: a vector ξ ∈ ℝⁿ as the step function on I = [0, 1] with value ξ_i on [(i−1)/n, i/n) and G(ξ)(1) = ξ_n
-- statement:
--   This file defines the operator $G$ of Section 4 of Blondel, Hendrickx and Tsitsiklis, which embeds discrete opinion vectors into the continuum model. The continuum objects it is used with ($I=[0,1]$, $Y$, $X_m$, $X^M$, the operator $\mathcal L$ of (3.3) and solutions of (3.2)) come from the shared definition `BHTOpinion.Continuum.Model`.
--
--   For $n\ge1$ and $\xi\in\mathbb R^n$, $G(\xi)$ is the step function on $I$ given by
--
--   $$G(\xi)(\alpha)=\xi_i\quad\text{for }\alpha\in\Bigl[\frac{i-1}{n},\frac in\Bigr),\ i=1,\dots,n,\qquad G(\xi)(1)=\xi_n .$$
--
--   It places the $n$ agents of the discrete model on $n$ consecutive blocks of $I$, each of length $1/n$. It is the link between the two models in the embedding claim and in Theorem 7.
--
--   **Formalization Note** With 0-based indices, $G(\xi)(\alpha)=\xi_{\min(\lfloor n\alpha\rfloor,\,n-1)}$ for $\alpha\in I$. For $n=0$ the Lean function returns the junk value $0$, and every statement that uses $G$ assumes $n\ge1$. The page says the vectors are "always sorted". $G$ is defined for every vector, and sortedness is a hypothesis only where the paper's theorem has it.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), p. 5231 (the operator G)

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

namespace BHTOpinion.Approx

/-- The operator `G` of Section 4 (p. 5231) mapping a vector `ξ ∈ ℝⁿ` to the step function
`G(ξ)(α) = ξ_i` for `α ∈ [(i−1)/n, i/n)` (`i = 1, …, n`, 1-based as on the page) and
`G(ξ)(1) = ξ_n`. With 0-based `Fin n` this is `ξ ⟨min ⌊n α⌋₊ (n − 1), _⟩` for `α ∈ [0, 1]`.
For `n = 0` there is no coordinate and `G` returns the junk value `0`; every statement using `G`
assumes `0 < n`. -/
noncomputable def G {n : ℕ} (ξ : Fin n → ℝ) (α : ℝ) : ℝ :=
  if h : 0 < n then
    ξ ⟨min ⌊(n : ℝ) * α⌋₊ (n - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt h one_pos)⟩
  else 0

end BHTOpinion.Approx


