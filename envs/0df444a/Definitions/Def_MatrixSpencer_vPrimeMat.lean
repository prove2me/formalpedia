-- Prove2me | Definitions.Def_MatrixSpencer_vPrimeMat
-- name    : MatrixSpencer_vPrimeMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:03.001582+00:00
-- url     : https://prove2.me/theorems/6bdc4529-1602-4d5f-806c-6c24324544ca
-- title:
--   The matrix function $v^\prime(X)$
-- statement:
--   For $v'(x)=\dfrac{2\beta x+2(\alpha-\beta)x^{2p-1}}{1-x^2}$, the matrix function
--   $$v'(X)=(I-X^2)^{-1}\bigl(2\beta X+2(\alpha-\beta)X^{2p-1}\bigr).$$
--
--   **Formalization Note** The paper writes $q$ for $p$ at this point. The matrix is only ever multiplied by the weight, which vanishes outside the unit ball.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 2.5, Step 3, p.10

import Mathlib

namespace MatrixSpencer

/-- **The matrix function `v′(X)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Step 3 of the proof of Theorem 2.5, p.10: "v′(x) = (2βx + 2(α−β)x^{2q−1}) / (1−x²)".

`v′(X) = (I − X²)⁻¹ (2βX + 2(α−β)X^{2p−1})`, the rational function above applied to `X`.

**Formalization Note.** The page writes `q` for `p` here. For `X` symmetric with `‖X‖ < 1`, this
is the functional calculus of `v′`. It is only ever multiplied by `weight`, which vanishes outside
the ball. -/
noncomputable def vPrimeMat {d : ℕ} (α β : ℝ) (p : ℕ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 - X ^ 2)⁻¹ * ((2 * β) • X + (2 * (α - β)) • X ^ (2 * p - 1))

end MatrixSpencer


