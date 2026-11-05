-- Prove2me | Definitions.Def_DHRUniq_IsSchmidtDecomp
-- name    : DHRUniq_IsSchmidtDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:27.441563+00:00
-- url     : https://prove2.me/theorems/7eeca957-e52b-414a-a2df-6cdbb0d90208
-- title:
--   Schmidt decomposition $|\psi\rangle=\sum_i\sqrt{p_i}\,|e_i\rangle\otimes|f_i\rangle$
-- statement:
--   Let $\psi$ be a vector of $\mathbb C^a\otimes\mathbb C^b$. Numbers $p_i\ge0$ and orthonormal families $(e_i)$ of $\mathbb C^a$ and $(f_i)$ of $\mathbb C^b$, with the same index set, form a **Schmidt decomposition** of $\psi$ if
--
--   $$
--   |\psi\rangle=\sum_i\sqrt{p_i}\,|e_i\rangle\otimes|f_i\rangle.
--   $$
--
--   The $p_i$ are the squared amplitudes, which are the eigenvalues of the reduced density operator.
--
--   **Formalization Note** The families need not span the factors and zero coefficients are allowed.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Lemma 2, p. 3; Theorem 7, p. 6; §8, p. 18

import Mathlib
import Definitions.Def_DHRUniq_IsOrthonormalFamily

namespace DHRUniq

/-- **Schmidt decomposition** `|ψ⟩ = ∑_i √p_i |e_i⟩ ⊗ |f_i⟩` (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Lemma 2, p. 3, and the
Schmidt decompositions of Theorem 7, p. 6, and of `|ψ^{⊗n}⟩`, §8, p. 18): nonnegative numbers
`p_i` and orthonormal families `(e_i)`, `(f_i)` in the two factors.

**Formalization Note** The `p_i` are the squared amplitudes, as in the paper. `0 ≤ p i` is part
of the predicate, so `Real.sqrt` is never applied to a negative number. The families need not
span the factors; zero coefficients are allowed. -/
def IsSchmidtDecomp {ι a b : Type} [Fintype ι] [DecidableEq ι] [Fintype a] [Fintype b]
    (ψ : a × b → ℂ) (p : ι → ℝ) (e : ι → a → ℂ) (f : ι → b → ℂ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ IsOrthonormalFamily e ∧ IsOrthonormalFamily f ∧
    ∀ x y, ψ (x, y) = ∑ i, (Real.sqrt (p i) : ℂ) * e i x * f i y

end DHRUniq


