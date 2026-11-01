-- Prove2me | Definitions.Def_WildeQIT_EntManip_schmidtVec
-- name    : WildeQIT_EntManip_schmidtVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:24.881563+00:00
-- url     : https://prove2.me/theorems/08459eba-b1be-46ae-9dfb-33338283f58e
-- title:
--   Schmidt-form vector $|\psi^p\rangle_{AB}=\sum_x\sqrt{p_X(x)}|x\rangle_A|x\rangle_B$
-- statement:
--   Let $p_X$ be a probability distribution on a finite alphabet $\mathcal X$, and let $\mathcal H_A$ and $\mathcal H_B$ both have orthonormal basis $\{|x\rangle\}_{x\in\mathcal X}$. The vector
--
--   $$
--   |\psi^p\rangle_{AB}\equiv\sum_{x\in\mathcal X}\sqrt{p_X(x)}\,|x\rangle_A|x\rangle_B
--   $$
--
--   has amplitude $\sqrt{p_X(x)}$ at $(x,x)$ and $0$ elsewhere. It is the coherent version of the distribution $p_X$ used in entanglement concentration.
--
--   **Formalization Note** A function on `X × X`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 19.4.2, p. 547

import Mathlib

namespace WildeQIT.EntManip

/-- **Schmidt-form state of a distribution** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Lemma 19.4.2, p. 547): for a probability distribution `p_X` on a finite
alphabet `𝒳`, `|ψ^p⟩_{AB} ≡ ∑_x √(p_X(x)) |x⟩_A |x⟩_B`, with amplitude `√(p_X(x))` at `(x, x)` and
`0` off the diagonal.

**Formalization Note** `H_A` and `H_B` both have orthonormal basis `{|x⟩}_{x ∈ 𝒳}`, so the vector
lives on `𝒳 × 𝒳`. -/
noncomputable def schmidtVec {X : Type} [DecidableEq X] (p : X → ℝ) : X × X → ℂ :=
  fun z => if z.1 = z.2 then ((Real.sqrt (p z.1) : ℝ) : ℂ) else 0

end WildeQIT.EntManip


