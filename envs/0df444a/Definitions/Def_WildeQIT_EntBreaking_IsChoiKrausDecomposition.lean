-- Prove2me | Definitions.Def_WildeQIT_EntBreaking_IsChoiKrausDecomposition
-- name    : WildeQIT_EntBreaking_IsChoiKrausDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:07.65386+00:00
-- url     : https://prove2.me/theorems/dc7f3fa8-e62f-4c23-b621-6b22c8b0a772
-- title:
--   Choi–Kraus decomposition $\mathcal N(X)=\sum_l V_lXV_l^\dagger$, $\sum_l V_l^\dagger V_l=I$
-- statement:
--   Let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a linear map and let $\{V_l\}_{l\in\iota}$ be a finite family of operators $V_l\in\mathcal L(\mathcal H_A,\mathcal H_B)$. The family is a **Choi–Kraus decomposition** of $\mathcal N$, and the $V_l$ are its **Kraus operators**, when
--
--   $$
--   \mathcal N(X_A)=\sum_{l}V_lX_AV_l^\dagger\quad\text{for all }X_A\in\mathcal L(\mathcal H_A),\qquad \sum_l V_l^\dagger V_l=I_A .
--   $$
--
--   These are equations (4.188) and (4.189) of Theorem 4.4.1. The Choi–Kraus theorem says that the quantum channels are exactly the maps with such a decomposition, and Theorem 4.6.1 characterizes entanglement-breaking channels by the rank of their Kraus operators.
--
--   **Formalization Note** Operators $\mathcal H_A\to\mathcal H_B$ are $b\times a$ complex matrices and $V^\dagger$ is the conjugate transpose. The index set is any finite type; the book's $\{0,\dots,d-1\}$ is `Fin d`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 4.4.1, eqs. (4.188)–(4.189), p. 151

import Mathlib

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.4.1, Theorem 4.4.1,
equations (4.188)–(4.189), p. 151.
-/

namespace WildeQIT.EntBreaking

open scoped Matrix

/-- **Choi–Kraus decomposition**, Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 4.4.1, (4.188)–(4.189), p. 151. A finite family
`V : ι → Matrix b a ℂ` of operators `V_l ∈ L(ℋ_A, ℋ_B)` is a Choi–Kraus decomposition of the
linear map `N : L(ℋ_A) → L(ℋ_B)` when

1. `N(X) = ∑_l V_l X V_l†` for every `X ∈ L(ℋ_A)` (4.188), and
2. `∑_l V_l† V_l = I_A` (4.189).

The operators `V_l` are the **Kraus operators** of `N` (the book uses "Kraus representation" and
"Kraus operators" for such a family, e.g. Theorem 4.6.1, p. 167).

**Formalization Note.** Operators `ℋ_A → ℋ_B` are `b × a` complex matrices; `V†` is the conjugate
transpose `Vᴴ`. The index set is any finite type `ι`; the book's indices `0, …, d−1` are `ι = Fin d`. -/
def IsChoiKrausDecomposition {a b ι : Type} [Fintype a] [Fintype b] [Fintype ι] [DecidableEq a]
    (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) (V : ι → Matrix b a ℂ) : Prop :=
  (∀ X : Matrix a a ℂ, N X = ∑ l, V l * X * (V l)ᴴ) ∧ ∑ l, (V l)ᴴ * V l = 1

end WildeQIT.EntBreaking


