-- Prove2me | Definitions.Def_HypercliqueFalse_secondMain
-- name    : HypercliqueFalse_secondMain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:55.934238+00:00
-- url     : https://prove2.me/theorems/3390a749-5ce0-45b9-b949-cd94d08086ad
-- title:
--   Lemma 4.1, second reduction: the main children, of size $(N, M/q, a, qb, c)$
-- statement:
--   Let $A, B, C, D, E$ be arrays of size $(N, M, a, b, c)$ with $M = M' q$. The second reduction splits $x_1 = q y_1 + i$ and $x_4 = q y_4 + j$; write $A^{i}$, $B^{ij}$, $C^{ij}$, $D^{j}$, $E^{ij}_\ell$ for the arrays at these digits. For $g \in [q]$ the **$g$-th main child** has size $(N, M', a, qb, c)$ and is
--   $$
--   \bar A^g = A^g,\quad \bar B^g[\kappa,(i,\beta)] = B^{gi}[\kappa,\beta],\quad \bar C^g[(i,\beta),\gamma] = C^{ig}[\beta,\gamma],\quad \bar D^g = D^g,\quad \bar E^g_\ell[\alpha,(i,\beta),\gamma] = E^{ig}_\ell[\alpha,\beta,\gamma].
--   $$
--   The remaining digit, which appears in $B$, $C$ and all $E_\ell$, moves into the dimension $b$, i.e. into the index $\beta$.
--
--   The paper describes this reduction in words only ("The second reduction is analogous: we split $x_1$ and $x_4$ instead … we move it into the dimension $b$"); these are the arrays that description determines, obtained from Lemma 3.1 with $V_{ij} = A^iB^{ij}$ and $U_{ij}[\beta,\alpha] = \sum_\gamma C^{ij}[\beta,\gamma]D^{j}[\gamma,\alpha]\prod_\ell E^{ij}_\ell[\alpha,\beta,\gamma]$.
--
--   **Formalization Note** Digit split and $[q]\times[b]\cong[qb]$ by `finProdFinEquiv`, 0-based.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 4.1, p.11

import Mathlib
import Definitions.Def_HypercliqueFalse_TData

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.1, second reduction: the `g`-th main child, of size `(N, M/q, a, qb, c)`.** Fischer,
*The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof
of Lemma 4.1, p.11: "The second reduction is analogous: we split x₁ and x₄ instead, which are shared
by B, C, and all E_ℓ. In the main terms, the remaining digit then appears in B, C, and all E_ℓ, and
we move it into the dimension b, that is, into the index β."

Split `x₁ = q·y₁ + i` and `x₄ = q·y₄ + j`, and write `A^i`, `B^{ij}`, `C^{ij}`, `D^j`, `E^{ij}` for the
arrays at these digits. With `V_{ij} = A^i B^{ij}` and `U_{ij}[β, α] = Σ_γ C^{ij}[β, γ] D^j[γ, α]
Π_ℓ E^{ij}_ℓ[α, β, γ]` the `(i, j)` term is `tr(V_{ij} U_{ij})`, and Lemma 3.1 gives the `g`-th main
term `Σ_i tr(V_{gi} U_{ig})`, which is `T_h` of
`Ā^g = A^g`, `B̄^g[κ, (i, β)] = B^{gi}[κ, β]`, `C̄^g[(i, β), γ] = C^{ig}[β, γ]`, `D̄^g = D^g`,
`Ē^g_ℓ[α, (i, β), γ] = E^{ig}_ℓ[α, β, γ]`.

**Formalization Note.** The paper gives no formulas for this reduction; these are the formulas its
description determines. `M = M' · q`; digit split and `[q] × [b] ≅ [qb]` by `finProdFinEquiv`. -/
def secondMain {h N M' q a b c n : ℕ} (T : TData h N (M' * q) a b c n) (g : Fin q) :
    TData h N M' a (q * b) c n where
  A y₁ x₂ x₃ r := T.A (finProdFinEquiv (y₁, g)) x₂ x₃ r
  B y₁ x₂ y₄ r := Matrix.of fun κ p =>
    T.B (finProdFinEquiv (y₁, g)) x₂ (finProdFinEquiv (y₄, (finProdFinEquiv.symm p).1)) r
      κ (finProdFinEquiv.symm p).2
  C y₁ x₃ y₄ r := Matrix.of fun p γ =>
    T.C (finProdFinEquiv (y₁, (finProdFinEquiv.symm p).1)) x₃ (finProdFinEquiv (y₄, g)) r
      (finProdFinEquiv.symm p).2 γ
  D x₂ x₃ y₄ r := T.D x₂ x₃ (finProdFinEquiv (y₄, g)) r
  E ℓ y₁ x₂ x₃ y₄ r α p γ :=
    T.E ℓ (finProdFinEquiv (y₁, (finProdFinEquiv.symm p).1)) x₂ x₃ (finProdFinEquiv (y₄, g)) r
      α (finProdFinEquiv.symm p).2 γ

end HypercliqueFalse


