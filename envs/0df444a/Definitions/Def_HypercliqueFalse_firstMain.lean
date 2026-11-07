-- Prove2me | Definitions.Def_HypercliqueFalse_firstMain
-- name    : HypercliqueFalse_firstMain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:58.947835+00:00
-- url     : https://prove2.me/theorems/51b8b0f2-a4fa-48e3-b376-ce2a50a0a23c
-- title:
--   Lemma 4.1, first reduction: the main children $(\bar A^g,\bar B^g,\bar C^g,\bar D^g,\bar E^g)$
-- statement:
--   Let $A, B, C, D, E$ be arrays of size $(N, M, a, b, c)$ with $N = N' q$. Split $x_2 = q\,y_2 + i$ and $x_3 = q\,y_3 + j$ into their last base-$q$ digit and the remaining digits, and write $A^{ij}$, $B^{i}$, $C^{j}$, $D^{ij}$, $E^{ij}_\ell$ for the arrays at these digits (so $A^{ij}_{x_1y_2y_3} = A_{x_1,\,qy_2+i,\,qy_3+j}$, and so on). For $g \in [q]$ the **$g$-th main child** has size $(N', M, qa, b, c)$ and is
--   $$
--   \bar A^g[(j,\alpha),\kappa] = A^{gj}[\alpha,\kappa],\quad \bar B^g = B^g,\quad \bar C^g = C^g,\quad \bar D^g[\gamma,(j,\alpha)] = D^{jg}[\gamma,\alpha],\quad \bar E^g_\ell[(j,\alpha),\beta,\gamma] = E^{jg}_\ell[\alpha,\beta,\gamma],
--   $$
--   that is, $\bar A^g$ stacks $A^{g1},\dots,A^{gq}$ and $\bar D^g$ places $D^{1g},\dots,D^{qg}$ side by side.
--
--   These are the main terms of the proof of Lemma 4.1 (and of Lemma 3.2 for $h = 3$).
--
--   **Formalization Note** 0-based digits: $x_2 = q y_2 + i$ is `finProdFinEquiv (y₂, i)`; $[q]\times[a]$ is identified with $[qa]$ by `finProdFinEquiv`, $(j,\alpha) \mapsto a j + \alpha$, as in the paper's "we identify $[q]\times[a]$ with $[qa]$".
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 4.1, pp.10–11; proof of Lemma 3.2, pp.6–7

import Mathlib
import Definitions.Def_HypercliqueFalse_TData

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.1, first reduction: the `g`-th main child `(Ā^g, B̄^g, C̄^g, D̄^g, Ē^g)`, of size
`(N/q, M, qa, b, c)`.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held
version, sha256 6bd5cf5d…7730), proof of Lemma 4.1, pp.10–11, with the block matrices of the proof
of Lemma 3.2, pp.6–7.

Split `x₂ = q·y₂ + i` and `x₃ = q·y₃ + j` (last base-`q` digit `i`, resp. `j`). Writing `A^{ij}`,
`B^i`, `C^j`, `D^{ij}`, `E^{ij}` for the arrays at these digits, the `g`-th main child is
`Ā^g[(j, α), κ] = A^{gj}[α, κ]`, `B̄^g = B^g`, `C̄^g = C^g`, `D̄^g[γ, (j, α)] = D^{jg}[γ, α]` and
`Ē^g_ℓ[(j, α), β, γ] = E^{jg}_ℓ[α, β, γ]` ("Ā^g = [A^{g1}; …; A^{gq}]", "D̄^g = [D^{1g} ⋯ D^{qg}]",
"Ē^g_ℓ[(j, α), β, γ] = E^{jg}_ℓ[α, β, γ], where we identify [q] × [a] with [qa]").

**Formalization Note.** `N = N' · q`; the digit split is `finProdFinEquiv (y, i) = q·y + i`, and
`[q] × [a]` is identified with `[qa]` by `finProdFinEquiv` (`(j, α) ↦ a·j + α`). 0-based. -/
def firstMain {h N' q M a b c n : ℕ} (T : TData h (N' * q) M a b c n) (g : Fin q) :
    TData h N' M (q * a) b c n where
  A x₁ y₂ y₃ r := Matrix.of fun p κ =>
    T.A x₁ (finProdFinEquiv (y₂, g)) (finProdFinEquiv (y₃, (finProdFinEquiv.symm p).1)) r
      (finProdFinEquiv.symm p).2 κ
  B x₁ y₂ x₄ r := T.B x₁ (finProdFinEquiv (y₂, g)) x₄ r
  C x₁ y₃ x₄ r := T.C x₁ (finProdFinEquiv (y₃, g)) x₄ r
  D y₂ y₃ x₄ r := Matrix.of fun γ p =>
    T.D (finProdFinEquiv (y₂, (finProdFinEquiv.symm p).1)) (finProdFinEquiv (y₃, g)) x₄ r
      γ (finProdFinEquiv.symm p).2
  E ℓ x₁ y₂ y₃ x₄ r p β γ :=
    T.E ℓ x₁ (finProdFinEquiv (y₂, (finProdFinEquiv.symm p).1)) (finProdFinEquiv (y₃, g)) x₄ r
      (finProdFinEquiv.symm p).2 β γ

end HypercliqueFalse


