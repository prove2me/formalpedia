-- Prove2me | Definitions.Def_HypercliqueFalse_tPoly
-- name    : HypercliqueFalse_tPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:46.599204+00:00
-- url     : https://prove2.me/theorems/b47b922e-aea2-4ead-8062-6f3dc4455053
-- title:
--   The auxiliary hyperclique polynomial $T_h(A,B,C,D,E)$
-- statement:
--   For arrays $A, B, C, D, E$ of size $(N, M, a, b, c)$ (see `TData`), the **auxiliary hyperclique polynomial** is
--   $$
--   T_h(A,B,C,D,E) = \sum_{x} \ \sum_{\alpha\in[a],\,\beta\in[b],\,\gamma\in[c]} (A_{\hat x_4}B_{\hat x_3})[\alpha,\beta]\cdot C_{\hat x_2}[\beta,\gamma]\cdot D_{\hat x_1}[\gamma,\alpha]\cdot \prod_{\ell=5}^{h+1} E_{\ell;\hat x_\ell}[\alpha,\beta,\gamma],
--   $$
--   where $x$ ranges over $x_1, x_4 \in [M]$, $x_2, x_3 \in [N]$ and $x_5,\dots,x_{h+1}\in[n]$.
--
--   For $N = M = n$ and $a = b = c = 1$ it is $H_h = H_{h+1,h}$; the recursive algorithm of Section 4 rewrites $T_h$ as sums of instances with smaller $N, M$ and larger $a, b, c$.
--
--   **Formalization Note** The array $E_{\ell}$ is evaluated at the tuple $(x_5,\dots,x_{h+1})$ with the entry $x_\ell$ removed (entry $j$ is $x_{j+5}$ for $j < \ell - 5$ and $x_{j+6}$ otherwise, 0-based).
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 4, p.10

import Mathlib
import Definitions.Def_HypercliqueFalse_TData

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The auxiliary hyperclique polynomial `T_h`.** Fischer, *The Hyperclique Hypothesis is False*,
arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 4, p.10:
"T_h(A, B, C, D, E) = Σ_x Σ_{α∈[a], β∈[b], γ∈[c]} (A_{x̂₄}B_{x̂₃})[α, β] · C_{x̂₂}[β, γ] · D_{x̂₁}[γ, α] ·
Π_{ℓ=5}^{h+1} E_{ℓ;x̂_ℓ}[α, β, γ]."

The outer sum ranges over `x₁, x₄ ∈ [M]`, `x₂, x₃ ∈ [N]` and `x₅, …, x_{h+1} ∈ [n]`.

**Formalization Note.** `E ℓ` is evaluated at the tuple `r` with entry `ℓ` removed: entry `j` of
that tuple is `r j` for `j < ℓ` and `r (j + 1)` for `j ≥ ℓ`, i.e. `x̂_{ℓ+5}` restricted to
`x₅, …, x_{h+1}`. -/
def tPoly {h N M a b c n : ℕ} (T : TData h N M a b c n) : ℤ :=
  ∑ x₁ : Fin M, ∑ x₂ : Fin N, ∑ x₃ : Fin N, ∑ x₄ : Fin M, ∑ r : Fin (h - 3) → Fin n,
    ∑ α : Fin a, ∑ β : Fin b, ∑ γ : Fin c,
      (T.A x₁ x₂ x₃ r * T.B x₁ x₂ x₄ r) α β * T.C x₁ x₃ x₄ r β γ * T.D x₂ x₃ x₄ r γ α *
        ∏ ℓ : Fin (h - 3), T.E ℓ x₁ x₂ x₃ x₄
          (fun j => r ⟨if (j : ℕ) < ℓ then j else j + 1, by
            have := j.isLt; have := ℓ.isLt; split <;> omega⟩) α β γ

end HypercliqueFalse


