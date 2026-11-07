-- Prove2me | Definitions.Def_HypercliqueFalse_TData
-- name    : HypercliqueFalse_TData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:00.255505+00:00
-- url     : https://prove2.me/theorems/8486d617-dc45-43b2-8835-8fb0245ba325
-- title:
--   The arrays $A, B, C, D, E$ of the auxiliary hyperclique polynomial $T_h$, of size $(N, M, a, b, c)$
-- statement:
--   Fix $h \ge 3$ and dimensions $N, M, a, b, c, n$. The variables are $x_1, x_4 \in [M]$, $x_2, x_3 \in [N]$ and $x_5, \dots, x_{h+1} \in [n]$; $\hat x_i$ denotes the tuple of all variables except $x_i$. The arrays of $T_h$ are matrix-valued or three-dimensional, each omitting exactly one variable:
--
--   1. $A_{\hat x_4} \in \mathbb Z^{a \times c}$, depending on $x_1, x_2, x_3, x_5, \dots$;
--   2. $B_{\hat x_3} \in \mathbb Z^{c \times b}$, depending on $x_1, x_2, x_4, x_5, \dots$;
--   3. $C_{\hat x_2} \in \mathbb Z^{b \times c}$, depending on $x_1, x_3, x_4, x_5, \dots$;
--   4. $D_{\hat x_1} \in \mathbb Z^{c \times a}$, depending on $x_2, x_3, x_4, x_5, \dots$;
--   5. $E_{\ell;\hat x_\ell} \in \mathbb Z^{a \times b \times c}$ for $\ell = 5, \dots, h+1$, depending on $x_1,\dots,x_4$ and all of $x_5,\dots,x_{h+1}$ except $x_\ell$.
--
--   The tuple $(N, M, a, b, c)$ is the **size**. For $h = 3$ there are no arrays $E$.
--
--   **Formalization Note** `A x₁ x₂ x₃ r`, `B x₁ x₂ x₄ r`, `C x₁ x₃ x₄ r`, `D x₂ x₃ x₄ r` with $r = (x_5,\dots,x_{h+1})$ as a tuple `Fin (h-3) → Fin n` (`r ℓ` $= x_{\ell+5}$, 0-based); `E ℓ x₁ x₂ x₃ x₄ r'` with $r'$ the remaining $h-4$ variables in increasing order. Indices are 0-based.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 4, pp.9–10

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The arrays of the auxiliary hyperclique polynomial `T_h`, of size `(N, M, a, b, c)`.**
Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256
6bd5cf5d…7730), Section 4, pp.9–10: "let A, B, C, D be matrix-valued arrays, where each matrix has
size A_{x̂₄} ∈ Z^{a×c}, B_{x̂₃} ∈ Z^{c×b}, C_{x̂₂} ∈ Z^{b×c}, D_{x̂₁} ∈ Z^{c×a} … In addition, the arrays
E₅, …, E_{h+1} have three-dimensional entries: E_{5;x̂₅}, …, E_{h+1;x̂_{h+1}} ∈ Z^{a×b×c}. … x₂, x₃
range over [N] and x₁, x₄ range over [M]; the variables x₅, …, x_{h+1} always range over [n]."

Each array omits exactly one of the variables `x₁, …, x_{h+1}`:
1. `A x₁ x₂ x₃ r` is `A_{x̂₄}` (an `a × c` matrix);
2. `B x₁ x₂ x₄ r` is `B_{x̂₃}` (`c × b`);
3. `C x₁ x₃ x₄ r` is `C_{x̂₂}` (`b × c`);
4. `D x₂ x₃ x₄ r` is `D_{x̂₁}` (`c × a`);
5. `E ℓ x₁ x₂ x₃ x₄ r' α β γ` is `E_{ℓ+5; x̂_{ℓ+5}}[α, β, γ]`.

**Formalization Note.** `x₁, x₄ : Fin M`, `x₂, x₃ : Fin N`; the tuple `r : Fin (h − 3) → Fin n` is
`(x₅, …, x_{h+1})` (`r ℓ = x_{ℓ+5}`). For `E ℓ` the tuple `r' : Fin (h − 4) → Fin n` lists the
remaining variables `x_j`, `j ∉ {1,2,3,4, ℓ+5}`, in increasing order (see `tPoly`). For `h = 3`
there are no arrays `E` (`Fin 0`). Section 4 has `h ≥ 3`. -/
structure TData (h N M a b c n : ℕ) where
  /-- `A_{x̂₄}`: depends on `x₁, x₂, x₃, x₅, …` -/
  A : Fin M → Fin N → Fin N → (Fin (h - 3) → Fin n) → Matrix (Fin a) (Fin c) ℤ
  /-- `B_{x̂₃}`: depends on `x₁, x₂, x₄, x₅, …` -/
  B : Fin M → Fin N → Fin M → (Fin (h - 3) → Fin n) → Matrix (Fin c) (Fin b) ℤ
  /-- `C_{x̂₂}`: depends on `x₁, x₃, x₄, x₅, …` -/
  C : Fin M → Fin N → Fin M → (Fin (h - 3) → Fin n) → Matrix (Fin b) (Fin c) ℤ
  /-- `D_{x̂₁}`: depends on `x₂, x₃, x₄, x₅, …` -/
  D : Fin N → Fin N → Fin M → (Fin (h - 3) → Fin n) → Matrix (Fin c) (Fin a) ℤ
  /-- `E_{ℓ+5; x̂_{ℓ+5}}`: depends on `x₁, x₂, x₃, x₄` and all of `x₅, …` except `x_{ℓ+5}` -/
  E : Fin (h - 3) → Fin M → Fin N → Fin N → Fin M → (Fin (h - 4) → Fin n) →
    Fin a → Fin b → Fin c → ℤ

end HypercliqueFalse


