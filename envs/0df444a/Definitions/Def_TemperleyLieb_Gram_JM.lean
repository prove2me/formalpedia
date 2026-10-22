-- Prove2me | Definitions.Def_TemperleyLieb_Gram_JM
-- name    : TemperleyLieb_Gram_JM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:47.864071+00:00
-- url     : https://prove2.me/theorems/39a7dba4-1dc0-4fc2-9878-8b3fad44c89c
-- title:
--   §3–4, pp. 10, 13, 15–16 — polynomial and Jucys–Murphy data
-- statement:
--   The polynomial sequence $p_i\in\mathbb Z[x]$ starts with $p_0=0$, $p_1=1$ and satisfies
--
--   $$p_{i+1}=xp_i-p_{i-1}.$$
--
--   The operators $T_0=T_1=0$, $T_2=e_1$ follow the recurrence on p. 10, with $z_i=\sum_{j=0}^i x^jT_{i-j}$. The polynomial $r_t(k)$ is the two-case content attached to the change in shape at stage $k$ on p. 15, and $z_t(k)=\sum_{j=0}^k x^j r_t(k-j)$. These are the explicit eigenvalue data used to state the triangular action, seminormal basis and determinant formula.
--
--   **Formalization Note** The recurrence requires $z_0$; it is set to zero, as the printed sum with $T_0=0$ dictates. The content is zero at stages zero and one and outside the path's stages. Statements use only $0\le k\le n$.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 10, definition of T_i and z_i; p. 13, definition of p_i; p. 15, definition of r_t(k); p. 16, definition of z_t(k)

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Algebra

noncomputable section
open scoped BigOperators

namespace TemperleyLieb.Gram

/-- The polynomials `p₀=0`, `p₁=1`, `pᵢ₊₁=Xpᵢ−pᵢ₋₁` of p. 13. -/
def p : ℕ → Polynomial ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => Polynomial.X * p (k + 1) - p k

/-- The recursive Jucys–Murphy elements `T_k` of p. 10. The two sums are
`z_{i-1}` and `z_{i-2}`; `z₀=0` follows from the printed sum. -/
def JM (S : Type*) [CommRing S] (δ : S) (n k : ℕ) : TL S δ n :=
  Nat.strongRecOn k (fun k rec =>
    if hk : k < 2 then 0
    else if h2 : k = 2 then e S δ n 1
    else
      let i := k - 1;
      let pastZ (m : ℕ) (hm : m < k) : TL S δ n :=
        ∑ j ∈ Finset.range (m + 1), δ ^ j • rec (m - j) (by omega);
      -(e S δ n i * rec i (by omega)) - rec i (by omega) * e S δ n i +
        e S δ n i * e S δ n (i - 1) * rec i (by omega) * e S δ n i -
        pastZ (i - 1) (by omega) - e S δ n i * pastZ (i - 2) (by omega))

/-- `z_k=Σ_{j=0}^k δ^j T_{k-j}` of p. 10. -/
def zJM (S : Type*) [CommRing S] (δ : S) (n k : ℕ) : TL S δ n :=
  ∑ j ∈ Finset.range (k + 1), δ ^ j • JM S δ n (k - j)

/-- The p. 15 content `r_t(k)` in the integral polynomial ring. -/
def r {n : ℕ} {f : Fin (n / 2 + 1)} (t : Tab n f) (k : ℕ) : Polynomial ℤ :=
  if k < 2 ∨ n < k then 0
  else
    let i := cups t k
    if cupStep t k then
      (p i - Polynomial.X * p (i - 1)) * p (k - i + 1)
    else
      (p (k - i + 1) - Polynomial.X * p (k - i)) * p i

/-- The p. 16 cumulative content `z_t(k)=Σ_{i=0}^k X^i r_t(k-i)`. -/
def zt {n : ℕ} {f : Fin (n / 2 + 1)} (t : Tab n f) (k : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (k + 1), Polynomial.X ^ i * r t (k - i)

end TemperleyLieb.Gram


