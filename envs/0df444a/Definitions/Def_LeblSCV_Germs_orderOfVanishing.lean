-- Prove2me | Definitions.Def_LeblSCV_Germs_orderOfVanishing
-- name    : LeblSCV_Germs_orderOfVanishing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:41.598836+00:00
-- url     : https://prove2.me/theorems/d9e80294-7f64-4e18-ade2-d22456f6db65
-- title:
--   Definition 6.2.1 — order of vanishing $\operatorname{ord}_p f$
-- statement:
--   Let $p \in \mathbb{C}^n$ and let $f$ be holomorphic in a neighborhood of $p$, with expansion $f(z) = \sum_{k=0}^\infty f_k(z - p)$ into homogeneous polynomials $f_k$ of degree $k$. If $f$ is not identically zero, its **order of vanishing** at $p$ is
--   $$ \operatorname{ord}_p f = \min\{ k \in \mathbb{N}_0 : f_k \not\equiv 0 \}, $$
--   and $\operatorname{ord}_p f = \infty$ if $f \equiv 0$. Equivalently, all partial derivatives of $f$ of order less than $k$ vanish at $p$ and some derivative of order $k$ does not.
--
--   **Formalization Note.** Defined for any complex normed space $E$ (in this mission $E = \mathbb{C}$ and $E = \mathbb{C}^n$), with values in `ℕ∞`: `orderOfVanishing f p` is the infimum of those $k$ for which the $k$-th Fréchet derivative `iteratedFDeriv ℂ k f p` is nonzero; the infimum of the empty set is $\infty$. Since $f_k(h) = \frac{1}{k!} D^k f(p)(h, \dots, h)$ and a symmetric multilinear map is zero exactly when it vanishes on the diagonal, $D^k f(p) \neq 0$ iff $f_k \not\equiv 0$. The definition is only used for functions holomorphic near $p$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 169, Definition 6.2.1

import Mathlib

namespace LeblSCV.Germs

/-- Definition 6.2.1 (Lebl, p. 169). For `f` holomorphic in a neighborhood of `p`, write
`f(z) = ∑_k f_k(z - p)` with `f_k` homogeneous of degree `k`. The order of vanishing is
`ord_p f = min {k ∈ ℕ₀ : f_k ≢ 0}`, and `ord_p f = ∞` if `f ≡ 0`. Since
`f_k(h) = (1/k!) Dᵏf(p)(h, …, h)` and a symmetric multilinear map vanishes iff it vanishes on
the diagonal, `f_k ≢ 0` iff the `k`-th derivative `Dᵏf(p)` is nonzero (the book's rephrasing:
"all partial derivatives of order less than `k` vanish at `p`, and at least one derivative of
order `k` does not"). The infimum over the empty set in `ℕ∞` is `⊤ = ∞`, the book's convention
for `f ≡ 0`. Only meaningful for `f` holomorphic near `p`, which every use assumes. -/
noncomputable def orderOfVanishing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (p : E) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : iteratedFDeriv ℂ k f p ≠ 0), (k : ℕ∞)

end LeblSCV.Germs


