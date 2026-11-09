-- Prove2me | Definitions.Def_MaskingHardness_IsConvConcConjWith
-- name    : MaskingHardness_IsConvConcConjWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:31.799778+00:00
-- url     : https://prove2.me/theorems/2b5936e8-4946-47fb-b530-17659e6a3e59
-- title:
--   Convex–concave conjugates $g,h$ under a real pairing $\langle\cdot,\cdot\rangle$
-- statement:
--   Let $V$ be a set carrying a real pairing $\langle\cdot,\cdot\rangle : V\times V\to\mathbb R$, and let $g,h : V\to\overline{\mathbb R}=\mathbb R\cup\{\pm\infty\}$. The pair $(g,h)$ is a pair of **convex–concave conjugates** for this pairing if
--
--   1. $g(a)=\sup_{b\in V}\; h(b)-\langle a,b\rangle$ for every $a\in V$;
--   2. $h(b)=\inf_{a\in V}\; g(a)+\langle a,b\rangle$ for every $b\in V$;
--   3. $g$ is proper: $g$ never takes the value $-\infty$ and is not identically $+\infty$;
--   4. $h$ is proper concave: $h$ never takes the value $+\infty$ and is not identically $-\infty$.
--
--   With the dot product of $\mathbb R^n$ this is Definition 2.6 of the paper; with the $\mathcal D$-weighted pairing $\langle a,b\rangle_{\mathcal D}=\mathbb E_{\mathcal D}[\langle a(x,y),b(x,y)\rangle]$ on functions $a,b:\mathcal X\times\mathcal Y\to\mathbb R^k$ it is condition (b) of Theorem 3.3. Fenchel duality (Theorem 2.9) and the six-functions theorem (Theorem 3.3) are stated for such pairs.
--
--   **Formalization Note** $\overline{\mathbb R}$ is `EReal`. Definition 2.6 also requires $g$ closed convex and $h$ closed concave; when the pairing is continuous and linear in each argument these follow from items 1 and 2 (a supremum of affine functions is closed and convex, an infimum of affine functions is closed and concave), so only properness is written out. Properness excludes the degenerate pairs $(+\infty,+\infty)$ and $(-\infty,-\infty)$, which satisfy items 1 and 2.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 2.6, p.17 (PDF p.19); the pairing ⟨a, b⟩_D of Theorem 3.3 (b), p.21 (PDF p.23) and Eq. (8), p.20 (PDF p.22)

import Mathlib

namespace MaskingHardness

/-- **Convex–concave conjugates under a pairing** (Gopalan–Prabhakaran–Tankala, *Universal
Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d,
Definition 2.6, printed p.17 = PDF p.19; used with the pairing `⟨a, b⟩_D` in Theorem 3.3 (b),
printed p.21 = PDF p.23, and in (8), printed p.20 = PDF p.22).

Two extended-real functions `g, h : V → ℝ̄` are convex–concave conjugates for a real pairing
`⟨·,·⟩` if
`g(a) = sup_b h(b) − ⟨a, b⟩` and `h(b) = inf_a g(a) + ⟨a, b⟩` for all `a, b`,
`g` is proper convex (never `−∞`, not identically `+∞`) and `h` is proper concave (never `+∞`,
not identically `−∞`).

**Formalization Note** ℝ̄ is `EReal`. The paper's Definition 2.6 also asks that `g` be closed
and convex and `h` closed and concave; these follow from the two formulas (a supremum of affine
functions is closed convex, an infimum is closed concave), so only properness is written out.
The pairing is a parameter: the dot product of `ℝⁿ` gives Definition 2.6 itself
(`IsConvConcConj`), and `⟨a, b⟩_D = E_D[⟨a(x,y), b(x,y)⟩]` gives Theorem 3.3 (b). -/
def IsConvConcConjWith {V : Type*} (pair : V → V → ℝ) (g h : V → EReal) : Prop :=
  (∀ a, g a = ⨆ b, h b - ((pair a b : ℝ) : EReal)) ∧
  (∀ b, h b = ⨅ a, g a + ((pair a b : ℝ) : EReal)) ∧
  (∀ a, g a ≠ ⊥) ∧ (∃ a, g a ≠ ⊤) ∧
  (∀ b, h b ≠ ⊤) ∧ (∃ b, h b ≠ ⊥)

end MaskingHardness


