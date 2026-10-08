-- Prove2me | Definitions.Def_MathieuM23_Regular
-- name    : MathieuM23_Regular
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T15:21:31.825721+00:00
-- url     : https://prove2.me/theorems/9bdee3de-1f19-4381-8617-dc47b03c3b11
-- title:
--   Regular extensions of $\mathbb{Q}(t)$
-- statement:
--   Let $L$ be a field extension of the rational function field $\mathbb{Q}(t)$. Then $L$ is **regular** (over $\mathbb{Q}$) if it contains no nontrivial algebraic extension of $\mathbb{Q}$. That is, every $x\in L$ that is algebraic over $\mathbb{Q}$ already lies in $\mathbb{Q}$.
--
--   Regularity is what lets Hilbert's irreducibility theorem specialize a regular $G$-extension of $\mathbb{Q}(t)$ to infinitely many $G$-extensions of $\mathbb{Q}$.
--
--   **Formalization Note** "Algebraic over $\mathbb{Q}$" is expressed as being a root of a nonzero polynomial $p\in\mathbb{Q}[X]$, with $\mathbb{Q}$ acting on $L$ through $\mathbb{Q}\subset\mathbb{Q}(t)\to L$. This avoids choosing a separate $\mathbb{Q}$-algebra structure on $L$.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 2, §1.2 (definition of a regular extension)

import Mathlib

/-! # Regular extensions of `ℚ(t)` (§1.2) -/

namespace MathieuM23

/-- An extension `L` of `ℚ(t)` is *regular* if it contains no nontrivial algebraic extension of
`ℚ`: every element of `L` that is a root of a nonzero polynomial with rational coefficients
already lies in (the image of) `ℚ`. -/
def IsRegularOverRatFunc (L : Type*) [Field L] [Algebra (RatFunc ℚ) L] : Prop :=
  ∀ x : L, (∃ p : Polynomial ℚ, p ≠ 0 ∧
      Polynomial.aeval x (p.map (algebraMap ℚ (RatFunc ℚ))) = 0) →
    ∃ q : ℚ, algebraMap (RatFunc ℚ) L (algebraMap ℚ (RatFunc ℚ) q) = x

end MathieuM23


