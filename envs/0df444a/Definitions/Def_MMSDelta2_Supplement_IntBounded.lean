-- Prove2me | Definitions.Def_MMSDelta2_Supplement_IntBounded
-- name    : MMSDelta2_Supplement_IntBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:05:43.834218+00:00
-- url     : https://prove2.me/theorems/5d94646b-1c1e-4c13-9e4b-8ca46d0ee1f1
-- title:
--   Instances with polynomially bounded integer values (the unary regime)
-- statement:
--   Fix $k\in\mathbb N$. An additive instance $v$ with $n$ agents and $m$ goods is **$k$-bounded** if every value is an integer whose absolute value is at most a fixed polynomial of the instance's length:
--   $$\forall i,g:\quad v_i(g)\in\mathbb Z\quad\text{and}\quad |v_i(g)|\le \ell^k+k,$$
--   where $\ell$ is the length of the binary code of the instance.
--
--   Restricting a problem to $k$-bounded instances for some fixed $k$ is the Garey–Johnson definition of hardness "even when all numerical values are given in unary" (p.3), used for the strong co-NP-hardness of Theorem 1.3 and its chores version in Theorem 1.5.
--
--   **Formalization Note** $\ell$ is the length of the base mission's `instCode n m v`. Every polynomial is bounded by one of the form $\ell^k+k$.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §1.1, p.3 (PDF p.5) ('the hardness persists even when all numerical values are given in unary'); proof of Theorem 1.3, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_MMSDelta2_instCode

namespace MMSDelta2.Supplement

/-!
# Instances whose values are polynomially bounded integers (the unary regime)

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §1.1, p.3 (PDF p.5): strong co-NP-hardness means
"the hardness persists even when all numerical values are given in unary"; proof of Theorem 1.3,
p.43 (PDF p.45): "All values in the FST core are polynomially bounded in n."

**Formalization Note.** Strong hardness is the Garey–Johnson notion: for some polynomial `p`, the
problem restricted to instances whose numbers are integers bounded by `p(length of the instance)`
is hard. Here the polynomial is `ℓ ↦ ℓ^k + k` and the length is that of the instance's binary code
`instCode n m v` (base mission).
-/

/-- Every item value of `v` is an integer of absolute value at most `ℓ^k + k`, where `ℓ` is the
length of the binary code of the instance. -/
def IntBounded (k n m : ℕ) (v : Fin n → Fin m → ℚ) : Prop :=
  ∀ i g, ∃ z : ℤ, v i g = (z : ℚ) ∧ |z| ≤ (((instCode n m v).length ^ k + k : ℕ) : ℤ)

end MMSDelta2.Supplement


