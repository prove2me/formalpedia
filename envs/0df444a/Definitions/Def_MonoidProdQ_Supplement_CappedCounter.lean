-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_CappedCounter
-- name    : MonoidProdQ_Supplement_CappedCounter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:08:25.438191+00:00
-- url     : https://prove2.me/theorems/ec1b6e2e-75fa-49a5-8d0b-cc082e1879a0
-- title:
--   Capped counters $M_{k,r}$
-- statement:
--   For integers $k,r\ge1$ let $C_{k+1}=\{0,1,\dots,k\}$ with **capped addition**
--
--   $$a\oplus b=\min\{a+b,\,k\},$$
--
--   and let $M_{k,r}=C_{k+1}^r$ with the coordinatewise operation. It is a commutative monoid with identity the zero vector, $|M_{k,r}|=(k+1)^r$, and every element satisfies $x^{k+1}=x^k$. Theorem 27 shows that its product breadth is exactly $kr$, so it witnesses the near-optimality of the general breadth bound of Theorem 25.
--
--   **Formalization Note** An element wraps a vector of coordinates indexed by $\{0,\dots,r-1\}$ with entries in $\{0,\dots,k\}$. The commutative monoid structure, finiteness and decidable equality are defined with the type; the hypotheses $k,r\ge1$ are carried by the statements.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.5, p.39

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.5, p.39: "For integers k, r ≥ 1, let
C_{k+1} = {0, 1, …, k}, a ⊕ b = min{a + b, k}, and put M_{k,r} = C_{k+1}^r": the capped counter
`M_{k,r}`, whose elements are vectors `(a₁, …, a_r)` with entries in `{0, …, k}`, multiplied
coordinatewise by capped addition; the identity is the zero vector.

**Formalization Note.** An element is a structure wrapping `Fin r → Fin (k + 1)` (so that the
monoid structure below is the only one on the type); the coordinates are indexed by `Fin r`.
The commutative monoid, finite-type and decidable-equality instances are defined in this
module. The hypotheses `k, r ≥ 1` are carried by the statements. -/
@[ext] structure CappedCounter (k r : ℕ) where
  /-- The coordinates `(a₁, …, a_r)`, each in `{0, …, k}`. -/
  val : Fin r → Fin (k + 1)
deriving DecidableEq

namespace CappedCounter

variable {k r : ℕ}

/-- Capped addition `a ⊕ b = min{a + b, k}` in every coordinate, with the zero vector as
identity. -/
instance : CommMonoid (CappedCounter k r) where
  mul a b := ⟨fun i => ⟨min ((a.val i : ℕ) + b.val i) k, by omega⟩⟩
  one := ⟨fun _ => 0⟩
  mul_assoc a b c := by
    ext i
    show min (min ((a.val i : ℕ) + b.val i) k + c.val i) k =
      min ((a.val i : ℕ) + min ((b.val i : ℕ) + c.val i) k) k
    omega
  one_mul a := by
    ext i
    show min (0 + (a.val i : ℕ)) k = a.val i
    have := (a.val i).isLt
    omega
  mul_one a := by
    ext i
    show min ((a.val i : ℕ) + 0) k = a.val i
    have := (a.val i).isLt
    omega
  mul_comm a b := by
    ext i
    show min ((a.val i : ℕ) + b.val i) k = min ((b.val i : ℕ) + a.val i) k
    omega

/-- The counter is finite: it is in bijection with `Fin r → Fin (k + 1)`. -/
instance : Fintype (CappedCounter k r) :=
  Fintype.ofEquiv (Fin r → Fin (k + 1)) ⟨fun v => ⟨v⟩, fun a => a.val, fun _ => rfl, fun _ => rfl⟩

end CappedCounter

end MonoidProdQ.Supplement


