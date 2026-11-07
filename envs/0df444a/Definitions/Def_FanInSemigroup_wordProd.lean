-- Prove2me | Definitions.Def_FanInSemigroup_wordProd
-- name    : FanInSemigroup_wordProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:59.594044+00:00
-- url     : https://prove2.me/theorems/9bc3f267-c119-4158-81fb-3ef450884b39
-- title:
--   Product of a nonempty word and positive powers in a semigroup
-- statement:
--   In a semigroup $S$ the product $a_0a_1\cdots a_l$ of a nonempty word is defined, and so is the product $a_1a_2\cdots a_n$ of an $n$-tuple with $n\ge 1$, and the power $b^m$ with $m\ge 1$, the product of $m$ copies of $b$. A semigroup has no empty product and no $b^0$.
--
--   These are the products that semigroup circuits compute and that the language $L(S,a)$ tests.
--
--   **Formalization Note** A nonempty word is given by its first letter and the rest, and is multiplied from the left. The exponent of a power lies in the positive naturals.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.54; proof of Lemma 2.4, p.55

import Mathlib

set_option autoImplicit false

namespace FanInSemigroup

variable {S : Type*} [Semigroup S]

/-- The product `a₀ a₁ ⋯ a_l` of a nonempty word, whose first letter is `a₀`, in a semigroup.
Chandra, Fortune, Lipton, STOC 1983, §2, p.54.

**Formalization Note.** A semigroup has no empty product, so a nonempty word is given by its first
letter and the rest; associativity makes the bracketing immaterial. -/
def wordProd (a₀ : S) (l : List S) : S :=
  l.foldl (· * ·) a₀

/-- The product `a₁a₂⋯aₙ` of an `n`-tuple, `n ≥ 1`. p.54: "the output is the encoding of the
product a1a2...an." -/
def tupleProd {n : ℕ} (hn : 1 ≤ n) (a : Fin n → S) : S :=
  wordProd (a ⟨0, hn⟩) (List.ofFn a).tail

/-- The power `b^m`, `m ≥ 1`, of an element of a semigroup, as the product of `m` copies of `b`.
Chandra, Fortune, Lipton, STOC 1983, proof of Lemma 2.4, p.55.

**Formalization Note.** Mathlib has no power on a bare `Semigroup`. The exponent is in `ℕ+`, so
no `b^0` occurs. -/
def ppow (b : S) (m : ℕ+) : S :=
  wordProd b (List.replicate m.natPred b)

end FanInSemigroup


