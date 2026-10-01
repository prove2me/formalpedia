-- Prove2me | Definitions.Def_ChapterSuperBracket
-- name    : ChapterSuperBracket
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:59:32.692591+00:00
-- url     : https://prove2.me/theorems/86f6ba8b-9486-4767-b934-add7acbbef75
-- title:
--   Chapter SuperBracket
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSuperBracket.lean`): generated def bundle for ChapterSuperBracket. See BookProof/ChapterSuperBracket.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSuperBracket.lean

import Mathlib


/-!
# Chapter — Yang–Mills / Classical Statistical Field Theory: the ℤ₂-graded
(super) commutator that unifies the bosonic and fermionic canonical relations

Source: `book.tex`, chapter *"Timepiece and the Gribov ambiguity"*, §*"Pure
Yang-Mills theory"* (line ~7300) and the parent chapter *"Quantization due to
time-evolution: Yang-Mills and Classical Statistical Field Theory"*.

For `SU(3)` Yang–Mills the author builds the Hilbert space as a tensor product
of a symmetric (bosonic) and an antisymmetric (fermionic) Fock space, obtaining
*"a graded Lie superalgebra of creation and annihilation operators, of both
bosonic and fermionic types"*.  The unified canonical (anti)commutation relation
displayed there carries the sign `(-1)^{(α mod 2)(β mod 2)}`:

```
[a(x,…,α), a†(y,…,β)} = a(x,…,α) a†(y,…,β) + (-1)^{(α mod 2)(β mod 2)} a†(y,…,β) a(x,…,α)
```

so that two *bosonic* (even) operators obey the **commutator** relation while two
*fermionic* (odd) operators obey the **anticommutator** relation.  This is the
defining sign of a ℤ₂-graded (super) Lie algebra.

This file isolates that self-contained algebraic content.  In an arbitrary
associative (unital) ring `R` — the algebra of operators — we model the ℤ₂-parity
of a homogeneous element by a `Bool` (`false` = even/bosonic, `true` =
odd/fermionic) and define

* `eps p q = (-1)^{p·q}` (`= -1` iff both `p` and `q` are odd) — the Koszul sign;
* `sbracket p q a b = a·b − ε(p,q)·(b·a)` — the **super-bracket** `⟦a,b⟧`.

We prove:

* `sbracket_even_even` — for two even elements `⟦a,b⟧ = ab − ba` is the ordinary
  **commutator** (bosonic CCR side);
* `sbracket_odd_odd` — for two odd elements `⟦a,b⟧ = ab + ba` is the
  **anticommutator** (fermionic CAR side): this is the single formula unifying
  the two canonical relations of the book;
* `eps_comm`, `eps_mul_self`, `eps_even_left`/`eps_even_right` — the Koszul sign
  is symmetric, squares to `1`, and is trivial against an even element;
* `sbracket_graded_antisymm` — **graded antisymmetry** `⟦a,b⟧ = −ε(p,q)⟦b,a⟧`;
* `super_jacobi` — **headline**: the graded Jacobi identity
  `ε(p,r)⟦a,⟦b,c⟧⟧ + ε(q,p)⟦b,⟦c,a⟧⟧ + ε(r,q)⟦c,⟦a,b⟧⟧ = 0`,
  which makes `(R, ⟦·,·⟧)` a **Lie superalgebra** — exactly the "graded Lie
  superalgebra" structure the book asserts for the creation/annihilation
  operators.  (The inner bracket `⟦b,c⟧` carries parity `xor q r`.)

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterSuperBracket

variable {R : Type*} [Ring R]

/-- The Koszul sign `ε(p,q) = (-1)^{p·q}`, valued in `ℤ`: it is `-1` exactly when
both parities are odd (`true`), and `+1` otherwise.  `false` models an even
(bosonic) degree, `true` an odd (fermionic) degree. -/
def eps (p q : Bool) : ℤ := if (p && q) then -1 else 1









/-- The super-bracket `⟦a,b⟧ = a·b − ε(p,q)·(b·a)` of two homogeneous elements
`a` (parity `p`) and `b` (parity `q`) of the operator algebra `R`. -/
def sbracket (p q : Bool) (a b : R) : R := a * b - (eps p q : R) * (b * a)















end BookProof.ChapterSuperBracket


