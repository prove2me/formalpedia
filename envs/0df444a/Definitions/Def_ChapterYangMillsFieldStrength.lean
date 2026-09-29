-- Prove2me | Definitions.Def_ChapterYangMillsFieldStrength
-- name    : ChapterYangMillsFieldStrength
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T14:19:48.133715+00:00
-- url     : https://prove2.me/theorems/87dafb49-2c90-480d-9236-d2736d6f710a
-- title:
--   Non-abelian field strength and magnetic field
-- statement:
--   Formal definitions for the Non-abelian field strength and magnetic field of the timepiece Lean 4 formalization (module `BookProof.YangMillsFieldStrength`, source chapter `BookProof/ChapterYangMillsFieldStrength.lean`).
--
--   Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (line ~7020).
--
--   Continuing `ChapterYangMillsSU3.lean` (the structure constants) and `ChapterYangMillsBianchi.lean` (the covariant derivative and the Bianchi/Jacobi identity), this file formalizes the next self-contained algebraic content of the same section: the explicit **non-abelian field strength formula** that the book records right after the covariant derivative,
--
--   ``` D_j = ∂_j - i g T_a A_{j a}, [D_j, D_k] = -i g T_a F_{j k a} B_{i a} = ½ ε_{i j k} (∂_j A_{k a} - ∂_k A_{j a} - g f_{a b c} A_{j b} A_{k c}). ```
--
--   The key algebraic identity is that the commutator of two covariant derivatives is a *zeroth-order* (multiplication) operator, whose multiplier is the field strength. We model this abstractly: the covariant derivative acts on an associative ring `R` (the "field values", e.g. matrices acting on the left) as
--
--   ``` D_j x = δ_j x + a_j * x, ```
--
--   where `δ : Fin 3 → R → R` is a family of **commuting Leibniz derivations** (the partial derivatives `∂_j`) and `a_j ∈ R` is the connection (`a_j = -i g A_j` in the book). Then
--
--   ``` [D_j, D_k] x = F_{j k} * x, F_{j k} = δ_j a_k - δ_k a_j + (a_j a_k - a_k a_j), ```
--
--   i.e. the double derivative terms cancel by commutativity of the `δ`'s and the mixed first-order terms cancel identically, leaving a pure multiplication operator (`nonabelian_fieldStrength`). Specializing to the book's connection `a_j = -i g A_j` in a complex algebra recovers exactly the book's magnetic field-strength combination
--
--   ``` [D_j, D_k] x = (-i g • F^{book}_{j k}) * x, F^{book}_{j k} = (∂_j A_k - ∂_k A_j) - i g (A_j A_k - A_k A_j) ```
--
--   (`commutator_eq_coupling`), where the non-abelian correction `-i g [A_j, A_k]` expands, via `[T_a, T_b] = i f_{a b c} T_c` (see `ChapterYangMillsSU3.lean`), into the book's `+ g f_{a b c} A_{j b} A_{k c}` term.
--
--   * `Dcov` — the covariant derivative `D_j x = δ_j x + a_j * x`; * `fieldStrengthMul` — the abstract field strength `F_{j k} = δ_j a_k - δ_k a_j + [a_j, a_k]`; * `nonabelian_fieldStrength` — `[D_j, D_k] x = F_{j k} * x` (the commutator of covariant derivatives is multiplication by the field strength); * `fieldStrengthMul_antisymm` — `F_{j k} = - F_{k j}`; * `Fbook` — the book's field-strength combination `(∂_j A_k - ∂_k A_j) - i g [A_j, A_k]`; * `commutator_eq_coupling` — `[D_j, D_k] x = (-i g • F^{book}_{j k}) * x` for the book's connection `a_j = -i g A_j`; * `Fbook_antisymm` — `F^{book}_{j k} = - F^{book}_{k j}`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFieldStrength.lean

import Mathlib

/-!
# Chapter "Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory",
§"Pure SU(3) Yang-Mills theory" — the non-abelian field strength and the magnetic field

Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and
Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"*
(line ~7020).

Continuing `ChapterYangMillsSU3.lean` (the structure constants) and
`ChapterYangMillsBianchi.lean` (the covariant derivative and the Bianchi/Jacobi
identity), this file formalizes the next self-contained algebraic content of the
same section: the explicit **non-abelian field strength formula** that the book
records right after the covariant derivative,

```
D_j = ∂_j - i g T_a A_{j a},        [D_j, D_k] = -i g T_a F_{j k a}
B_{i a} = ½ ε_{i j k} (∂_j A_{k a} - ∂_k A_{j a} - g f_{a b c} A_{j b} A_{k c}).
```

The key algebraic identity is that the commutator of two covariant derivatives
is a *zeroth-order* (multiplication) operator, whose multiplier is the field
strength.  We model this abstractly: the covariant derivative acts on an
associative ring `R` (the "field values", e.g. matrices acting on the left) as

```
D_j x = δ_j x + a_j * x,
```

where `δ : Fin 3 → R → R` is a family of **commuting Leibniz derivations**
(the partial derivatives `∂_j`) and `a_j ∈ R` is the connection
(`a_j = -i g A_j` in the book).  Then

```
[D_j, D_k] x = F_{j k} * x,    F_{j k} = δ_j a_k - δ_k a_j + (a_j a_k - a_k a_j),
```

i.e. the double derivative terms cancel by commutativity of the `δ`'s and the
mixed first-order terms cancel identically, leaving a pure multiplication
operator (`nonabelian_fieldStrength`).  Specializing to the book's connection
`a_j = -i g A_j` in a complex algebra recovers exactly the book's magnetic
field-strength combination

```
[D_j, D_k] x = (-i g • F^{book}_{j k}) * x,
F^{book}_{j k} = (∂_j A_k - ∂_k A_j) - i g (A_j A_k - A_k A_j)
```

(`commutator_eq_coupling`), where the non-abelian correction `-i g [A_j, A_k]`
expands, via `[T_a, T_b] = i f_{a b c} T_c` (see `ChapterYangMillsSU3.lean`),
into the book's `+ g f_{a b c} A_{j b} A_{k c}` term.

* `Dcov` — the covariant derivative `D_j x = δ_j x + a_j * x`;
* `fieldStrengthMul` — the abstract field strength `F_{j k} = δ_j a_k - δ_k a_j + [a_j, a_k]`;
* `nonabelian_fieldStrength` — `[D_j, D_k] x = F_{j k} * x` (the commutator of
  covariant derivatives is multiplication by the field strength);
* `fieldStrengthMul_antisymm` — `F_{j k} = - F_{k j}`;
* `Fbook` — the book's field-strength combination `(∂_j A_k - ∂_k A_j) - i g [A_j, A_k]`;
* `commutator_eq_coupling` — `[D_j, D_k] x = (-i g • F^{book}_{j k}) * x` for the
  book's connection `a_j = -i g A_j`;
* `Fbook_antisymm` — `F^{book}_{j k} = - F^{book}_{k j}`.
-/

open Complex

namespace BookProof.YangMillsFieldStrength

section Abstract

variable {R : Type*} [Ring R]

/-- The covariant derivative acting on the ring of field values,
`D_j x = δ_j x + a_j * x`, where `δ_j` is the partial derivative `∂_j` and `a_j`
is the connection (`a_j = -i g A_j` in the book, with `A_j` acting by left
multiplication). -/
def Dcov (δ : Fin 3 → R → R) (a : Fin 3 → R) (j : Fin 3) (x : R) : R := δ j x + a j * x

/-- The (abstract) non-abelian field strength, the multiplier appearing in the
commutator of two covariant derivatives:
`F_{j k} = δ_j a_k - δ_k a_j + (a_j a_k - a_k a_j)`. -/
def fieldStrengthMul (δ : Fin 3 → R → R) (a : Fin 3 → R) (j k : Fin 3) : R :=
  (δ j (a k) - δ k (a j)) + (a j * a k - a k * a j)





end Abstract

section Coupling

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The book's field-strength combination
`F^{book}_{j k} = (∂_j A_k - ∂_k A_j) - i g (A_j A_k - A_k A_j)`, with `A_j` the
matrix-valued gauge potential `A_j = T_a A_{j a}` and `g` the coupling constant.
Its non-abelian term `-i g [A_j, A_k]` expands, via `[T_a, T_b] = i f_{a b c} T_c`
(see `ChapterYangMillsSU3.lean`), into the book's `+ g f_{a b c} A_{j b} A_{k c}`. -/
def Fbook (δ : Fin 3 → R → R) (g : ℝ) (A : Fin 3 → R) (j k : Fin 3) : R :=
  (δ j (A k) - δ k (A j)) - (I * (g : ℂ)) • (A j * A k - A k * A j)







end Coupling

end BookProof.YangMillsFieldStrength


