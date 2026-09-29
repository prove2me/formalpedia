-- Prove2me | Definitions.Def_ChapterYangMillsBianchi
-- name    : ChapterYangMillsBianchi
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-08T01:41:20.935579+00:00
-- url     : https://prove2.me/theorems/04160311-5e51-44a7-a7a5-dbb931ecfc06
-- title:
--   Yang-Mills Bianchi identity
-- statement:
--   Formal definitions for the Yang-Mills Bianchi identity of the timepiece Lean 4 formalization (module `BookProof.YangMillsBianchi`, source chapter `BookProof/ChapterYangMillsBianchi.lean`).
--
--   Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (line ~7010).
--
--   Continuing `ChapterYangMillsSU3.lean` (the structure constants), this file formalizes the next self-contained algebraic content of the same section: the covariant derivative
--
--   ``` D_j = ∂_j - i g T_a A_{j a}, [D_j, D_k] = -i g T_a F_{j k a} ```
--
--   and the **Jacobi (Bianchi) relation** the book states for it,
--
--   ``` ε_{i j k} [D_i, [D_j, D_k]] = 0. ```
--
--   All of this is purely algebraic: the covariant derivatives `D_i` are elements of an (arbitrary, associative, possibly non-commutative) ring `R`, and their commutator `⁅·,·⁆ = a*b - b*a` is the ambient Lie bracket. The field strength `F_{j k} = ⁅D_j, D_k⁆` is antisymmetric, and the Levi-Civita contraction of the double commutator vanishes — an immediate consequence of the Jacobi identity `lie_jacobi`. This is exactly the identity underlying the vanishing of the covariant divergence of the magnetic field (`∇·B = 0` / the homogeneous Yang-Mills equation) that the book records right after introducing `B_{i a}`.
--
--   * `eps` — the Levi-Civita symbol on `Fin 3`; * `fieldStrength` — `F_{j k} = ⁅D_j, D_k⁆`, the commutator of covariant derivatives; * `fieldStrength_antisymm` — `F_{j k} = - F_{k j}`; * `bianchi_cyclic` — the cyclic Jacobi identity for the double commutators; * `bianchi` — the book's `ε_{i j k} [D_i, [D_j, D_k]] = 0`; * `bianchi_fieldStrength` — the same written with the field strength, `ε_{i j k} [D_i, F_{j k}] = 0`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsBianchi.lean

import Mathlib

/-!
# Chapter "Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory",
§"Pure SU(3) Yang-Mills theory" — the covariant derivative and the Bianchi (Jacobi) identity

Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and
Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"*
(line ~7010).

Continuing `ChapterYangMillsSU3.lean` (the structure constants), this file
formalizes the next self-contained algebraic content of the same section: the
covariant derivative

```
D_j = ∂_j - i g T_a A_{j a},        [D_j, D_k] = -i g T_a F_{j k a}
```

and the **Jacobi (Bianchi) relation** the book states for it,

```
ε_{i j k} [D_i, [D_j, D_k]] = 0.
```

All of this is purely algebraic: the covariant derivatives `D_i` are elements of
an (arbitrary, associative, possibly non-commutative) ring `R`, and their
commutator `⁅·,·⁆ = a*b - b*a` is the ambient Lie bracket.  The field strength
`F_{j k} = ⁅D_j, D_k⁆` is antisymmetric, and the Levi-Civita contraction of the
double commutator vanishes — an immediate consequence of the Jacobi identity
`lie_jacobi`.  This is exactly the identity underlying the vanishing of the
covariant divergence of the magnetic field (`∇·B = 0` / the homogeneous
Yang-Mills equation) that the book records right after introducing `B_{i a}`.

* `eps` — the Levi-Civita symbol on `Fin 3`;
* `fieldStrength` — `F_{j k} = ⁅D_j, D_k⁆`, the commutator of covariant
  derivatives;
* `fieldStrength_antisymm` — `F_{j k} = - F_{k j}`;
* `bianchi_cyclic` — the cyclic Jacobi identity for the double commutators;
* `bianchi` — the book's `ε_{i j k} [D_i, [D_j, D_k]] = 0`;
* `bianchi_fieldStrength` — the same written with the field strength,
  `ε_{i j k} [D_i, F_{j k}] = 0`.
-/

open BigOperators

namespace BookProof.YangMillsBianchi

/-- The Levi-Civita symbol on `Fin 3`: `+1` for even permutations of `(0,1,2)`,
`-1` for odd permutations, and `0` whenever two indices coincide.  It is written
as the sign of the product of the pairwise differences. -/
def eps (i j k : Fin 3) : ℤ :=
  Int.sign (((j : ℤ) - (i : ℤ)) * ((k : ℤ) - (i : ℤ)) * ((k : ℤ) - (j : ℤ)))

variable {R : Type*} [Ring R]

/-- The (Yang-Mills) field strength as the commutator of covariant derivatives,
`F_{j k} = ⁅D_j, D_k⁆` (equal to `-i g T_a F_{j k a}` in the book's notation). -/
def fieldStrength (D : Fin 3 → R) (j k : Fin 3) : R := ⁅D j, D k⁆





/-
**Bianchi (Jacobi) identity**, `ε_{i j k} [D_i, [D_j, D_k]] = 0`.
-/




end BookProof.YangMillsBianchi


