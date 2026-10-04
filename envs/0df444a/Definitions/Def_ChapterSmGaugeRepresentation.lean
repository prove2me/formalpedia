-- Prove2me | Definitions.Def_ChapterSmGaugeRepresentation
-- name    : ChapterSmGaugeRepresentation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:01:20.55328+00:00
-- url     : https://prove2.me/theorems/d865aebf-f14e-4f00-a0fb-1e0d2f12ba5b
-- title:
--   Chapter SmGaugeRepresentation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmGaugeRepresentation.lean`): generated def bundle for ChapterSmGaugeRepresentation. See BookProof/ChapterSmGaugeRepresentation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmGaugeRepresentation.lean

import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsSU3
import Mathlib


/-!
# A concrete Standard-Model gauge representation, and a fully instantiated BRST charge

`BookProof.ChapterSmBrstGhost` proves that the Standard-Model BRST charge

```
Ω = Σ_a c^a G_a − ½ Σ f_{abc} c^a c^b b_c ,     G_a = −i dΓ(T_a)
```

is nilpotent *whenever* the twelve matter generators `T_a` close with the structure
constants `smStruct f₃` of `su(3) ⊕ su(2) ⊕ u(1)`.  This module removes the last hypothesis
that is a statement about a representation rather than about the Lie algebra: it builds a
**concrete** family of twelve generators — one coloured weak doublet, i.e. the internal
space `ℂ³ ⊗ ℂ²` of a quark multiplet at one plane-wave momentum, with hypercharge `y` —
and proves that it closes with exactly those structure constants.

## What is proved

* `pauli`, `su2gen` — the Pauli matrices and the `su(2)` generators `τ_k / 2`, with
  **`su2gen_closes`**: `[τ_j/2, τ_k/2] = i ε_{jkl} τ_l/2`, i.e. they close with the
  Levi-Civita structure constants `su2Struct` of `BookProof.ChapterSmBrstGhost`.
* `smGenP` — the twelve generators on the internal space `ℂ³ ⊗ ℂ²`: the eight gluon
  directions `T_a ⊗ 1`, the three weak directions `1 ⊗ τ_k/2` and the hypercharge `y·1`;
  **`smGenP_closes`** — they close with `sumStruct f₃ (sumStruct su2Struct u1Struct)`, the
  direct-sum structure constants (a bracket never leaves its summand, the colour and weak
  factors commute, and the hypercharge is central).
* `smGen` — the same twelve generators on the six matter modes `Fin 6 ≃ Fin 3 × Fin 2`, with
  **`smGen_closes`**: `ClosesWithStructureConstants (smGen S₃ y) (smStruct f₃)`.
* **`sm_brst_nilpotent_rep`** — the Standard-Model BRST charge of this concrete multiplet,
  on the eighteen-mode Fock space (six matter modes and twelve ghosts), squares to zero.
  Its only remaining inputs are the two defining relations of the `su(3)` generators
  themselves (`TraceOrthonormal`, `ClosesWithStructureConstants`), from which the
  antisymmetry and the Jacobi identity of `f₃` are *derived*, through
  `BookProof.YangMillsSU3.structureConstant_antisymm_swap` and
  `BookProof.YangMillsSU3.structureConstant_jacobi`.
* `sm_brst_nilpotent_of_su3_relations` — the same reduction of the hypotheses for an
  arbitrary matter representation.

## Honest boundary

The multiplet is one coloured weak doublet at one momentum: the mode set is finite, as in
`BookProof.ChapterSmBrstGhost`.  The `su(3)` generators enter through their two defining
relations rather than through the explicit Gell-Mann table, and nothing is claimed about the
size of the BRST cohomology.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGaugeRep

open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

/-! ## 1. The `su(2)` generators -/

/-- The three Pauli matrices. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- The `su(2)` generators in the physics normalization, `τ_k / 2`. -/
def su2gen (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • pauli k



/-! ## 2. The twelve generators on the internal space `ℂ³ ⊗ ℂ²` -/

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}









/-- **The twelve Standard-Model generators on the internal space of one coloured weak
doublet**: `T_a ⊗ 1` in the eight gluon directions, `1 ⊗ τ_k/2` in the three weak
directions, and the central hypercharge `y·1`. -/
def smGenP (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) :
    (Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) → Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ
  | Sum.inl a => S3 a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | Sum.inr (Sum.inl k) => (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ su2gen k
  | Sum.inr (Sum.inr _) => ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)







/-! ## 3. The generators on the six matter modes -/

/-- The colour–isospin mode labelling: the `3 × 2 = 6` modes of one coloured weak doublet at
one plane-wave momentum. -/
def internalEquiv : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv

/-- The matrix algebra of the internal space, transported to the six matter modes. -/
def toModes : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ internalEquiv

/-- **The twelve Standard-Model generators on the six matter modes.** -/
def smGen (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) (a : Fin 12) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  toModes (smGenP S3 y (smIdxEquiv a))



/-! ## 4. The fully instantiated BRST charge -/





end

end BookProof.SmGaugeRep


