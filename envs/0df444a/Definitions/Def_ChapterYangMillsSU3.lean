-- Prove2me | Definitions.Def_ChapterYangMillsSU3
-- name    : ChapterYangMillsSU3
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-08T01:41:39.622716+00:00
-- url     : https://prove2.me/theorems/9e152958-8ad1-49a6-acf4-0ed55b3277fb
-- title:
--   SU(3) structure constants
-- statement:
--   Formal definitions for the SU(3) structure constants of the timepiece Lean 4 formalization (module `BookProof.YangMillsSU3`, source chapter `BookProof/ChapterYangMillsSU3.lean`).
--
--   Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (line ~7001).
--
--   The book opens the SU(3) construction with the defining relations of the `SU(N)` generators `T_a` and their structure constants `f_{abc}`:
--
--   ``` [T_a, T_b] = i f_{abc} T_c tr(T_a T_b) = ½ δ_{ab} ```
--
--   (The electromagnetic case is recovered by dropping the `SU(N)` index and setting `f_{abc} = 0`.) This file formalizes the self-contained algebraic content of these two relations. Working with an arbitrary finite family of complex matrices `T : Fin d → Matrix (Fin n) (Fin n) ℂ` satisfying the two hypotheses above (with *real* structure constants `f`), we prove:
--
--   * `structureConstant_formula` — the closed formula recovering the structure constants from the trace, `f_{abd} = -2 i · tr([T_a, T_b] T_d)`, the algebraic reason the two book relations determine `f` uniquely; * `structureConstant_antisymm_swap` — antisymmetry in the first two indices, `f_{abc} = - f_{bac}` (immediate from `[T_a, T_b] = -[T_b, T_a]`); * `structureConstant_antisymm_rotate` — antisymmetry in the last two indices, `f_{abc} = - f_{acb}` (the genuine content, via cyclicity of the trace); * `structureConstant_totally_antisymmetric` — the standard corollary that the structure constants are **totally antisymmetric** under any transposition of indices; * `structureConstant_jacobi` — the **Jacobi identity for the structure constants**, `Σₑ (f_{abe} f_{ech} + f_{bce} f_{eah} + f_{cae} f_{ebh}) = 0`, obtained by projecting the matrix Jacobi identity onto the trace-orthonormal basis. This is precisely the identity that makes the BRST charge `Ω` (with its cubic ghost term `f_{abc} ψ†_a ψ†_b ψ_c`) nilpotent.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsSU3.lean

import Mathlib

/-!
# Chapter "Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory",
§"Pure SU(3) Yang-Mills theory" — the structure constants

Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and
Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"*
(line ~7001).

The book opens the SU(3) construction with the defining relations of the
`SU(N)` generators `T_a` and their structure constants `f_{abc}`:

```
[T_a, T_b] = i f_{abc} T_c
tr(T_a T_b) = ½ δ_{ab}
```

(The electromagnetic case is recovered by dropping the `SU(N)` index and setting
`f_{abc} = 0`.)  This file formalizes the self-contained algebraic content of
these two relations.  Working with an arbitrary finite family of complex
matrices `T : Fin d → Matrix (Fin n) (Fin n) ℂ` satisfying the two hypotheses
above (with *real* structure constants `f`), we prove:

* `structureConstant_formula` — the closed formula recovering the structure
  constants from the trace, `f_{abd} = -2 i · tr([T_a, T_b] T_d)`, the algebraic
  reason the two book relations determine `f` uniquely;
* `structureConstant_antisymm_swap` — antisymmetry in the first two indices,
  `f_{abc} = - f_{bac}` (immediate from `[T_a, T_b] = -[T_b, T_a]`);
* `structureConstant_antisymm_rotate` — antisymmetry in the last two indices,
  `f_{abc} = - f_{acb}` (the genuine content, via cyclicity of the trace);
* `structureConstant_totally_antisymmetric` — the standard corollary that the
  structure constants are **totally antisymmetric** under any transposition of
  indices;
* `structureConstant_jacobi` — the **Jacobi identity for the structure
  constants**, `Σₑ (f_{abe} f_{ech} + f_{bce} f_{eah} + f_{cae} f_{ebh}) = 0`,
  obtained by projecting the matrix Jacobi identity onto the trace-orthonormal
  basis.  This is precisely the identity that makes the BRST charge `Ω`
  (with its cubic ghost term `f_{abc} ψ†_a ψ†_b ψ_c`) nilpotent.
-/

open Matrix BigOperators

namespace BookProof.YangMillsSU3

variable {n d : ℕ}
variable (T : Fin d → Matrix (Fin n) (Fin n) ℂ)
variable (f : Fin d → Fin d → Fin d → ℝ)

/-- Trace-orthonormality of the `SU(N)` generators: `tr(T_a T_b) = ½ δ_{ab}`. -/
def TraceOrthonormal : Prop :=
  ∀ a b, (T a * T b).trace = (if a = b then (1 / 2 : ℂ) else 0)

/-- The generators close under commutation with *real* structure constants:
`[T_a, T_b] = i f_{abc} T_c`. -/
def ClosesWithStructureConstants : Prop :=
  ∀ a b, T a * T b - T b * T a = Complex.I • ∑ c, (f a b c : ℂ) • T c

variable {T f}

/-
**Structure-constant formula.**  The two book relations recover the
structure constants from the trace: `f_{abd} = -2 i · tr([T_a, T_b] T_d)`.
-/


/-
**Antisymmetry in the first two indices**: `f_{abc} = - f_{bac}`.
-/


/-
**Antisymmetry in the last two indices**: `f_{abc} = - f_{acb}`.
This is the genuine content, following from cyclicity of the trace.
-/




/-
**Jacobi identity for the structure constants**:
`Σₑ (f_{abe} f_{ech} + f_{bce} f_{eah} + f_{cae} f_{ebh}) = 0`,
the projection of the matrix Jacobi identity onto the trace-orthonormal basis.
This is the identity that makes the BRST charge nilpotent.
-/


end BookProof.YangMillsSU3


