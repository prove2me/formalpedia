-- Prove2me | Definitions.Def_ChapterGellMann
-- name    : ChapterGellMann
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:13:46.156098+00:00
-- url     : https://prove2.me/theorems/19d1fb50-0119-484f-a4f9-e2122e2d6327
-- title:
--   Chapter GellMann
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGellMann.lean`): generated def bundle for ChapterGellMann. See BookProof/ChapterGellMann.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGellMann.lean

import Definitions.Def_ChapterParity
import Definitions.Def_ChapterYangMillsSU3
import Mathlib


/-!
# Chapter "Quantization due to time-evolution: Yang-Mills …", §"Pure SU(3) Yang-Mills
theory" — the concrete Gell-Mann generators satisfy the defining `SU(3)` relations

Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and Classical
Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (line ~7001), which opens
with the defining relations of the `SU(N)` generators

```
[T_a, T_b] = i f_{abc} T_c ,     tr(T_a T_b) = ½ δ_{ab}
```

`ChapterYangMillsSU3.lean` develops the structure-constant theory *abstractly*, from the
two relations as `Prop`-level hypotheses (`TraceOrthonormal`, `ClosesWithStructureConstants`).
`ChapterParity.lean` introduces the *concrete* Gell-Mann matrices `λ^a`
(`ChapterParity.gellMann`) and proves their complex-conjugation sign law.  This file closes
the gap by verifying that the concrete Gell-Mann matrices really are a system of `SU(3)`
generators: they are **Hermitian**, **traceless**, and **trace-orthonormal**, and the
rescaled generators `T_a = ½ λ^a` satisfy the book's normalization `tr(T_a T_b) = ½ δ_{ab}`
— i.e. they discharge the abstract `TraceOrthonormal` hypothesis of `ChapterYangMillsSU3`.

## Contents

* `gellMann_isHermitian` — `(λ^a)ᴴ = λ^a` (each generator is self-adjoint);
* `gellMann_trace_zero` — `tr(λ^a) = 0` (each generator is traceless, so `T_a ∈ su(3)`);
* `gellMann_trace_orthonormal` — `tr(λ^a λ^b) = 2 δ_{ab}` (the physics normalization of the
  Gell-Mann basis, including the `λ⁸` case where the `1/√3` normalization is essential);
* `su3gen` — the generators `T_a = ½ λ^a`, with `su3gen_isHermitian`, `su3gen_trace_zero`;
* `su3gen_traceOrthonormal` — **bridge**: `T_a = ½ λ^a` satisfies
  `YangMillsSU3.TraceOrthonormal`, i.e. `tr(T_a T_b) = ½ δ_{ab}`, so the concrete Gell-Mann
  system meets the abstract hypothesis used throughout `ChapterYangMillsSU3`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix

namespace BookProof.ChapterGellMann

open BookProof.ChapterParity







/-- The `SU(3)` generators in the physics normalization, `T_a = ½ λ^a`. -/
noncomputable def su3gen (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • gellMann a







end BookProof.ChapterGellMann


