-- Prove2me | Definitions.Def_ChapterKatoRellichDeficiencyCore
-- name    : ChapterKatoRellichDeficiencyCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-18T03:23:45.967931+00:00
-- url     : https://prove2.me/theorems/c1a95b1a-22ac-4553-8bf2-e98305938c39
-- title:
--   Bounded symmetric perturbations preserve essential self-adjointness
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.KatoRellichDeficiencyCore`, source chapter `BookProof/ChapterKatoRellichDeficiencyCore.lean`): Bounded symmetric perturbations preserve essential self-adjointness
--
--   This module proves the **Kato–Rellich theorem** in the special case of a *bounded* symmetric perturbation, in the deficiency-space formulation used throughout this project (`BookProof.FarisLavine.EssentiallySelfAdjointOn`):
--
--   > If `H` is symmetric on a domain `D` and essentially self-adjoint, and `B` is a bounded > everywhere-defined symmetric operator, then `H + B` is essentially self-adjoint on `D`.
--
--   No closure or spectral theory is needed. The proof is an explicit Neumann-series argument at the level of *finite* sums, which keeps every approximant inside the domain `D`:
--
--   * For a symmetric `H` one has `‖H x - e i x‖ ≥ |e| ‖x‖` (`FarisLavine.norm_sub_smul_sq`), so an approximate solution of `(H - e i) x = v` has controlled norm. * Given `y`, solve `(H - e i) v₀ ≈ y`, then `(H - e i) v₁ ≈ -B v₀`, and so on. The partial sums `Sₘ = v₀ + ⋯ + v_{m-1}` satisfy `(H + B - e i) Sₘ ≈ y - rₘ` where the residuals `rₘ` decay geometrically with ratio `‖B‖/|e| < 1`. * Hence the range of `H + B - e i` is dense whenever `|e| > ‖B‖`, and this gives vanishing deficiency spaces at `± e i`; the basic criterion `FarisLavine.deficiencyTrivialAt_of_dense_range` then propagates this to every non-real point, in particular to `± i`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterKatoRellichDeficiencyCore.lean

import Definitions.Def_ChapterFarisLavine
import Mathlib

/-!
# Bounded symmetric perturbations preserve essential self-adjointness

This module proves the **Kato–Rellich theorem** in the special case of a *bounded*
symmetric perturbation, in the deficiency-space formulation used throughout this
project (`BookProof.FarisLavine.EssentiallySelfAdjointOn`):

> If `H` is symmetric on a domain `D` and essentially self-adjoint, and `B` is a bounded
> everywhere-defined symmetric operator, then `H + B` is essentially self-adjoint on `D`.

No closure or spectral theory is needed.  The proof is an explicit Neumann-series
argument at the level of *finite* sums, which keeps every approximant inside the domain
`D`:

* For a symmetric `H` one has `‖H x - e i x‖ ≥ |e| ‖x‖` (`FarisLavine.norm_sub_smul_sq`),
  so an approximate solution of `(H - e i) x = v` has controlled norm.
* Given `y`, solve `(H - e i) v₀ ≈ y`, then `(H - e i) v₁ ≈ -B v₀`, and so on.  The
  partial sums `Sₘ = v₀ + ⋯ + v_{m-1}` satisfy `(H + B - e i) Sₘ ≈ y - rₘ` where the
  residuals `rₘ` decay geometrically with ratio `‖B‖/|e| < 1`.
* Hence the range of `H + B - e i` is dense whenever `|e| > ‖B‖`, and this gives
  vanishing deficiency spaces at `± e i`; the basic criterion
  `FarisLavine.deficiencyTrivialAt_of_dense_range` then propagates this to every
  non-real point, in particular to `± i`.
-/
namespace BookProof.KatoRellich

end BookProof.KatoRellich


