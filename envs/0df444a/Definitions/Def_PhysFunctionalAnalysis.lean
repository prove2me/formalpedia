-- Prove2me | Definitions.Def_PhysFunctionalAnalysis
-- name    : PhysFunctionalAnalysis
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T18:45:03.351751+00:00
-- url     : https://prove2.me/theorems/a1b3dbf4-27c6-4768-b76a-455d2f794302
-- title:
--   Chapter PhysFunctionalAnalysis
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/PhysFunctionalAnalysis.lean`): generated def bundle for PhysFunctionalAnalysis. See BookProof/PhysFunctionalAnalysis.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/PhysFunctionalAnalysis.lean

import Definitions.Def_PhysMeasureBasis
import Mathlib


/-!
# Part 3: Function space (H1–H7)

Separability of `L²`, non-separability of `L^∞`, existence of the
wave-function `√p`, the Hilbert-space classification surrogate for the
Fock–Guichardet isomorphism, and an atomless probability measure on the unit
sphere.
-/

open MeasureTheory Set
open scoped ENNReal lp

noncomputable section

namespace PhysFunctionalAnalysis

open PhysMeasureBasis

/-! ### H1. `L²([0,1])` is separable -/

instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩



/-! ### H2. `L^∞([0,1])` is NOT separable -/



/-! ### H3. Wave-functions exist: `Ψ = √p` -/





/-! ### H5. Polynomials are dense in `L²([0,1])` -/



/-! ### H6. All infinite-dimensional separable real Hilbert spaces are
isometrically isomorphic -/

/-
A uniformly separated family in a separable (pseudo)metric space is indexed
    by a countable type.
-/


/-
A separable infinite-dimensional real Hilbert space is isometric to
    `ℓ²(ℕ, ℝ)`.
-/




/-! ### H7. An atomless Borel probability measure on the unit sphere -/



end PhysFunctionalAnalysis


