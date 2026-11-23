-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:52.821772+00:00
-- url     : https://prove2.me/theorems/d9118438-1ba2-43a8-88df-d892ac738d7f
-- title:
--   Cube Cut Regular Sequence
-- statement:
--   Definitions and structural lemmas for Cube Cut Regular Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
namespace GlobalTheory
namespace CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
def ExactMod (A : Cube.{0} I K) (J : ∀ s, Submodule K (A.obj s)) : Prop :=
  (∀ x : Cube.Term A 0, (∀ s, Cube.d A 0 x s ∈ J s.1) → ∀ s, x s ∈ J s.1) ∧
    ∀ (p : ℕ) (x : Cube.Term A (p + 1)), (∀ s, Cube.d A (p + 1) x s ∈ J s.1) →
      ∃ y : Cube.Term A p, ∀ s, (x - Cube.d A p y) s ∈ J s.1
section Family
variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))
abbrev imSum (k : ℕ) (s : Finset I) : Submodule K (B.obj s) :=
  ⨆ (j : Fin g) (_ : (j : ℕ) < k), LinearMap.range ((φ j).app s).hom
end Family
end CubeCut
end GlobalTheory


