-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
-- name    : GroundTheory_PAdicHodge_CompletedAlgClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:40.47307+00:00
-- url     : https://prove2.me/theorems/6f53e298-90f7-4a24-93a0-e43ff7bdccaf
-- title:
--   Completed Alg Closure
-- statement:
--   Definitions and structural lemmas for Completed Alg Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CompletedAlgClosure.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
def SpectralAlgClosure : Type _ := AlgebraicClosure K
namespace SpectralAlgClosure
instance : Field (SpectralAlgClosure K) := inferInstanceAs (Field (AlgebraicClosure K))
instance : Algebra K (SpectralAlgClosure K) := inferInstanceAs (Algebra K (AlgebraicClosure K))
instance : IsAlgClosed (SpectralAlgClosure K) := inferInstanceAs (IsAlgClosed (AlgebraicClosure K))
instance : Algebra.IsAlgebraic K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra.IsAlgebraic K (AlgebraicClosure K))
instance : NormedField (SpectralAlgClosure K) := spectralNorm.normedField K (SpectralAlgClosure K)
instance : NormedAlgebra K (SpectralAlgClosure K) :=
  spectralNorm.normedAlgebra K (SpectralAlgClosure K)
instance : IsUltrametricDist (SpectralAlgClosure K) := IsUltrametricDist.of_normedAlgebra K
end SpectralAlgClosure
abbrev CompletedAlgClosure : Type _ := UniformSpace.Completion (SpectralAlgClosure K)
namespace CompletedAlgClosure
instance : IsUltrametricDist (CompletedAlgClosure K) := IsUltrametricDist.of_normedAlgebra K
instance : NontriviallyNormedField (CompletedAlgClosure K) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨algebraMap K _ x, by rw [norm_algebraMap']; exact hx⟩
instance [CharZero K] : IsAlgClosed (CompletedAlgClosure K) := by
  have : CharZero (CompletedAlgClosure K) :=
    (RingHom.charZero_iff (algebraMap K (CompletedAlgClosure K)).injective).mp inferInstance
  exact IsAlgClosed.of_denseRange (K := SpectralAlgClosure K) UniformSpace.Completion.denseRange_coe
variable (L : Type*) [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
def embedding : L →ₐ[K] CompletedAlgClosure K :=
  (IsScalarTower.toAlgHom K (SpectralAlgClosure K) (CompletedAlgClosure K)).comp
    (IsAlgClosed.lift : L →ₐ[K] SpectralAlgClosure K)
end CompletedAlgClosure
end GroundTheory.PAdicHodge


