-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:56.237858+00:00
-- url     : https://prove2.me/theorems/efeec154-4891-4f2f-9644-1c239abc320e
-- title:
--   Fe Is Field
-- statement:
--   Definitions and structural lemmas for Fe Is Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FeIsField.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
def Th (e : Matrix (Fin N) (Fin N) k) : Module.End k (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun f := LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e)
  map_add' f g := by rw [← map_add]; congr 1
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; congr 1
variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)
abbrev Fe : Subalgebra k (Module.End k (Wd e)) := (rho hA he).range
end PositivityTheory.RgUd.TP.Desc.Piece.PDich


