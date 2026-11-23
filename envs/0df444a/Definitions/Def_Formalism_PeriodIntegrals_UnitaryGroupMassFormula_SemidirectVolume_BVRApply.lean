-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_BVRApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_BVRApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:27.687775+00:00
-- url     : https://prove2.me/theorems/043fb527-6cbf-4210-98c9-186a2e648b21
-- title:
--   BVRApply
-- statement:
--   Definitions and structural lemmas for BVRApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/BVRApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct Matrix
section Bases
variable (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (M : ℕ)
  (A : Type) [CommRing A] [Algebra F A]
def bV : Module.Basis (Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) F (Fin M → E) :=
  (Pi.basis fun _ : Fin M => Module.finBasis F E).reindex (Fintype.equivFin _)
def bVR : Module.Basis (Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) A
    (Fin M → A ⊗[F] E) :=
  (Pi.basis fun _ : Fin M => Algebra.TensorProduct.basis A (Module.finBasis F E)).reindex
    (Fintype.equivFin _)
end Bases
end PI.VolSemiDirect.W.Cj


