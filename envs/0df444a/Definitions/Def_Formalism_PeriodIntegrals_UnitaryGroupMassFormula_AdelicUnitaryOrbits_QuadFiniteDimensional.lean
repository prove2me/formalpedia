-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:00.621038+00:00
-- url     : https://prove2.me/theorems/b7bf846c-bb56-44fc-9dad-697d7a58df30
-- title:
--   Quad Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Quad Finite Dimensional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
section Field
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
def quadBasis (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ]) :
    Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
end Field
section Ring
variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]
def quadBasisR : Module.Basis (Fin 2) R (R ⊗[F] E) :=
  Algebra.TensorProduct.basis R (quadBasis h2 hli)
end Ring
end PIW.AdelicOrbitU


