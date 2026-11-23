-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:41.411401+00:00
-- url     : https://prove2.me/theorems/2c12a078-2811-4aaa-896d-ef8cce53a801
-- title:
--   Pos Near
-- statement:
--   Definitions and structural lemmas for Pos Near, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/PosNear.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
namespace PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
section Coord
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k
variable [FiniteDimensional F E]
end Coord
section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
end Loc
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
end Main
end PositiveNearLattice
open PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
def TestNear : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∃ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) ∧ IsAdm F E (fun X => (φ X : ℂ)) ∧
    ∃ U : Set (HA (AF F) σ J), IsOpen U ∧ U.Nonempty ∧
      ∀ g ∈ U, 0 < φ (g • ratTup (AF F) X0)
end PI.VolStabSW


