-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:32.432247+00:00
-- url     : https://prove2.me/theorems/a720515e-a8cd-43b6-8f97-1b28c9f2618f
-- title:
--   Tens All
-- statement:
--   Definitions and structural lemmas for Tens All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensAll.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
namespace TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2
section Top
variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]
end Top
end TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW
end PI.VolStabW


