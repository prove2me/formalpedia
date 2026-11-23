-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:00.874881+00:00
-- url     : https://prove2.me/theorems/8164878f-eb1b-4d0a-8d5f-db0fd1d15414
-- title:
--   Dens Inf St
-- statement:
--   Definitions and structural lemmas for Dens Inf St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensInfSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
def SubmDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      DensAll μ f id ν {x | Function.Surjective (fderiv ℝ f x)}
def SubmLocal : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      ∀ x0, Function.Surjective (fderiv ℝ f x0) → ∃ N, IsOpen N ∧ x0 ∈ N ∧ DensAll μ f id ν N
def CoordInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
    (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
      gramR (Ainf F) σ J X) ∧
    ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X))
section Transport
variable {V X Y V' X' : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace V'] [MeasurableSpace V']
  [BorelSpace V'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']
end Transport
section Local
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]
end Local
end PI.VolStabW


