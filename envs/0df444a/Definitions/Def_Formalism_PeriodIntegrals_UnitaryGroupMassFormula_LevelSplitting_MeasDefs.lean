-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:49.608039+00:00
-- url     : https://prove2.me/theorems/d7f2314f-49eb-4bd4-bb7b-144a8903103c
-- title:
--   Meas Defs
-- statement:
--   Definitions and structural lemmas for Meas Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.Meas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
def PlacesCountable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Countable (HeightOneSpectrum (𝓞 F))
def ContPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)),
    Continuous (fun g : HA (Af F) σ J =>
      ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))
def LatBorel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)),
    MeasurableSet[borel (Fin n → Fv F v ⊗[F] E)] (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))
end PI.LevelKSplit.W.Meas


