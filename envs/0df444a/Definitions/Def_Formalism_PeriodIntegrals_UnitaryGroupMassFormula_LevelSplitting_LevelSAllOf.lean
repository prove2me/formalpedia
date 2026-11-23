-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:56.523484+00:00
-- url     : https://prove2.me/theorems/67b6bf39-8fcd-4f7d-909b-b641cb0c4c8c
-- title:
--   Level SAll Of
-- statement:
--   Definitions and structural lemmas for Level SAll Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelKSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def SplitK : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ ΛX ΛW ΛY : Set (Fin M → E), Adapted F E σ M J P ΛX ΛW ΛY →
    ∀ m h : HA (Af F) σ J, m ∈ Nsub (Af F) σ J P → h ∈ Hsub (Af F) σ J P →
      m * h ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY) → h ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
end Ext
section ExtN
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def ExistS : Prop :=
  ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ μN : Measure (Nsub (Af F) σ J P), μN.IsHaarMeasure →
    ∀ μH : Measure (Hsub (Af F) σ J P), μH.IsHaarMeasure →
    ∃ μS : Measure (Ssub (Af F) σ J P), μS.IsHaarMeasure ∧
      IsProdNH F E σ M J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) μS μN μH
def MeasKf : Prop :=
  ∀ Λ : Set (Fin M → E), MeasurableSet (Kf σ J Λ : Set (HA (Af F) σ J))
variable {F E σ M J}
end ExtN
def ExistSAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ExistS F E σ M J
def MeasKfAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      MeasKf F E σ M J
def SplitKAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SplitK F E σ M J
end PI.LevelKSplit.W


