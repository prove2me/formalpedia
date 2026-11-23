-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LevelKSplit
-- name    : Formalism_PeriodIntegrals_LevelKSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:46.771804+00:00
-- url     : https://prove2.me/theorems/4d8f9f70-287a-4561-af6e-49c8489c5fdd
-- title:
--   Level KSplit
-- statement:
--   Definitions and structural lemmas for Level KSplit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LevelKSplit.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def IsProdNH {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] (K N H : Subgroup (HA R σ J))
    (μK : Measure K) (μN : Measure N) (μH : Measure H) : Prop :=
  ∀ f : HA R σ J → ENNReal, Measurable f →
    ∫⁻ k, f (k : HA R σ J) ∂μK = ∫⁻ m, ∫⁻ h, f ((m : HA R σ J) * (h : HA R σ J)) ∂μH ∂μN
def Adapted {r : ℕ} (P : Frame E M r) (ΛX ΛW ΛY : Set (Fin M → E)) : Prop :=
  (∀ x ∈ ΛX, x ∈ Submodule.span E (Set.range P.e)) ∧
  (∀ y ∈ ΛY, y ∈ Submodule.span E (Set.range P.f)) ∧
  (∀ w ∈ ΛW, ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0)
def LevelS : Prop :=
  IsHermND σ J → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ ΛX ΛW ΛY : Set (Fin M → E), Adapted F E σ M J P ΛX ΛW ΛY →
    ∀ μN : Measure (Nsub (Af F) σ J P), μN.IsHaarMeasure →
    ∀ μH : Measure (Hsub (Af F) σ J P), μH.IsHaarMeasure →
    AllSome (fun μS : Measure (Ssub (Af F) σ J P) => μS.IsHaarMeasure ∧
      IsProdNH F E σ M J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) μS μN μH)
      fun μS =>
      μS {s | (s : HA (Af F) σ J) ∈ KS σ J P (ΛX ∪ ΛW ∪ ΛY)} =
        μN {m | (m : HA (Af F) σ J) ∈ NO σ J P (ΛX ∪ ΛW ∪ ΛY)} *
        μH {h | (h : HA (Af F) σ J) ∈ KH σ J P (ΛX ∪ ΛW ∪ ΛY)}
end Ext
def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J
def LevelSAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => LevelS F E σ M J
end PI.LevelKSplit


