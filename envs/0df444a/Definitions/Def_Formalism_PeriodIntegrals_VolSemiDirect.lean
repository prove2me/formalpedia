-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
-- name    : Formalism_PeriodIntegrals_VolSemiDirect
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:44.763443+00:00
-- url     : https://prove2.me/theorems/36540f6c-33eb-4315-bea5-cb1598384cc2
-- title:
--   Vol Semi Direct
-- statement:
--   Definitions and structural lemmas for Vol Semi Direct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/VolSemiDirect.lean

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
namespace PI.VolSemiDirect
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def ratIn (K : Subgroup (HA (AF F) σ J)) : Subgroup K :=
  ((HFinIn (AF F) σ J) ⊓ K).subgroupOf K
def IsProdNH {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] (K N H : Subgroup (HA R σ J))
    (μK : Measure K) (μN : Measure N) (μH : Measure H) : Prop :=
  ∀ f : HA R σ J → ENNReal, Measurable f →
    ∫⁻ k, f (k : HA R σ J) ∂μK = ∫⁻ m, ∫⁻ h, f ((m : HA R σ J) * (h : HA R σ J)) ∂μH ∂μN
def VolumeUnipotent : Prop :=
  IsHermND σ J → ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ μN : Measure (FrameUnipotentSubgroup (AF F) σ J P), μN.IsHaarMeasure →
    ∀ μH : Measure (Hsub (AF F) σ J P), μH.IsHaarMeasure →
    AllSome (fun μS : Measure (S0 (AF F) σ J P) => μS.IsHaarMeasure ∧
      IsProdNH F E σ M J (S0 (AF F) σ J P) (FrameUnipotentSubgroup (AF F) σ J P) (Hsub (AF F) σ J P) μS μN μH)
      fun μS =>
    AllSome (fun 𝓕 : Set (S0 (AF F) σ J P) =>
      IsFundamentalDomain (ratIn F E σ M J (S0 (AF F) σ J P)) 𝓕 μS) fun 𝓕 =>
    AllSome (fun 𝓕N : Set (FrameUnipotentSubgroup (AF F) σ J P) =>
      IsFundamentalDomain (ratIn F E σ M J (FrameUnipotentSubgroup (AF F) σ J P)) 𝓕N μN) fun 𝓕N =>
    AllSome (fun 𝓕H : Set (Hsub (AF F) σ J P) =>
      IsFundamentalDomain (ratIn F E σ M J (Hsub (AF F) σ J P)) 𝓕H μH) fun 𝓕H =>
      μS 𝓕 = μN 𝓕N * μH 𝓕H
end Ext
def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J
def VolumeUnipotentAllCM : Prop := ForAllCM fun F E _ _ _ _ σ M J => VolumeUnipotent F E σ M J
end PI.VolSemiDirect


