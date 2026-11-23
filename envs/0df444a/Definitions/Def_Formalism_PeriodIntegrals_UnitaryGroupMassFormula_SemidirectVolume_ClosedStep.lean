-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:26.936997+00:00
-- url     : https://prove2.me/theorems/5c57abcf-62b5-4ada-8e2f-068aacd5f66b
-- title:
--   Closed Step
-- statement:
--   Definitions and structural lemmas for Closed Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ClosedStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
def ratG {X : Type} [Group X] (Γ K : Subgroup X) : Subgroup K := (Γ ⊓ K).subgroupOf K
def LCSC (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  LocallyCompactSpace G ∧ SecondCountableTopology G ∧ T2Space G ∧ IsTopologicalGroup G
def DiscC {X : Type} [Group X] [TopologicalSpace X] (Γ K : Subgroup X) : Prop :=
  Countable (ratG Γ K) ∧ DiscreteTopology (ratG Γ K)
def Semi {X : Type} [Group X] [TopologicalSpace X] (K N H : Subgroup X) : Prop :=
  (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
    ∃ e : (N × H) ≃ₜ K, ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X)
def RatSemi {X : Type} [Group X] (Γ N H : Subgroup X) : Prop :=
  ∀ n ∈ N, ∀ h ∈ H, n * h ∈ Γ → h ∈ Γ
def ConjInv {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X] (N H : Subgroup X) : Prop :=
  ∀ μN : Measure N, μN.IsHaarMeasure → ∀ h ∈ H, ∀ f : X → ENNReal, Measurable f →
    ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μN = ∫⁻ n, f (n : X) ∂μN
def ProdF {X : Type} [Group X] [MeasurableSpace X] (K N H : Subgroup X)
    (μK : Measure K) (μN : Measure N) (μH : Measure H) : Prop :=
  ∀ f : X → ENNReal, Measurable f →
    ∫⁻ k, f (k : X) ∂μK = ∫⁻ m, ∫⁻ h, f ((m : X) * (h : X)) ∂μH ∂μN
def SubLCSC : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] (Γ K : Subgroup X), LCSC X → IsClosed (K : Set X) →
    Countable Γ → DiscreteTopology Γ → LCSC K ∧ DiscC Γ K
def FDExG : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (Γ K : Subgroup X),
    LCSC K → DiscC Γ K →
    ∃ 𝓕 : Set K, MeasurableSet 𝓕 ∧ ∀ μ : Measure K, IsFundamentalDomain (ratG Γ K) 𝓕 μ
def ProdHaarG : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (K N H : Subgroup X), Semi K N H → LCSC K → LCSC N → LCSC H → ConjInv N H →
    ∀ μN : Measure N, μN.IsHaarMeasure → ∀ μH : Measure H, μH.IsHaarMeasure →
    ∃ μK : Measure K, μK.IsHaarMeasure ∧ ProdF K N H μK μN μH
def VolG : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (Γ K N H : Subgroup X), Semi K N H → RatSemi Γ N H → LCSC K → LCSC N → LCSC H →
    DiscC Γ K → DiscC Γ N → DiscC Γ H →
    ∀ (μK : Measure K) (μN : Measure N) (μH : Measure H),
    μK.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure → ProdF K N H μK μN μH →
    ∀ (𝓕 : Set K) (𝓕N : Set N) (𝓕H : Set H), IsFundamentalDomain (ratG Γ K) 𝓕 μK →
      IsFundamentalDomain (ratG Γ N) 𝓕N μN → IsFundamentalDomain (ratG Γ H) 𝓕H μH →
      μK 𝓕 = μN 𝓕N * μH 𝓕H
def LcscHA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    LCSC (HA (AF F) σ J)
def DiscHA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J)
def ClosedStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    IsClosed (S0 (AF F) σ J P : Set (HA (AF F) σ J)) ∧
      IsClosed (FrameUnipotentSubgroup (AF F) σ J P : Set (HA (AF F) σ J)) ∧
      IsClosed (Hsub (AF F) σ J P : Set (HA (AF F) σ J))
def SemiStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    Semi (S0 (AF F) σ J P) (FrameUnipotentSubgroup (AF F) σ J P) (Hsub (AF F) σ J P) ∧
      RatSemi (HFinIn (AF F) σ J) (FrameUnipotentSubgroup (AF F) σ J P) (Hsub (AF F) σ J P)
def ConjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ConjInv (FrameUnipotentSubgroup (AF F) σ J P) (Hsub (AF F) σ J P)
def TensTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧
      LocallyCompactSpace (AF F ⊗[F] E) ∧ SecondCountableTopology (AF F ⊗[F] E)
end PI.VolSemiDirect.W


