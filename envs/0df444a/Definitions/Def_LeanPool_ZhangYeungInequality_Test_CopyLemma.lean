-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Test_CopyLemma
-- name    : LeanPool_ZhangYeungInequality_Test_CopyLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:17:04.891494+00:00
-- url     : https://prove2.me/theorems/2b611bba-6ebe-4f1d-87ff-751d9add0c0e
-- title:
--   Copy Lemma
-- statement:
--   Definitions and structural lemmas for Copy Lemma, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Test/CopyLemma.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_identity_Y__c9ae01529d93
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_transport_X_to_X__38bc3900b8ed
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
public import Theorems.Thm_ZhangYeung_copyLemma
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ZhangYeung_delta_of_condMI_vanishes_eq

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeungTest
open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR
universe u
section Signature
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν :=
  copyLemma hX hY hZ hU μ
end Signature
section LemmaTwoFormA
variable {Ω : Type*} [MeasurableSpace Ω]
  {α β γ δ : Type*}
  [Finite α] [Finite β] [Finite γ] [Finite δ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
example
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D|⟨B, C⟩;ν] = 0) :
    delta B C A D ν
      = I[A : D; ν] - I[A : D|B;ν] - I[A : D|C;ν]
        - I[B : C|⟨A, D⟩;ν] :=
  delta_of_condMI_vanishes_eq hA hB hC hD ν hVanish
end LemmaTwoFormA
section Consequences
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
example
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' Y₁ ν
      = I[X' : Y₁; ν] - I[X' : Y₁|Z';ν] - I[X' : Y₁|U';ν]
        - I[Z' : U'|⟨X', Y₁⟩;ν] :=
  copyLemma_delta_identity_Y₁ hX' hY₁ hZ' hU' hCond
example
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' X₁ ν
      = I[X' : X₁; ν] - I[X' : X₁|Z';ν] - I[X' : X₁|U';ν]
        - I[Z' : U'|⟨X', X₁⟩;ν] :=
  copyLemma_delta_identity_X_X₁ hX' hX₁ hZ' hU' hCond
example
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X Y μ = delta Z' U' X' Y₁ ν :=
  copyLemma_delta_transport_Y_to_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond
example
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X X μ = delta Z' U' X' X₁ ν :=
  copyLemma_delta_transport_X_to_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond
example
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z U X Y μ ≤ I[X' : Y₁; ν] :=
  copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond
example
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[Z : U; μ] - 2 * I[Z : U|X;μ] ≤ I[X' : X₁; ν] :=
  copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond
end Consequences
section DownstreamUsage
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → Fin 2) (Y₁ : Ω' → Fin 2),
      IsProbabilityMeasure ν ∧ delta Z U X Y μ ≤ I[X' : Y₁; ν] := by
  obtain ⟨Ω', _, ν, X', _, _, Y₁, Z', U',
      hν, hX', hY', hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  exact ⟨Ω', _, ν, X', Y₁, hν,
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond⟩
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → Fin 2) (X₁ : Ω' → Fin 2) (Y₁ : Ω' → Fin 2),
      2 * I[Z : U; μ] - 3 * I[Z : U|X;μ] - I[Z : U|Y;μ]
        ≤ I[X' : Y₁; ν] + I[X' : X₁; ν] := by
  obtain ⟨Ω', _, ν, X', _, X₁, Y₁, Z', U',
      hν, hX', hY', hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  refine ⟨Ω', _, ν, X', X₁, Y₁, ?_⟩
  have h1 : delta Z U X Y μ ≤ I[X' : Y₁; ν] :=
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond
  have h2 : I[Z : U; μ] - 2 * I[Z : U|X;μ] ≤ I[X' : X₁; ν] :=
    copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond
  rw [delta_def] at h1
  linarith
end DownstreamUsage
end ZhangYeungTest


