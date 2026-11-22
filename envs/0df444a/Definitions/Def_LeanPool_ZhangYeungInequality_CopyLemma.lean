-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
-- name    : LeanPool_ZhangYeungInequality_CopyLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:51:54.509806+00:00
-- url     : https://prove2.me/theorems/0decb99f-3cae-4319-9fff-2d7e127a4993
-- title:
--   Copy Lemma
-- statement:
--   Definitions and structural lemmas for Copy Lemma, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
section Consequences
def projZUA {S₁ S₂ S₃ S₄ : Type*} (p : S₁ × S₂ × S₃ × S₄) :
  S₃ × S₄ × S₁ :=
  (p.2.2.1, p.2.2.2, p.1)
def projZUB {S₁ S₂ S₃ S₄ : Type*} (p : S₁ × S₂ × S₃ × S₄) :
  S₃ × S₄ × S₂ :=
  (p.2.2.1, p.2.2.2, p.2.1)
section TripleIdentDistribs
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω}
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'}
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
end TripleIdentDistribs
section Finite
variable {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
end Finite
section Transport
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
end Transport
end Consequences
end ZhangYeung


