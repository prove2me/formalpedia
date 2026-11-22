-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
-- name    : LeanPool_NemytskiiLebesgue_IntegralFunctional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:35:01.953286+00:00
-- url     : https://prove2.me/theorems/420216b3-16ac-4636-9b89-2a0202aed3ab
-- title:
--   Integral Functional
-- statement:
--   Definitions and structural lemmas for Integral Functional, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_comp_continuous

set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
@[expose] noncomputable def outR1 {Ω : Type*} {m : ℕ} (f : Ω → ℝ^m → ℝ) :
    Ω → ℝ^m → ℝ^1 :=
  (realLIE <| f · ·)
@[expose] noncomputable def outR1nested {Ω : Type*} {m : ℕ} (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) :
    Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^1) :=
  (realLIE.toContinuousLinearMap.comp <| f' · ·)
lemma IsCaratheodory.outR1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ) :
    IsCaratheodory (NemytskiiLebesgue.outR1 f) μ :=
  hf.comp_continuous realLIE.continuous
lemma IsCaratheodory.outR1nested
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ) :
    IsCaratheodory (NemytskiiLebesgue.outR1nested f') μ :=
  hf'.comp_continuous (by fun_prop)
end NemytskiiLebesgue


