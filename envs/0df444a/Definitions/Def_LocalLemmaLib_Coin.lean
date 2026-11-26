-- Prove2me | Definitions.Def_LocalLemmaLib_Coin
-- name    : LocalLemmaLib_Coin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:19:54.520217+00:00
-- url     : https://prove2.me/theorems/4bcaa6fc-2ac4-5b40-8927-18ae08da468b
-- title:
--   Coin
-- statement:
--   Definitions and structural lemmas for Coin, from Juan Pablo Traverso Gianini (jtraverso/lovasz-local-lemma; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Lovasz Local Lemma and two applications development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace LocalLemma
noncomputable def coinMeasure (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi fun _ => (PMF.uniformOfFintype Bool).toMeasure
instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (coinMeasure ι) := by
  unfold coinMeasure; infer_instance
def CoordDep {ι : Type*} (A : Set (ι → Bool)) (D : Finset ι) : Prop :=
  ∀ ω ω' : ι → Bool, (∀ i ∈ D, ω i = ω' i) → ω ∈ A → ω' ∈ A
end LocalLemma


