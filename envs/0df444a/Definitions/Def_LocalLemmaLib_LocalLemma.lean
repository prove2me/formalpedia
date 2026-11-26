-- Prove2me | Definitions.Def_LocalLemmaLib_LocalLemma
-- name    : LocalLemmaLib_LocalLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:20:17.900044+00:00
-- url     : https://prove2.me/theorems/31a235a4-e7a5-5c34-8dad-b8475d7c46cc
-- title:
--   Local Lemma
-- statement:
--   Definitions and structural lemmas for Local Lemma, from Juan Pablo Traverso Gianini (jtraverso/lovasz-local-lemma; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Lovasz Local Lemma and two applications development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace LocalLemma
def IsDependencyGraph {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) (Γ : SimpleGraph (Fin n)) : Prop :=
  ∀ i, Indep (MeasurableSpace.generateFrom {A i})
    (MeasurableSpace.generateFrom {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j}) μ
def avoid {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (S : Finset (Fin n)) : Set Ω :=
  ⋂ j ∈ S, (A j)ᶜ
end LocalLemma


