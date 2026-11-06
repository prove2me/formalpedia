-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
-- name    : QEC_Coding_Stabilizer_FixedGeneratorInteraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:47:18.071728+00:00
-- url     : https://prove2.me/theorems/77bf35ff-9a77-4d43-9623-32d7e6b8a7c9
-- title:
--   Fixed Generator Interaction
-- statement:
--   Definitions and structural lemmas for Fixed Generator Interaction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
set_option autoImplicit false
namespace QEC
namespace Coding
namespace StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def fixedGeneratorInteractionOf (generators : κ → Binary ι) (p q : ι) : Prop :=
  p ≠ q ∧ ∃ j : κ, p ∈ support (generators j) ∧ q ∈ support (generators j)
def fixedGeneratorInteractionGraphOf (generators : κ → Binary ι) :
    Locality.ConnectivityGraph ι where
  adjacent := fixedGeneratorInteractionOf generators
  symmetric := by
    intro p q h
    rcases h with ⟨hpq, j, hp, hq⟩
    exact ⟨hpq.symm, j, hq, hp⟩
  loopless := by
    intro p h
    exact h.1 rfl
namespace BinaryStabilizerPresentation
def fixedGeneratorInteraction (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (p q : ι) : Prop :=
  p ≠ q ∧ ∃ j : κ, p ∈ P.generatorSupport j ∧ q ∈ P.generatorSupport j
def fixedGeneratorInteractionGraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Locality.ConnectivityGraph ι where
  adjacent := P.fixedGeneratorInteraction
  symmetric := by
    intro p q h
    rcases h with ⟨hpq, j, hp, hq⟩
    exact ⟨Ne.symm hpq, j, hq, hp⟩
  loopless := by
    intro p h
    exact h.1 rfl
def fixedGeneratorOuterBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) : Set ι :=
  {q | q ∉ A ∧ ∃ p : ι, p ∈ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q}
def fixedGeneratorInnerBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) : Set ι :=
  {p | p ∈ A ∧ ∃ q : ι, q ∉ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q}
def fixedGeneratorNoCrossEdge
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) : Prop :=
  ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B →
    ¬ P.fixedGeneratorInteractionGraph.adjacent p q
def fixedGeneratorDecoupled
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) : Prop :=
  Disjoint A B ∧ P.fixedGeneratorNoCrossEdge A B
end BinaryStabilizerPresentation
end StabilizerCode
end Coding
end QEC


