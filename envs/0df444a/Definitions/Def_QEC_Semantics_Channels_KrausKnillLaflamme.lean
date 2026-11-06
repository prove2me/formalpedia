-- Prove2me | Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
-- name    : QEC_Semantics_Channels_KrausKnillLaflamme
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:33:50.00352+00:00
-- url     : https://prove2.me/theorems/f9e09057-0e5e-4902-a7ea-2b2b3df25748
-- title:
--   Kraus Knill Laflamme
-- statement:
--   Definitions and structural lemmas for Kraus Knill Laflamme, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_mem_sameSpaceErrorSet_iff

set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
def IndexedKnillLaflammeConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) : Prop :=
  ∀ i j : ι,
    ∀ x : H, x ∈ C.carrier →
      ∀ y : H, y ∈ C.carrier →
        inner Complex (E.operator i x) (E.operator j y) =
          scalar i j * inner Complex x y
def IndexedKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) : Prop :=
  ∃ scalar : ι → ι → Complex,
    IndexedKnillLaflammeConditionWithScalar E C scalar
def errorImageSubspace
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (i : ι) :
    Submodule Complex H :=
  C.carrier.map (E.operator i)
def IndexedKnillLaflammeProjectorConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) : Prop :=
  ∀ i j : ι,
    (C.projector.comp ((LinearMap.adjoint (E.operator i)).comp (E.operator j))).comp
        C.projector =
      scalar i j • C.projector
def IndexedKnillLaflammeProjectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) : Prop :=
  ∃ scalar : ι → ι → Complex,
    IndexedKnillLaflammeProjectorConditionWithScalar E C scalar
noncomputable def sameSpaceScalar
    (E : FiniteKrausFamily ι H H) (scalar : ι → ι → Complex) :
    Operator H → Operator H → Complex := by
  classical
  exact fun A B =>
    if hA : A ∈ E.sameSpaceErrorSet then
      if hB : B ∈ E.sameSpaceErrorSet then
        scalar
          (Classical.choose ((E.mem_sameSpaceErrorSet_iff A).1 hA))
          (Classical.choose ((E.mem_sameSpaceErrorSet_iff B).1 hB))
      else 0
    else 0
end FiniteKrausFamily
end
end Semantics
end QEC


