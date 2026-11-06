-- Prove2me | Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
-- name    : QEC_Bounds_GeometricLocalityTradeoff_Model
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:27:38.976667+00:00
-- url     : https://prove2.me/theorems/efef3d45-0077-452f-b13c-26575ccd0577
-- title:
--   Model
-- statement:
--   Definitions and structural lemmas for Model, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_idempotent
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators
universe u v
structure BPTSquareLattice where
  rows : Nat
  columns : Nat
  rows_positive : 0 < rows
  columns_positive : 0 < columns
namespace BPTSquareLattice
abbrev Site (L : BPTSquareLattice) : Type := Fin L.rows × Fin L.columns
def siteCount (L : BPTSquareLattice) : Nat := Fintype.card L.Site
def square (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat) : Finset L.Site :=
  Finset.univ.filter fun site =>
    origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + width ∧
      origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + width
@[simp]
theorem mem_square_iff (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat)
    (site : L.Site) :
    site ∈ L.square origin width ↔
      origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + width ∧
        origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + width := by
  simp [square]
end BPTSquareLattice
structure BPTQuditLattice where
  lattice : BPTSquareLattice
  localDimension : lattice.Site → Nat
  localDimension_positive : ∀ site, 0 < localDimension site
  uniformDimensionBound : Nat
  uniformDimensionBound_positive : 0 < uniformDimensionBound
  localDimension_le_uniform : ∀ site, localDimension site ≤ uniformDimensionBound
namespace BPTQuditLattice
abbrev Site (L : BPTQuditLattice) : Type := L.lattice.Site
abbrev Register (L : BPTQuditLattice) : Type :=
  Semantics.Qudit.QuditRegister L.localDimension
def subsystem (L : BPTQuditLattice) (region : Finset L.Site) :
    Semantics.QuditSubsystem L.localDimension where
  selected := region
@[simp]
theorem subsystem_selected (L : BPTQuditLattice) (region : Finset L.Site) :
    (L.subsystem region).selected = region :=
  rfl
@[simp]
theorem mem_subsystem_selected_iff (L : BPTQuditLattice) (region : Finset L.Site)
    (site : L.Site) :
    site ∈ (L.subsystem region).selected ↔ site ∈ region :=
  Iff.rfl
noncomputable def erasureChannel (L : BPTQuditLattice) (region : Finset L.Site) :
    Semantics.QuantumChannel L.Register (L.subsystem region).complementSystem :=
  (L.subsystem region).erasureChannelFromRegister
end BPTQuditLattice
structure BPTCommutingProjectorModel (L : BPTQuditLattice) (κ : Type v) [Fintype κ] where
  interactionRange : Nat
  interactionRange_positive : 0 < interactionRange
  support : κ → Finset L.Site
  squareOrigin : κ → Nat × Nat
  support_subset_square : ∀ check,
    support check ⊆ L.lattice.square (squareOrigin check) interactionRange
  localProjector : (check : κ) →
    Semantics.Operator (L.subsystem (support check)).selectedSystem
  projector_idempotent : ∀ check,
    ((L.subsystem (support check)).extendLocalToRegister (localProjector check)).comp
        ((L.subsystem (support check)).extendLocalToRegister (localProjector check)) =
      (L.subsystem (support check)).extendLocalToRegister (localProjector check)
  projector_self_adjoint : ∀ check,
    LinearMap.adjoint
        ((L.subsystem (support check)).extendLocalToRegister (localProjector check)) =
      (L.subsystem (support check)).extendLocalToRegister (localProjector check)
  projector_commutes : ∀ check other,
    ((L.subsystem (support check)).extendLocalToRegister (localProjector check)).comp
        ((L.subsystem (support other)).extendLocalToRegister (localProjector other)) =
      ((L.subsystem (support other)).extendLocalToRegister (localProjector other)).comp
        ((L.subsystem (support check)).extendLocalToRegister (localProjector check))
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]
noncomputable def projector (M : BPTCommutingProjectorModel L κ) (check : κ) :
    Semantics.Operator L.Register :=
  (L.subsystem (M.support check)).extendLocalToRegister (M.localProjector check)
theorem projector_commute (M : BPTCommutingProjectorModel L κ) (check other : κ) :
    Commute (M.projector check) (M.projector other) := by
  change (M.projector check).comp (M.projector other) =
    (M.projector other).comp (M.projector check)
  exact M.projector_commutes check other
theorem projector_pairwise_commute (M : BPTCommutingProjectorModel L κ)
    (checks : Finset κ) :
    (checks : Set κ).Pairwise (Function.onFun Commute M.projector) := by
  intro check _ other _ _
  exact M.projector_commute check other
noncomputable def projectorProduct (M : BPTCommutingProjectorModel L κ) :
    Semantics.Operator L.Register :=
  Finset.univ.noncommProd M.projector (M.projector_pairwise_commute Finset.univ)
def commonFixedSubmodule (M : BPTCommutingProjectorModel L κ) : Submodule Complex L.Register where
  carrier := {vector | ∀ check, M.projector check vector = vector}
  zero_mem' := by
    intro check
    exact (M.projector check).map_zero
  add_mem' := by
    intro left right hleft hright check
    simp [map_add, hleft check, hright check]
  smul_mem' := by
    intro scalar vector hvector check
    simp [map_smul, hvector check]
def codeSpace (M : BPTCommutingProjectorModel L κ) : Semantics.QuantumCode L.Register where
  carrier := M.commonFixedSubmodule
noncomputable def fullCodeProjector (M : BPTCommutingProjectorModel L κ) :
    Semantics.Operator L.Register :=
  M.codeSpace.projector
structure EncodedQubitParameter (M : BPTCommutingProjectorModel L κ) where
  encodedQubits : Nat
  codeDimension_eq_two_pow : M.codeSpace.dimension = 2 ^ encodedQubits
def supportCouples (M : BPTCommutingProjectorModel L κ) (check : κ)
    (region : Finset L.Site) : Prop :=
  ((M.support check) ∩ region).Nonempty ∧ ((M.support check) \ region).Nonempty
noncomputable def boundary (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Finset L.Site :=
  (Finset.univ.filter fun check => M.supportCouples check region).biUnion M.support
noncomputable def internalBoundary (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Finset L.Site :=
  M.boundary region ∩ region
noncomputable def externalBoundary (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Finset L.Site :=
  M.boundary region \ region
def regionSubsystem (_M : BPTCommutingProjectorModel L κ) (region : Finset L.Site) :
    Semantics.QuditSubsystem L.localDimension :=
  L.subsystem region
noncomputable def regionErasureChannel (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    Semantics.QuantumChannel L.Register (M.regionSubsystem region).complementSystem :=
  (M.regionSubsystem region).erasureChannelFromRegister
end BPTCommutingProjectorModel
end Bounds
end QEC


