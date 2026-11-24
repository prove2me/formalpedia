-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:09.907406+00:00
-- url     : https://prove2.me/theorems/8b7048c7-b9d9-45b7-84f8-842dcaa20716
-- title:
--   Admissible Lattice Family Hermitian Weil Action
-- statement:
--   Definitions and structural lemmas for Admissible Lattice Family Hermitian Weil Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilAction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
def rho (R : ℕ) (X : Matrix (Fin n) (Fin N ⊕ Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Matrix (Fin n) (Fin N) E → ℂ :=
  heisH (((2 * R : ℕ) : E) • X.toCols₁) (((2 * R : ℕ) : E) • X.toCols₂) φ
def cols (Λ : Lt E n) (N : ℕ) : AddSubgroup (Matrix (Fin n) (Fin N ⊕ Fin N) E) where
  carrier := {X | ∀ i, Xᵀ i ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy i => Λ.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => Λ.neg_mem (hx i)
abbrev Quo (Λ : Lt E n) (N s : ℕ) : Type :=
  cols Λ N ⧸ ((cols Λ N).map (nsmulAddMonoidHom s)).addSubgroupOf (cols Λ N)
end
end GlobalTheory.SW.WeilAdm
namespace GlobalTheory.SW
end GlobalTheory.SW


