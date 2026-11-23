-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:11.020659+00:00
-- url     : https://prove2.me/theorems/378ea8ff-f17d-4466-b83a-61111a3891bd
-- title:
--   Exists Rational Symplectic Of Unitary Cm Field
-- statement:
--   Definitions and structural lemmas for Exists Rational Symplectic Of Unitary Cm Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
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
namespace GlobalTheory.SW.UniSp
noncomputable section
section Abstract
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  {S : Matrix ι K ℂ} {S' : Matrix K ι ℂ}
variable {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
variable [DecidableEq m]
def dl (X : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ := fromBlocks X 0 0 Xᴴᵀ
def sw (m : Type) [DecidableEq m] : Matrix (m ⊕ m) (m ⊕ m) ℂ := fromBlocks 0 1 1 0
end Abstract
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
def Sm (Ψ : Finset (E →+* ℂ)) (N : ℕ) : Matrix (QI E N) ((Fin N ⊕ Fin N) × Ψ) ℂ :=
  Matrix.of fun p q => Sum.elim
    (fun b => if p.1 = b then q.2.1 (Module.finBasis ℚ E p.2) else 0)
    (fun b => if p.1 = b then conj (q.2.1 (Module.finBasis ℚ E p.2)) else 0) q.1
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
end
end GlobalTheory.SW.UniSp


