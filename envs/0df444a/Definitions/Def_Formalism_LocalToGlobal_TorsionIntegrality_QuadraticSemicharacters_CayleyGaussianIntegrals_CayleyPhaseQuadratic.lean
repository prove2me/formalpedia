-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:16.854924+00:00
-- url     : https://prove2.me/theorems/09886e0a-b082-4a83-a082-f21468b15255
-- title:
--   Cayley Phase Quadratic
-- statement:
--   Definitions and structural lemmas for Cayley Phase Quadratic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyPhaseQuadratic.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Phi
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
def phiQ (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V)
    (c : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : ℂ :=
  phiC H α Ae ((Quotient.out c : Λ) : V)
def bQ (H : Sesq V) (Λ : AddSubgroup V) (δ Ae : V ≃ₗ[ℂ] V)
    (c d : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : ℂ :=
  bC H Ae ((Quotient.out c : Λ) : V) ((Quotient.out d : Λ) : V)
end Phi
end Formalism.L2.Th1.H


