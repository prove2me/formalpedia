-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:09.489278+00:00
-- url     : https://prove2.me/theorems/3ff6aa57-42cf-44de-a42e-cc6a8a213aae
-- title:
--   Local Component GL
-- statement:
--   Definitions and structural lemmas for Local Component GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LocalComponentGL.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
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
section Reps
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def repClass {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (x : S) :
    Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ :=
  QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : Λ₂)
end Reps
end Formalism.L2.Th1.H


