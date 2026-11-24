-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:23.900657+00:00
-- url     : https://prove2.me/theorems/02b3b370-9f3b-4878-bfc1-50612c168bb3
-- title:
--   PJoin Int Num
-- statement:
--   Definitions and structural lemmas for PJoin Int Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
namespace JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
def newVar : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) := ⟨.inr (), (0 : Fin 1)⟩
variable (F) in

def dropPt : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) → MRing ι F
  | ⟨.inl k, i⟩ => X ⟨k, i⟩
  | ⟨.inr _, _⟩ => 1
def extendZero : (K → ℕ) →+ (K ⊕ Unit → ℕ) where
  toFun a := Sum.elim a 0
  map_zero' := by
    funext x
    cases x <;> rfl
  map_add' a b := by
    funext x
    cases x <;> simp
def restrictFirst : (K ⊕ Unit → ℕ) →+ (K → ℕ) where
  toFun a k := a (.inl k)
  map_zero' := rfl
  map_add' _ _ := rfl
end
end JoinIntNum
end GroundTheory.Heights₂.Heights.NumbersDVR


