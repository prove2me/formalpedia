-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:44:05.773795+00:00
-- url     : https://prove2.me/theorems/935a08af-56ae-47c7-a271-709c65514e6c
-- title:
--   Base Case False General Holds
-- statement:
--   Definitions and structural lemmas for Base Case False General Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
section general
variable {k : Type*} [Field k] {S : Type*} {v : AddValuation k (WithTop ℝ)}
def HasWtG (v : AddValuation k (WithTop ℝ)) (ω : (S →₀ ℕ) →+ ℝ) (w : ℝ)
    (f : MvPowerSeries S k) : Prop :=
  ∀ E : S →₀ ℕ, (w : WithTop ℝ) ≤ v (coeff E f) + ((ω E : ℝ) : WithTop ℝ)
end general
section two
variable {k : Type*} [Field k] {Z Z' : Type*} {v : AddValuation k (WithTop ℝ)}
def om2 (Z Z' : Type*) (r r' : ℝ) : ((Z ⊕ Z') →₀ ℕ) →+ ℝ where
  toFun E := (((Finsupp.sumFinsuppAddEquivProdFinsupp E).1.degree : ℕ) : ℝ) * r +
    (((Finsupp.sumFinsuppAddEquivProdFinsupp E).2.degree : ℕ) : ℝ) * r'
  map_zero' := by simp
  map_add' E F := by
    simp only [map_add, Prod.fst_add, Prod.snd_add]
    push_cast
    ring
end two
namespace Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
end Data
end
end Formalism.BaseCaseIdentities


