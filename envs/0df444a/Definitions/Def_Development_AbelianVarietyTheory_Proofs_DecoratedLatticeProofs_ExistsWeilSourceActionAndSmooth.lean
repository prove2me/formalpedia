-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmooth
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmooth
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:43.176377+00:00
-- url     : https://prove2.me/theorems/8c841820-b0ba-4b99-b958-7cc96c90cbbc
-- title:
--   Exists Weil Source Action And Smooth
-- statement:
--   Definitions and structural lemmas for Exists Weil Source Action And Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsWeilSourceActionAndSmooth.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_smul_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
noncomputable section
namespace GlobalTheory.PosOne.SrcAction
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def srcRep {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k) (SB (Matrix b a k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om μ g 1 Φ.1, om_mem_SB μ g 1 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) 1 Φ.1 Ψ.1
        simpa using this
      map_smul' := fun z Φ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) z Φ.1 0
        have h0 : om μ g (1 : GL b k) (0 : Matrix b a k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (by
    show om μ (g * h) 1 Φ.1 = om μ g 1 (om μ h 1 Φ.1)
    rw [← om_mul, mul_one])
end GlobalTheory.PosOne.SrcAction
namespace GlobalTheory.PosOne
open GlobalTheory.PosOne.SrcAction
end GlobalTheory.PosOne


