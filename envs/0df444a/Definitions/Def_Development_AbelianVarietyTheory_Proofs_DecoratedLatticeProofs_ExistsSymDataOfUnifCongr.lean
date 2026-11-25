-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T11:17:07.23385+00:00
-- url     : https://prove2.me/theorems/86b28768-568d-5b90-93f2-4f0c0d834a7f
-- title:
--   Exists Sym Data Of Unif Congr
-- statement:
--   Definitions and structural lemmas for Exists Sym Data Of Unif Congr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSymDataOfUnifCongr.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
import Theorems.Thm_GlobalTheory_StepData_mem_KOne
import Theorems.Thm_GlobalTheory_SymSupport_InR_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
namespace GlobalTheory.SymChain
namespace UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
theorem reGL_symm_mem_KOne (e : ι ≃ Y) {d : GL Y k} (hd : d ∈ KOne k Y) : (reGL e).symm d ∈ KOne k ι :=
  mem_KOne.2 fun i j => by simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hd (e i) (e j)
def Near (F G : LatFrame k ι Y) : Prop := G.ord = F.ord ∧ F.bas⁻¹ * G.bas ∈ KOne k Y
theorem Near.conj {F G : LatFrame k ι Y} (h : Near F G) :
    ∃ d ∈ KOne k ι, ∀ g, G.conj.symm g = d⁻¹ * F.conj.symm g * d := by
  refine ⟨_, reGL_symm_mem_KOne F.ord h.2, fun g => ?_⟩
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, h.1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have : reGL F.ord (F.conj.symm g) = F.bas⁻¹ * g * F.bas := by
    conv_rhs => rw [← F.conj.apply_symm_apply g, LatFrame.conj_apply]
    group
  rw [this]; group
variable {ϖ ϖ' : kˣ}
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
end General
end UnifChange
open UnifChange
end GlobalTheory.SymChain


