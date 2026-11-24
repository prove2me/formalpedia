-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:57.005826+00:00
-- url     : https://prove2.me/theorems/483f6229-a5ee-4ae6-84c1-01a863fbb08d
-- title:
--   Translation Invariant Schwartz Bruhat Map Factors Inte
-- statement:
--   Definitions and structural lemmas for Translation Invariant Schwartz Bruhat Map Factors Inte, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
namespace GlobalTheory.SplitWeil.HaarFactor
section General
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
example (U : AddSubgroup A) (a b : A) : ((a : A ⧸ U) = b) ↔ a - b ∈ U := QuotientAddGroup.eq_iff_sub_mem
theorem tens_mem {f : X₀ → ℂ} (hf : f ∈ SB X₀) {φ : A → ℂ} (hφ : φ ∈ SB A) :
    (fun z : X₀ × A => f z.1 * φ z.2) ∈ SB (X₀ × A) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hφ.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (hf.2.prod hφ.2) fun z hz => ?_⟩
  rcases not_and_or.mp (Set.mem_prod.not.mp hz) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
def tensL (φ : SB A) : SB X₀ →ₗ[ℂ] SB (X₀ × A) where
  toFun f := ⟨fun z => f.1 z.1 * φ.1 z.2, tens_mem f.2 φ.2⟩
  map_add' f g := by ext z; simp [add_mul]
  map_smul' c f := by ext z; simp [mul_assoc]
section Meas
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
end Meas
end General
section Concrete
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def cballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball
def boxSub (n : Type*) (s : kˣ) : AddSubgroup (n → k) := AddSubgroup.pi Set.univ fun _ => cballSub s
end Concrete
end GlobalTheory.SplitWeil.HaarFactor


