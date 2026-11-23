-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:15.557856+00:00
-- url     : https://prove2.me/theorems/18d107a3-bc82-4ec2-a96e-8c1e96130240
-- title:
--   Annihilator Of Annihilator Le
-- statement:
--   Definitions and structural lemmas for Annihilator Of Annihilator Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
def perpSub {V : Type} [AddCommGroup V] (χ : V → V → ℂ) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  add_mem' := by
    intro y y' hy hy' x hx
    rw [hs, ha, hs y, hs y', hy x hx, hy' x hx, one_mul]
  zero_mem' := by
    intro x _
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have := ha 0 0 x
    rw [add_zero] at this
    rw [hs]
    exact (mul_eq_left₀ hne).1 this.symm
  neg_mem' := by
    intro y hy x hx
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have h0 : χ 0 x = 1 := by
      have := ha 0 0 x
      rw [add_zero] at this
      exact (mul_eq_left₀ hne).1 this.symm
    have := ha y (-y) x
    rw [add_neg_cancel, h0, hs y x, hy x hx, one_mul] at this
    rw [hs]
    exact this.symm
end GlobalTheory.CompanionTheory.SW.CofinalDual


