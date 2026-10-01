-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailContactLossBridge
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailContactLossBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:59:30.076988+00:00
-- url     : https://prove2.me/theorems/93dd7442-57fd-4128-b829-6f4909f333c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailContactLossBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailContactLossBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailContactLossBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailContactLossBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailContactLossBridge.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailContactGainDerivative

-- ===== source module GeneralCK.PureGapDoubleCapLowTailContactLossBridge =====
section

/-! A finite upper certificate for the contact displacement can control
the true low-cap slope using the certified diagonal bias margin. -/

namespace GeneralCK

open Set

theorem doubleCapContactGain_increment_le_of_deriv_upper
    {c y L : ℝ} (hc : 0 < c) (hcy : c ≤ y) (hy : y < 1)
    (hupper : ∀ z ∈ Ioo c y, deriv doubleCapContactGain z ≤ L) :
    doubleCapContactGain y - doubleCapContactGain c ≤ L * (y - c) := by
  let f : ℝ → ℝ := fun z => L * z - doubleCapContactGain z
  have hf : ∀ z ∈ Icc c y,
      HasDerivAt f (L - deriv doubleCapContactGain z) z := by
    intro z hz
    have hz0 : 0 < z := hc.trans_le hz.1
    have hz1 : z < 1 := hz.2.trans_lt hy
    have h := ((hasDerivAt_id z).const_mul L).sub
      (doubleCapContactGain_hasDerivAt hz0 hz1)
    have hfexpr : f = (fun t : ℝ => L * t) - doubleCapContactGain := by
      funext t
      rfl
    rw [hfexpr]
    convert! h using 1
    simp only [mul_one, id_eq,
      (doubleCapContactGain_hasDerivAt hz0 hz1).deriv]
  have hmono : MonotoneOn f (Icc c y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c y)
    · intro z hz
      exact (hf z hz).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : z ∈ Ioo c y := by simpa using hz
      exact (hf z ⟨hz'.1.le, hz'.2.le⟩).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z ∈ Ioo c y := by simpa using hz
      rw [(hf z ⟨hz'.1.le, hz'.2.le⟩).deriv]
      exact sub_nonneg.mpr (hupper z hz')
  have hval := hmono ⟨le_rfl, hcy⟩ ⟨hcy, le_rfl⟩ hcy
  dsimp [f] at hval
  linarith only [hval]

theorem doubleCapSlopeBiasExpression_nonneg_of_contact_loss
    {y c L : ℝ}
    (hloss : doubleCapContactGain y - doubleCapContactGain c ≤ L * (y - c))
    (hdiag : 2 * L * (y - c) ≤ doubleCapSlopeBiasExpression y y) :
    0 ≤ doubleCapSlopeBiasExpression y c := by
  have hidentity : doubleCapSlopeBiasExpression y c =
      doubleCapSlopeBiasExpression y y -
        2 * (doubleCapContactGain y - doubleCapContactGain c) := by
    unfold doubleCapSlopeBiasExpression doubleCapContactGain
    ring
  rw [hidentity]
  linarith only [hloss, hdiag]

#print axioms doubleCapContactGain_increment_le_of_deriv_upper
#print axioms doubleCapSlopeBiasExpression_nonneg_of_contact_loss

end GeneralCK

end


