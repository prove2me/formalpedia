-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:52.059341+00:00
-- url     : https://prove2.me/theorems/4e27366b-89b1-49ac-a548-c2c43ce74c93
-- title:
--   KHComb Contract St
-- statement:
--   Definitions and structural lemmas for KHComb Contract St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KHCombContractSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
def KHCombContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k),
    i₀ ∉ J k → ∀ f : CombC S J n, combD S J n f = 0 →
      ∃ g : CombC S J n, f - g ∈ combB S J n ∧ ∀ I : CombCell ι J n,
        (J k = ∅ ∧ (I.1.1 k).card = 1 →
          ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = f I') ∧
        (¬ (J k = ∅ ∧ (I.1.1 k).card = 1) → g I = 0)
end
end GroundTheory.Heights₂.Heights.Kleiman


