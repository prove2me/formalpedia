-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAppellHumbertFrameOfPulledBiextension
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAppellHumbertFrameOfPulledBiextension
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:41.485145+00:00
-- url     : https://prove2.me/theorems/4ba87c02-f0e4-4797-af0a-5988c64ea992
-- title:
--   Exists Appell Humbert Frame Of Pulled Biextension
-- statement:
--   Definitions and structural lemmas for Exists Appell Humbert Frame Of Pulled Biextension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAppellHumbertFrameOfPulledBiextension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.PulledBiextFrame
open GlobalTheory.CubeValues GlobalTheory.SelfCube
def combUnif {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {K : Type} [Fintype K] (φ : K → (A.left ⟶ A.left))
    (p : K → (Fin g → ℂ) → (Fin g → ℂ)) (hd : ∀ k, Differentiable ℂ (p k)) (ε : K → ℤ)
    (hp : ∀ k z, (u.ex z).left ≫ φ k = (u.ex (p k z)).left) :
    HolUnif A (LB.LinComb L φ ε) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => ∏ k, u.fr (j k) (p k z) ^ ε k
  fr_hol := fun j => by
    have hD : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.LinComb L φ ε).U j →
        ∀ k, ⊤ ≤ (u.ex (p k z)).left ⁻¹ᵁ L.U (j k) := fun z hz k => by
      rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
    refine differentiableOn_prod' _ fun k => DifferentiableOn.zpow
      ((u.fr_hol (j k)).comp (hd k).differentiableOn fun z hz => hD z hz k) ?_
    exact Or.inl fun z hz => u.fr_ne _ _ (hD z hz k)
  fr_ne := fun j z hz => by
    refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ?_)
    rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
  fr_compat := fun j j' z hz => by
    obtain ⟨h1, h2⟩ := (le_preimage_inf _ _ _).1 hz
    have e := val_linComb (u.ex z).left GlobalTheory.valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * _) e.symm)
    simp only [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have a1 := (le_preimage_wchart (u.ex z).left L φ j).1 h1 k
    have a2 := (le_preimage_wchart (u.ex z).left L φ j').1 h2 k
    rw [hp] at a1 a2 ⊢
    rw [u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨a1, a2⟩), mul_zpow]
end GlobalTheory.PulledBiextFrame


