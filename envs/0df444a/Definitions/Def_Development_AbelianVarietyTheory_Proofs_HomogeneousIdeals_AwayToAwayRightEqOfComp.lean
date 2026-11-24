-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T09:26:38.397708+00:00
-- url     : https://prove2.me/theorems/72a58de2-cb86-4286-85f3-56fc7913dec1
-- title:
--   Away To Away Right Eq Of Comp
-- statement:
--   Definitions and structural lemmas for Away To Away Right Eq Of Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AwayToAwayRightEqOfComp.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
abbrev tanExp (v : Fin n → (epsR R ⟶ G)) (s : Fin n → S) : sp (R₀ := R) (DualNumber S) ⟶ G :=
  lieExp v (fun i => (inr (s i) : DualNumber S)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
variable (S) in

def IsLieBasisOver (v : Fin n → (epsR R ⟶ G)) : Prop :=
  (∀ s s' : Fin n → S, tanExp v s = tanExp v s' → s = s') ∧
    ∀ w : sp (R₀ := R) (DualNumber S) ⟶ G, IsTanOver w → ∃ s, w = tanExp v s
variable (A) in

def ExpBij (v : Fin n → (epsR R ⟶ G)) : Prop :=
  ∀ J : Ideal A, J ^ 2 = ⊥ →
    (∀ (c c' : Fin n → A), (∀ i, c i ∈ J) → (∀ i, c' i ∈ J) → ∀ hc hc',
      lieExp v c hc = lieExp v c' hc' → c = c') ∧
    ∀ y ∈ redKer G J, ∃ (c : Fin n → A) (hc : ∀ i, c i * c i = 0),
      (∀ i, c i ∈ J) ∧ y = lieExp v c hc
variable {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
end GlobalTheory.SqZero


