-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:59.532749+00:00
-- url     : https://prove2.me/theorems/fa59ac2e-3abf-4756-924a-65c755a1be8f
-- title:
--   Pull Top ZFConst Unit
-- statement:
--   Definitions and structural lemmas for Pull Top ZFConst Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/PullTopZFConstUnit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData
section Sections
variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]
def secVal {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε)) : Γ(Y, ⊤) :=
  (Y.presheaf.map (homOfLE (wchart_triv φ (fun _ => PUnit.unit)).ge).op).hom (s.f (fun _ => PUnit.unit))
end Sections
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]
def constUnit : Fˣ →* Γ((DegPre.BF (toricPre K X q) F).left, ⊤)ˣ :=
  (pullTop (fst (TF (R := K) F) (toricPre K X q).P.A).left).comp
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom)
end GlobalTheory.ToricData


