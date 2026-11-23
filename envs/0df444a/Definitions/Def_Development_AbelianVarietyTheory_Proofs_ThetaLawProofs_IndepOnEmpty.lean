-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:26.005654+00:00
-- url     : https://prove2.me/theorems/d3a64980-1a6e-4057-b1ec-4581d7443c21
-- title:
--   Indep On Empty
-- statement:
--   Definitions and structural lemmas for Indep On Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IndepOnEmpty.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.RelBasis
variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
def comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) (c : Fin N → Γ(T, W)) (y : Y)
    (i : L.ι) : Y.presheaf.stalk y :=
  ∑ k, gs p₁ y W (c k) * gs p₂ y (L.U i) ((b k).f i)
def IndepOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ c : Fin N → Γ(T, W), (∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → comb b p₁ p₂ W c y i = 0) → c = 0
def SpanOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ σ : ∀ i : L.ι, Γ(Y, p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i),
    (∀ (y : Y) (i i' : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y _ (σ i) = (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val * gs (𝟙 Y) y _ (σ i')) →
    ∃ c : Fin N → Γ(T, W), ∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ W c y i
def BoxSpan (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) : Prop :=
  ∀ (K : Type) [Fintype K] (φ : K → (T ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim ε (fun _ => t)))),
    ∃ a : Fin N → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s r z J = ∑ k, sval (a k) (r ≫ p₁) z J * gs (r ≫ p₂) z (L.U (J (r ≫ p₂))) ((b k).f (J (r ≫ p₂)))
def gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom
end GlobalTheory.RelBasis


