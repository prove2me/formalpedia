-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:55.963956+00:00
-- url     : https://prove2.me/theorems/16a41c3e-3fa1-44db-85f9-f2c192475ee7
-- title:
--   Alg Over Hom Surjective
-- statement:
--   Definitions and structural lemmas for Alg Over Hom Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AlgOverHomSurjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf
section General
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]
end General
variable {k : Type} [Field k]
def IsChart (G : Over (Sp k)) [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    (ε : A →ₐ[k] k) {r : ℕ} (f : Fin r → A) : Prop :=
  IsOpenImmersion j.left ∧ algOverHom ε ≫ j = 1 ∧ Algebra.adjoin k (Set.range f) = ⊤ ∧ ∀ i, ε (f i) = 0
def TwoVar {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    {r : ℕ} (f : Fin r → A) (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ (F : Type) [Field F] [Algebra k F] (τ : MvPowerSeries (Fin 2) k →ₐ[k] F)
    (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] F), τ d ≠ 0 →
    (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) →
    (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) →
    ∃ χ : A →ₐ[k] F, (∀ i, χ (f i) * τ d = τ (h i)) ∧
      algOverHom σ₁ ≫ a = (algOverHom χ ≫ j) * (algOverHom σ₀ ≫ a)
end GlobalTheory.SS.ArcInf
end


