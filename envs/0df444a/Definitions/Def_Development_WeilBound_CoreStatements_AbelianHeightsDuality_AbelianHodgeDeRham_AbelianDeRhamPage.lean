-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_AbelianHodgeDeRham_AbelianDeRhamPage
-- name    : Development_WeilBound_CoreStatements_AbelianHeightsDuality_AbelianHodgeDeRham_AbelianDeRhamPage
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:07:07.818342+00:00
-- url     : https://prove2.me/theorems/19ec6595-0a5a-5870-98b9-5f5e5c74d5a8
-- title:
--   Abelian De Rham Page
-- statement:
--   Definitions and structural lemmas for Abelian De Rham Page, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/AbelianHodgeDeRham/AbelianDeRhamPage.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
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
open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
attribute [local instance] Over.cartesianMonoidalCategory
namespace FubiniStudyChowHeightFormula₂.Hdr
def IsVB (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M
def IsVBRank (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  IsVB R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n
def IsSubbundle {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (F : Submodule R M) (n : ℕ) : Prop :=
  IsVBRank R F n ∧ IsVB R (M ⧸ F)
abbrev Hodge1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) : Submodule R (HH1 s) :=
  LinearMap.range (clForm s)
def AbelianDeRhamPage : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    (∃ e : ⋀[R]^2 (HH1 A.hom) ≃ₗ[R] HH2 A.hom, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHH A.hom a b) ∧
    IsVBRank R (HH1 A.hom) (2 * g) ∧
    (ClosedForm A.hom = ⊤ ∧ Function.Injective (clForm A.hom) ∧ IsSubbundle (Hodge1 A.hom) g) ∧
    (Function.Exact (Hodge1 A.hom).subtype (toHO1 A.hom) ∧ Function.Surjective (toHO1 A.hom)) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
      (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
      (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, IsPull1 h.w c (e (1 ⊗ₜ c))) ∧
      (∃ e : R' ⊗[R] Hodge1 A.hom ≃ₗ[R'] Hodge1 s', ∀ c : Hodge1 A.hom, IsPull1 h.w c.1 (e (1 ⊗ₜ c)).1) ∧
      ∃ e : R' ⊗[R] HO1 A.hom ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))
end FubiniStudyChowHeightFormula₂.Hdr


