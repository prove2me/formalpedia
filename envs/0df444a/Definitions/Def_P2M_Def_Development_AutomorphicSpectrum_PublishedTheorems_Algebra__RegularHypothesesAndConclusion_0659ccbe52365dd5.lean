-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:47.452441+00:00
-- url     : https://prove2.me/theorems/a9d1236c-c635-4792-8ae9-503392a61cea
-- title:
--   Regular Hypotheses And Conclusion
-- statement:
--   Definitions and structural lemmas for Regular Hypotheses And Conclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.Hypotheses₂
namespace FreeQuot
universe u
def IsFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f
variable {S : Scheme.{u}} (G X : Over S) [GrpObj G] [ModObj G X]
def IsFreeAction : Prop :=
  ∀ (T : Over S) (g : T ⟶ G) (x : T ⟶ X), g • x = x → g = 1
def orbit (x : X.left) : Set X.left :=
  (γ[G, X] : G ⊗ X ⟶ X).left '' ((snd G X).left ⁻¹' {x})
def orbitPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := MulAction.orbitRel.Quotient (T.unop ⟶ G) (T.unop ⟶ X)
  map f := ↾(Quotient.map (fun x => f.unop ≫ x) (by
    rintro _ y ⟨g, rfl⟩
    exact ⟨f.unop ≫ g, (ModObj.comp_smul _ _ _).symm⟩))
  map_id T := by
    ext ⟨x⟩
    exact congrArg (Quotient.mk _) (Category.id_comp x)
  map_comp f g := by
    ext ⟨x⟩
    exact congrArg (Quotient.mk _) (Category.assoc _ _ x)
variable {X} {Y : Over S}
def IsInvariant (q : X ⟶ Y) : Prop :=
  (γ[G, X] : G ⊗ X ⟶ X) ≫ q = snd G X ≫ q
variable {G} in
theorem IsInvariant.smul_comp {q : X ⟶ Y} (h : IsInvariant G q) {T : Over S} (g : T ⟶ G) (x : T ⟶ X) :
    (g • x) ≫ q = x ≫ q := by
  rw [Hom.smul_def, Category.assoc, h, lift_snd_assoc]
variable {G} in

def IsInvariant.desc {q : X ⟶ Y} (h : IsInvariant G q) : orbitPresheaf G X ⟶ yoneda.obj Y where
  app T := ↾(Quotient.lift (fun x => x ≫ q) (by
    rintro _ y ⟨g, rfl⟩
    exact h.smul_comp g y))
  naturality T T' f := by
    ext ⟨x⟩
    exact Category.assoc _ _ _
def IsFppfQuotient (q : X ⟶ Y) : Prop :=
  ∃ h : IsInvariant G q,
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) h.desc ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) h.desc
def IsFppfTorsor (q : X ⟶ Y) : Prop :=
  IsPullback (γ[G, X] : G ⊗ X ⟶ X) (snd G X) q q ∧
    ∃ (J : Type u) (U : J → Scheme.{u}) (f : ∀ i, U i ⟶ Y.left),
      (∀ i, Flat (f i) ∧ LocallyOfFinitePresentation (f i)) ∧ (∀ y : Y.left, ∃ i z, f i z = y) ∧
        ∀ i, ∃ s : U i ⟶ X.left, s ≫ q.left = f i
end FreeQuot
open FreeQuot
def FreeQuotientScheme : Prop :=
  ∀ (S : Scheme.{0}) (G X : Over S) [GrpObj G] [ModObj G X],
    IsFiniteLocallyFree G.hom → IsFreeAction G X →
    (∀ x : X.left, ∃ U : X.left.Opens, IsAffineOpen U ∧ orbit G X x ⊆ U) →
    ∃ (Y : Over S) (q : X ⟶ Y), IsFppfQuotient G q ∧ IsFppfTorsor G q
namespace FreeQuot
universe u
variable {S : Scheme.{u}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
section Regular
attribute [local instance] ModObj.regular
end Regular
end FreeQuot
end GlobalTheory.CompanionTheory.Hypotheses₂


