-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:49:50.35964+00:00
-- url     : https://prove2.me/theorems/e2a20b2c-8dbd-5895-866b-8cef32dc6353
-- title:
--   Scheme Descends To Subalgebra
-- statement:
--   Definitions and structural lemmas for Scheme Descends To Subalgebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
namespace GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
section Iso
variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}
def up {R R' : Subalgebra k V} (h : R ≤ R') (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q)
    (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    pullback p (spMap (algebraMap k R')) ⟶ pullback q (spMap (algebraMap k R')) :=
  pullback.lift (bcMap p (Subalgebra.inclusion h) ≫ ψ) (pullback.snd _ _)
    (by rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition])
@[reassoc]
theorem up_fst {R R' : Subalgebra k V} (h : R ≤ R') (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q)
    (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    up h ψ hψ ≫ pullback.fst _ _ = bcMap p (Subalgebra.inclusion h) ≫ ψ := pullback.lift_fst _ _ _
@[reassoc]
theorem up_snd {R R' : Subalgebra k V} (h : R ≤ R') (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q)
    (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    up h ψ hψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
@[reassoc]
theorem up_bcMap {R R' R'' : Subalgebra k V} (h : R ≤ R') (h' : R' ≤ R'')
    (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q) (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    up (h.trans h') ψ hψ ≫ bcMap q (Subalgebra.inclusion h') =
      bcMap p (Subalgebra.inclusion h') ≫ up h ψ hψ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, up_fst, Category.assoc, up_fst,
      bcMap_comp_of_eq_assoc p _ _ (Subalgebra.inclusion (h.trans h')) fun _ ↦ rfl]
  · rw [Category.assoc, bcMap_snd, up_snd_assoc, Category.assoc, up_snd, bcMap_snd]
end Iso
def HasModel {V : Type} [CommRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀),
    Algebra.FiniteType ℤ R ∧ LocallyOfFinitePresentation p₀ ∧ QuasiSeparated p₀ ∧ QuasiCompact p₀ ∧ IsPullback φ p p₀ (spMap f)
structure PairModel {S S₀ U T : Scheme.{0}} (f : S ⟶ S₀) (p : U ⟶ S) (a : T ⟶ U) where

  U₀ : Scheme.{0}

  T₀ : Scheme.{0}

  p₀ : U₀ ⟶ S₀

  a₀ : T₀ ⟶ U₀

  φ : U ⟶ U₀

  τ : T ⟶ T₀
  lfp : LocallyOfFinitePresentation p₀
  qs : QuasiSeparated p₀
  qc : QuasiCompact p₀
  opn : IsOpenImmersion a₀
  qca : QuasiCompact a₀
  hφ : IsPullback φ p p₀ f
  hτ : IsPullback τ a a₀ φ
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}
theorem isPullback_lift {X X₀ : Scheme.{0}} {q : X ⟶ S} {q₀ : X₀ ⟶ S₀} {φ : X ⟶ X₀} (h : IsPullback φ q q₀ f)
    (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    IsPullback (pullback.lift φ (q ≫ σ) (by rw [Category.assoc, e, h.w])) q (pullback.snd q₀ g) σ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q₀ g) (v₁₃ := q₀) (h₂₂ := g) ?_ (pullback.lift_snd _ _ _)
    (.of_hasPullback _ _)
  rw [pullback.lift_fst, e]
  exact h
def PairModel.baseChange (M : PairModel f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) : PairModel σ p a :=
  have w : M.τ ≫ M.a₀ ≫ M.p₀ = ((a ≫ p) ≫ σ) ≫ g := by
    rw [M.hτ.w_assoc, M.hφ.w, Category.assoc, Category.assoc, e]
  let a₁ : pullback (M.a₀ ≫ M.p₀) g ⟶ pullback M.p₀ g :=
    pullback.lift (pullback.fst _ _ ≫ M.a₀) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have h₁ : IsPullback (pullback.fst _ _) a₁ M.a₀ (pullback.fst _ _) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (.of_hasPullback M.p₀ g)
    rw [pullback.lift_snd]
    exact .of_hasPullback _ _
  { U₀ := pullback M.p₀ g
    T₀ := pullback (M.a₀ ≫ M.p₀) g
    p₀ := pullback.snd _ _
    a₀ := a₁
    φ := pullback.lift M.φ (p ≫ σ) (by rw [Category.assoc, e, M.hφ.w])
    τ := pullback.lift M.τ ((a ≫ p) ≫ σ) w
    lfp := inferInstance
    qs := inferInstance
    qc := inferInstance
    opn := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁ M.opn
    qca := MorphismProperty.of_isPullback (P := @QuasiCompact) h₁ M.qca
    hφ := isPullback_lift M.hφ σ g e
    hτ := by
      refine IsPullback.of_right ?_ ?_ h₁
      · rw [pullback.lift_fst, pullback.lift_fst]
        exact M.hτ
      · apply pullback.hom_ext
        · simp only [a₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, M.hτ.w]
        · simp only [a₁, Category.assoc, pullback.lift_snd] }
variable {V : Type} [CommRing V]
end GlobalTheory.SpreadScheme
namespace GlobalTheory
end GlobalTheory


