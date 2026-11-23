-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_CanonicalRigidImages
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_CanonicalRigidImages
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:35.000442+00:00
-- url     : https://prove2.me/theorems/ef0d5268-f030-4c26-831b-61326aed5961
-- title:
--   Canonical Rigid Images
-- statement:
--   Definitions and structural lemmas for Canonical Rigid Images, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/CanonicalRigidImages.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages
def fnSec {Z Y : Scheme.{0}} (L : LB Z) (f : Γ(Y, ⊤)) :
    LB.Sec (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  f := fun _ => (Y.presheaf.map (homOfLE le_top).op).hom f
  compat := by
    intro i j
    have key : ∀ {U W : Y.Opens} (h : W ≤ U),
        (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom f) =
          (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f := by
      intro U W h
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      rfl
    have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
      rfl
    rw [key, key, hg, Units.val_one, _root_.one_mul]
def unitGen {Z Y : Scheme.{0}} (L : LB Z) (u : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top u
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (e : ℕ)
abbrev Se (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Scheme.{0} :=
  Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))
abbrev Be : Over (Se R I e) := thickObj R I e D.P.A
abbrev up (T : Over (Se R I e)) : Over (Spec (CommRingCat.of R)) := Over.mk (T.hom ≫ thick R I e)
def down {T : Over (Se R I e)} (y : T ⟶ Be D I e) : up I e T ⟶ D.P.A :=
  Over.homMk (y.left ≫ pullback.fst D.P.A.hom (thick R I e)) (by
    have h := Over.w y
    dsimp at h ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])
def cPt (T : Over (Se R I e)) (χ : D.X) : up I e T ⟶ D.P.A := toUnit _ ≫ D.c χ
def oφ {T : Over (Se R I e)} (y : T ⟶ Be D I e) (χ : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cPt D I e T χ) (down D I e y)).left, (cPt D I e T χ).left, (down D I e y).left,
    (pzero D.P.A (up I e T)).left]
def oε : Fin 4 → ℤ := ![1, -1, -1, 1]
def oεinv : Fin 4 → ℤ := fun k => - oε k
def oLB (χ : D.X) : LB (Be D I e).left := LB.LinComb D.P.L (oφ D I e (𝟙 _) χ) oε
def cubAt {T : Over (Se R I e)} (a b d : up I e T ⟶ D.P.A) :=
  LB.pullGen (Z := T.left) D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift b d)).left
def IsImage {H : Over (Se R I e)} (q : H ⟶ Be D I e) (χ : D.X)
    (x : LB.Gen (LB.LinComb D.P.L (oφ D I e q χ) oεinv)) (V : (Be D I e).left.Opens)
    (s : LB.Sec (LB.LinComb D.P.L (fun k => V.ι ≫ oφ D I e (𝟙 _) χ k) oε))
    (h : Γ((q.left ⁻¹ᵁ V).toScheme, ⊤)) : Prop :=
  GeneratorPullback.SecRel D.P.L _ _ (fnSec D.P.L h) _ _ s (q.left ∣_ V) _ _
    (LB.pullGen D.P.L _ _ x (q.left ⁻¹ᵁ V).ι)
structure GtIso (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where

  q : thickObj R I e G ⟶ Be D I e
  q_hom : IsMonHom q
  q_affine : IsAffineHom q.left

  x : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (oφ D I e q χ) oεinv)
  x_gen : ∀ χ, (x χ).IsGen

  x_add : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (x (χ + χ'))
      (cubAt D I e (cPt D I e _ χ) (cPt D I e _ χ') (down D I e q)))
    (LB.mulGen D.P.L _ _ _ _ (x χ) (x χ'))

  x_mul : ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ (x χ) (μ[thickObj R I e G]).left)
      (cubAt D I e (cPt D I e _ χ)
        (down D I e (fst (thickObj R I e G) (thickObj R I e G) ≫ q))
        (down D I e (snd (thickObj R I e G) (thickObj R I e G) ≫ q))))
    (LB.mulGen D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ (x χ) (fst (thickObj R I e G) (thickObj R I e G)).left)
      (LB.pullGen D.P.L _ _ (x χ) (snd (thickObj R I e G) (thickObj R I e G)).left))

  span : ∀ (V : (Be D I e).left.Opens), IsAffineOpen V →
    ∀ f : Γ((q.left ⁻¹ᵁ V).toScheme, ⊤),
      ∃ (F : Finset D.X)
        (s : ∀ χ, LB.Sec (LB.LinComb D.P.L (fun k => V.ι ≫ oφ D I e (𝟙 _) χ k) oε))
        (h : D.X → Γ((q.left ⁻¹ᵁ V).toScheme, ⊤)),
        (∀ χ ∈ F, IsImage D I e q χ (x χ) V (s χ) (h χ)) ∧ f = ∑ χ ∈ F, h χ

  indep : ∀ (V : (Be D I e).left.Opens), IsAffineOpen V →
    ∀ (F : Finset D.X)
      (s : ∀ χ, LB.Sec (LB.LinComb D.P.L (fun k => V.ι ≫ oφ D I e (𝟙 _) χ k) oε))
      (h : D.X → Γ((q.left ⁻¹ᵁ V).toScheme, ⊤)),
      (∀ χ ∈ F, IsImage D I e q χ (x χ) V (s χ) (h χ)) → ∑ χ ∈ F, h χ = 0 →
        ∀ χ ∈ F, ∀ j, (s χ).f j = 0

  i : splitTorus (Se R I e) D.X ⟶ thickObj R I e G
  i_hom : IsMonHom i
  i_q : i ≫ q = toUnit _ ≫ η[Be D I e]

  i_char : ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (x χ) i.left) (unitGen D.P.L (charUnit (Se R I e) D.X χ))
def IsCanonRig (χ : D.X) (r : LB.Gen ((oLB D I e χ).pull (eSec (Be D I e)))) : Prop :=
  ∀ j : Fin 4 → D.P.L.ι, LB.Coh D.P.L (fun k => eSec (Be D I e) ≫ oφ D I e (𝟙 _) χ k) j →
    r.s (fun _ => j) = 1
def IsGtOfData (H : Over (Se R I e)) [GrpObj H] : Prop :=
  ∃ (hB : IsAbelianScheme (Be D I e))
    (r : ∀ χ, LB.Gen ((oLB D I e χ).pull (eSec (Be D I e))))
    (hL : ∀ χ, (oLB D I e χ).IsLB) (hr : ∀ χ, (r χ).IsGen)
    (hadd : ∀ χ χ' : D.X, ∃ t : LB.Iso (oLB D I e χ') (LB.div (oLB D I e (χ + χ')) (oLB D I e χ)),
      t.IsGen)
    (hzero : ∃ t : LB.Gen (oLB D I e 0), t.IsGen)
    (hprim : ∀ χ : D.X, ∃ t : LB.Gen (abelian₂ (Be D I e) (oLB D I e χ)), t.IsGen),
    (∀ χ, IsCanonRig D I e χ (r χ)) ∧
    SplitExt.IsGt
      ({ B := Be D I e, isAbelian := hB, X := D.X,
         O := fun χ => ⟨oLB D I e χ, r χ, hL χ, hr χ⟩,
         addIso := hadd, zeroTriv := hzero, primitive := hprim } : SplitExt (Se R I e)) H
def NonemptyIffIsGt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
    Nonempty (GtIso D I e G) ↔ IsGtOfData D I e (thickObj R I e G)
example : ∑ k, oε k = 0 ∧ oεinv = ![-1, 1, 1, -1] := by decide
example {T T' : Over (Se R I e)} (f : T' ⟶ T) (y : T ⟶ Be D I e) :
    (down D I e (f ≫ y)).left = f.left ≫ (down D I e y).left := by
  simp [down]
end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages


