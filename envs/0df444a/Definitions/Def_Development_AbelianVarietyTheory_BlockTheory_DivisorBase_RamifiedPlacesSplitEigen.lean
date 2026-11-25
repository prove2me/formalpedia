-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_RamifiedPlacesSplitEigen
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_RamifiedPlacesSplitEigen
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:20.589673+00:00
-- url     : https://prove2.me/theorems/6a578168-0f98-4976-9b67-0864b5af8711
-- title:
--   Ramified Places Split Eigen
-- statement:
--   Definitions and structural lemmas for Ramified Places Split Eigen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/RamifiedPlacesSplitEigen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
section Frames
variable {S : Scheme.{0}} {R : Type} [CommRing R]
abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G]
def IsEigTan (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left
def IsCombAt {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
def IsEigBasis (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigTan act x χ (v i)) ∧ ∀ w, IsEigTan act x χ w → ∃! c : Fin n → R, IsCombAt c v w
end Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def RamifiedPlacesSplit (H : Host E) : Prop :=
  IsAbelianGalois ℚ E ∧
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ differentIdeal ℤ (𝓞 E) →
    w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 E) ∈ w.asIdeal →
      (ℓ ≠ H.d ∧ IsSquare (-(H.d : ZMod ℓ))) ∨ (ℓ = H.d ∧ ¬ w.asIdeal ^ 3 ∣ Ideal.span {(ℓ : 𝓞 E)})
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def charIn (c : Coeff l) {R : Type} [CommRing R] (φ : c.F →+* R) (τ : E →+* ℂ) : 𝓞 E →+* R :=
  φ.comp ((τ.codRestrict c.F (c.conj τ)).comp (algebraMap (𝓞 E) E))
abbrev Rule (Y : Model Xo c β) : Type 1 :=
  ∀ (R : Type) [CommRing R] (_ : c.F →+* R) (x : Sp R ⟶ Y.X),
    (Fin D.p → (epsAt x ⟶ Y.t.G)) → (Fin D.q → (epsAt x ⟶ Y.t.G)) → R
def IsFrame (Y : Model Xo c β) (τ : E →+* ℂ) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Y.X)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  x ≫ Y.s = spMap (φ.comp β) ∧ IsEigBasis Y.t.act x (charIn c φ τ) v ∧
    IsEigBasis Y.t.act x (charIn c φ (conjEmb τ)) w
def IsDetSection (Y : Model Xo c β) (τ : E →+* ℂ) (f : Rule Y) : Prop :=
  (∀ (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Y.X) (v v' : Fin D.p → (epsAt x ⟶ Y.t.G))
      (w w' : Fin D.q → (epsAt x ⟶ Y.t.G)) (M : Matrix (Fin D.p) (Fin D.p) R) (N : Matrix (Fin D.q) (Fin D.q) R),
      IsFrame Y τ φ x v w → IsFrame Y τ φ x v' w' → (∀ i, IsCombAt (M i) v (v' i)) → (∀ i, IsCombAt (N i) w (w' i)) →
      f R φ x v w * N.det = f R φ x v' w' * M.det) ∧
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (φ : c.F →+* R) (x : Sp R ⟶ Y.X)
      (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G))
      (v' : Fin D.p → (epsAt (spMap g ≫ x) ⟶ Y.t.G)) (w' : Fin D.q → (epsAt (spMap g ≫ x) ⟶ Y.t.G)),
      IsFrame Y τ φ x v w → IsFrame Y τ (g.comp φ) (spMap g ≫ x) v' w' →
      (∀ i, (v' i).left = spMap (dualMapR g) ≫ (v i).left) → (∀ i, (w' i).left = spMap (dualMapR g) ≫ (w i).left) →
      f R' (g.comp φ) (spMap g ≫ x) v' w' = g (f R φ x v w)
def IsGeomComponent (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) : Prop :=
  IsClosed (U : Set (Xo.XF c)) ∧ GeometricallyConnected (U.ι ≫ pullback.snd _ _)
def IsPointOf (U : (Xo.XF c).Opens) {k : Type} [Field k] (φ : c.F →+* k) (y : Sp k ⟶ Xo.XF c) : Prop :=
  y ≫ pullback.snd _ _ = spMap φ ∧ Set.range y ⊆ (U : Set (Xo.XF c))
def NonzeroOn (Y : Model Xo c β) (τ : E →+* ℂ) (f : Rule Y) (U : (Xo.XF c).Opens) : Prop :=
  ∃ (k : Type) (_ : Field k) (φ : c.F →+* k) (y : Sp k ⟶ Xo.XF c)
    (v : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)),
    IsPointOf U φ y ∧ IsFrame Y τ φ (y ≫ Y.j) v w ∧ f k φ (y ≫ Y.j) v w ≠ 0
def IsCommonFibre {B : Type} [CommRing B] {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] (a₀ : OAct B G₀)
    {V K : Type} [CommRing V] [Field K] [Algebra V K] (x : Sp K ⟶ S) {𝒢 : Over (Sp V)} [GrpObj 𝒢] (a₁ : OAct B 𝒢)
    {A : Over (Sp K)} [GrpObj A] (a : OAct B A) (φ₀ : A.left ⟶ G₀.left) (φ₁ : A.left ⟶ 𝒢.left) : Prop :=
  IsGrpPullback A G₀ x φ₀ ∧ IsGrpPullback A 𝒢 (spMap (algebraMap V K)) φ₁ ∧
    (∀ b, (a.act b).left ≫ φ₀ = φ₀ ≫ (a₀.act b).left) ∧ ∀ b, (a.act b).left ≫ φ₁ = φ₁ ≫ (a₁.act b).left
def HasValAt (Y : Model Xo c β) (τ : E →+* ℂ) (f : Rule Y) (U : (Xo.XF c).Opens)
    (lam : HeightOneSpectrum (𝓞 c.F)) (r : ℚ) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V K : Type) [CommRing V] [Field K] [Algebra V K] (j : K →+* ℂ_[ℓ]) (φ : c.F →+* K),
    Function.Injective (algebraMap V K) → (∀ z : K, z ∈ Set.range (algebraMap V K) ↔ ‖j z‖ ≤ 1) →
    (∀ a : 𝓞 c.F, a ∈ lam.asIdeal ↔ ‖j (φ (a : c.F))‖ < 1) →
    ∀ y : Sp K ⟶ Xo.XF c, IsPointOf U φ y →
    ∀ (𝒢 : Over (Sp V)) [GrpObj 𝒢] (a₁ : OAct (𝓞 E) 𝒢) (A : Over (Sp K)) [GrpObj A] (a : OAct (𝓞 E) A)
      (φ₀ : A.left ⟶ Y.t.G.left) (φ₁ : A.left ⟶ 𝒢.left),
      IsSemiAbelian 𝒢 → IsCommonFibre Y.t.act (y ≫ Y.j) a₁ a φ₀ φ₁ →
    ∀ (χ χ' : 𝓞 E →+* V), (algebraMap V K).comp χ = charIn c φ τ →
      (algebraMap V K).comp χ' = charIn c φ (conjEmb τ) →
    ∀ (u : Fin D.p → (epsAt (𝟙 (Sp V)) ⟶ 𝒢)) (u' : Fin D.q → (epsAt (𝟙 (Sp V)) ⟶ 𝒢))
      (v : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)),
      IsEigBasis a₁ (𝟙 (Sp V)) χ u → IsEigBasis a₁ (𝟙 (Sp V)) χ' u' → IsFrame Y τ φ (y ≫ Y.j) v w →
      (∀ i, ∃ z : Sp (DualNumber K) ⟶ A.left,
        z ≫ φ₁ = spMap (dualMapR (algebraMap V K)) ≫ (u i).left ∧ z ≫ φ₀ = (v i).left) →
      (∀ i, ∃ z : Sp (DualNumber K) ⟶ A.left,
        z ≫ φ₁ = spMap (dualMapR (algebraMap V K)) ≫ (u' i).left ∧ z ≫ φ₀ = (w i).left) →
      ‖j (f K φ (y ≫ Y.j) v w)‖ = (ℓ : ℝ) ^ (-(r : ℝ))
def ValConstAt (H : Host E) : Prop :=
  ∀ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (U : (Xo.XF c).Opens), IsGeomComponent Xo c U →
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
    ∀ f : Rule Y, IsDetSection Y τ f → NonzeroOn Y τ f U →
    ∀ lam : HeightOneSpectrum (𝓞 c.F), ∃ r : ℚ, HasValAt Y τ f U lam r
def Stmt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), RamifiedPlacesSplit H → ValConstAt H
example (ℓ : ℕ) [Fact ℓ.Prime] : ‖(ℓ : ℂ_[ℓ])‖ = (ℓ : ℝ) ^ (-((1 : ℚ) : ℝ)) := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends, ← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)),
    PadicAlgCl.norm_extends, Padic.norm_p, Rat.cast_one, Real.rpow_neg_one]
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen


