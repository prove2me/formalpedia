-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_GeometricComponentEmbedding
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_GeometricComponentEmbedding
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:57.645015+00:00
-- url     : https://prove2.me/theorems/0e7a34a9-ed65-57ce-8851-354a5f7a97d4
-- title:
--   Geometric Component Embedding
-- statement:
--   Definitions and structural lemmas for Geometric Component Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/GeometricComponentEmbedding.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Lie
variable {S : Scheme.{0}} {R : Type} [CommRing R]
abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)
variable {G : Over S} [GrpObj G]
def IsCombAt {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
def IsEigAt {O : Type} [CommRing O] (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left
def IsEigBasis {O : Type} [CommRing O] (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigAt act x χ (v i)) ∧ ∀ w, IsEigAt act x χ w → ∃! c : Fin n → R, IsCombAt c v w
end Lie
def gramSq {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin n → (Fin g → ℂ)) : ℝ :=
  (Matrix.of fun a b => (Real.pi : ℂ) * (z a ⬝ᵥ Hm.mulVec (star (z b)))).det.re
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
def embF (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F where
  toFun a := ⟨τ (a : E), c.conj τ a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
def embFc (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F := (embF c τ).comp (H.bar : 𝓞 E →+* 𝓞 E)
variable {Xo : Moduli D l} {c : Coeff l}
def IsGeomComponent (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) : Prop :=
  IsClosed (U : Set (Xo.XF c)) ∧
    GeometricallyConnected (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
def cpt (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) : Set Y.X :=
  closure (Y.j '' (U : Set (Xo.XF c)))
abbrev Rule (Y : Model Xo c (RingHom.id c.F)) : Type 1 :=
  ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.X), (Fin D.p → (epsAt x ⟶ Y.t.G)) → (Fin D.q → (epsAt x ⟶ Y.t.G)) → R
def IsFrame (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) {R : Type} [CommRing R]
    (j : c.F →+* R) (x : Sp R ⟶ Y.X) (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  x ≫ Y.s = spMap j ∧ Set.range x ⊆ cpt Y U ∧
    IsEigBasis Y.t.act x (j.comp (embF c τ)) v ∧ IsEigBasis Y.t.act x (j.comp (embFc c τ)) w
def IsDetSection (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : Rule Y) : Prop :=
  (∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) (v v' : Fin D.p → (epsAt x ⟶ Y.t.G))
      (w w' : Fin D.q → (epsAt x ⟶ Y.t.G)) (M : Matrix (Fin D.p) (Fin D.p) R) (N : Matrix (Fin D.q) (Fin D.q) R),
      IsFrame Y U τ j x v w → IsFrame Y U τ j x v' w' →
      (∀ i, IsCombAt (M i) v (v' i)) → (∀ i, IsCombAt (N i) w (w' i)) →
      sig R x v' w' * M.det = sig R x v w * N.det) ∧
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ Y.X)
      (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G))
      (v' : Fin D.p → (epsAt (spMap φ ≫ x) ⟶ Y.t.G)) (w' : Fin D.q → (epsAt (spMap φ ≫ x) ⟶ Y.t.G)),
      IsFrame Y U τ j x v w →
      (∀ i, (v' i).left = spMap (Chart.dualMapR φ) ≫ (v i).left) →
      (∀ i, (w' i).left = spMap (Chart.dualMapR φ) ≫ (w i).left) →
      sig R' (spMap φ ≫ x) v' w' = φ (sig R x v w)
def HasCoords {S : Scheme.{0}} {t : SAB H S} {x : Sp ℂ ⟶ S} {t' : SAB H (Sp ℂ)} (m : SABMap t' t x) {g : ℕ}
    (u : HolUnif t'.G t'.PP.L g) {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) (z : Fin n → (Fin g → ℂ)) : Prop :=
  ∀ i, ∃ v₀ : epsR ℂ ⟶ t'.G, v₀.left ≫ m.φ = (v i).left ∧ u.IsDiff (z i) v₀
def SqNormIs (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : Rule Y)
    (s : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (κ : ℝ) : Prop :=
  ∀ (v : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G))
    (t' : SAB H (Sp ℂ)) (m : SABMap t' Y.t (y ≫ Y.j)) (g : ℕ) (u : HolUnif t'.G t'.PP.L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (zv : Fin D.p → (Fin g → ℂ)) (zw : Fin D.q → (Fin g → ℂ)),
    IsFrame Y U τ s (y ≫ Y.j) v w → u.IsAH Hm χ → HasCoords m u v zv → HasCoords m u w zw →
    ‖sig ℂ (y ≫ Y.j) v w‖ ^ 2 * gramSq Hm zv = κ * gramSq Hm zw
def FlatLineNormConstant : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens), IsGeomComponent Xo c U →
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ∀ sig : Rule Y, IsDetSection Y U τ sig →
    ∀ s : c.F →+* ℂ, ∃ κ : ℝ, ∀ y : Sp ℂ ⟶ Xo.XF c,
      y ≫ pullback.snd _ _ = spMap s → Set.range y ⊆ (U : Set (Xo.XF c)) → SqNormIs Y U τ sig s y κ
example {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin 0 → (Fin g → ℂ)) : gramSq Hm z = 1 := by
  simp [gramSq]
example (a : ℂ) : gramSq (1 : Matrix (Fin 1) (Fin 1) ℂ) (fun _ : Fin 1 => fun _ => a) = Real.pi * ‖a‖ ^ 2 := by
  simp [gramSq, dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
example (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) :
    IsDetSection Y U τ (fun _ _ _ _ _ => 0) :=
  ⟨by intros; simp, by intros; simp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares


