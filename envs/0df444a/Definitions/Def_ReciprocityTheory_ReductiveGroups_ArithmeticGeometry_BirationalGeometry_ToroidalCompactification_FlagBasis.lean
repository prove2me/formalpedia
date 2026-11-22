-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:20.454896+00:00
-- url     : https://prove2.me/theorems/5ba2af87-437a-455c-8b39-424236be0509
-- title:
--   Flag Basis
-- statement:
--   Definitions and structural lemmas for Flag Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/FlagBasis.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.dupNamespace false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonObj NumberField IsLocalRing MvPolynomial
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Tan
variable {V : Type} [CommRing V]
abbrev ptOver (V R : Type) [CommRing V] [CommRing R] [Algebra V R] : Over (Sp V) :=
  Over.mk (spMap (algebraMap V R))
abbrev epsOver (V R : Type) [CommRing V] [CommRing R] [Algebra V R] : Over (Sp V) :=
  Over.mk (spMap ((algebraMap R (DualNumber R)).comp (algebraMap V R)))
def epsMul {R : Type} [CommRing R] (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom
variable {R : Type} [CommRing R] [Algebra V R] {G : Over (Sp V)} [GrpObj G]
def IsTan (v : epsOver V R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : ptOver V R ⟶ G).left
def IsComb {m : ℕ} (v : Fin m → (epsOver V R ⟶ G)) (c : Fin m → R) (w : epsOver V R ⟶ G) : Prop :=
  ∃ u : Fin m → (epsOver V R ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
end Tan
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
structure ValPt (Y : Model Xo c β) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  K' : Type
  [fld : Field K']
  [alg : Algebra V K']
  [frac : IsFractionRing V K']
  complete : IsAdicComplete (maximalIdeal V) V
  char0 : CharZero K'
  oV : O →+* V
  fK : c.F →+* K'
  compat : (algebraMap V K').comp oV = fK.comp β
  y : Sp K' ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = spMap fK
  yt : Sp V ⟶ Y.X
  yt_over : yt ≫ Y.s = spMap oV
  ext : spMap (algebraMap V K') ≫ yt = y ≫ Y.j
  G : SAB H (Sp V)
  pull : SABMap G Y.t yt
attribute [instance] ValPt.ring ValPt.dom ValPt.dvr ValPt.fld ValPt.alg ValPt.frac
variable {Y : Model Xo c β}
def ValPt.IsAlg (P : ValPt Y) : Prop := Finite (ResidueField P.V) ∧ IsLocalHom P.oV
def ValPt.IsTrivOnF (P : ValPt Y) : Prop := ∃ f : c.F →+* P.V, f.comp β = P.oV ∧ (algebraMap P.V P.K').comp f = P.fK
def ValPt.emb (P : ValPt Y) (τ : E →+* ℂ) (a : 𝓞 E) : P.K' := P.fK ⟨τ (a : E), c.conj τ a⟩
def ValPt.IsEig (P : ValPt Y) {R : Type} [CommRing R] [Algebra P.V R] (τ : E →+* ℂ)
    (v : epsOver P.V R ⟶ P.G.G) : Prop :=
  ∀ (a : 𝓞 E) (z : P.V), algebraMap P.V P.K' z = P.emb τ a →
    (v ≫ P.G.act.act a).left = spMap (epsMul (algebraMap P.V R z)) ≫ v.left
def Datum.mult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q
def conjEmb (τ : E →+* ℂ) : E →+* ℂ := (starRingEnd ℂ).comp τ
structure FlagBasis (P : ValPt Y) where
  u : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (epsOver P.V P.V ⟶ P.G.G)
  tan : ∀ τ i, IsTan (u τ i)
  eig : ∀ τ i, P.IsEig τ (u τ i)
  basis : ∀ τ (w : epsOver P.V P.V ⟶ P.G.G), IsTan w → P.IsEig τ w → ∃! a : Fin (D.mult τ) → P.V, IsComb (u τ) a w
section Letters
variable (D) (n : ℕ)
def Letter : Type := {x : (E →+* ℂ) × ℕ × Fin n // x.2.1 < D.mult x.1}
variable {D n}
def Letter.row (x : Letter D n) : (E →+* ℂ) × ℕ := (x.1.1, x.1.2.1)
def letter (τ : E →+* ℂ) (i : ℕ) (b : Fin n) (h : i < D.mult τ) : Letter D n := ⟨(τ, i, b), h⟩
def harmOp (τ : E →+* ℂ) (i i' : ℕ) (hi : i < D.mult τ) (hi' : i' < D.mult (conjEmb τ)) :
    MvPolynomial (Letter D n) ℤ →ₗ[ℤ] MvPolynomial (Letter D n) ℤ :=
  ∑ b : Fin n, (pderiv (letter τ i b hi)).toLinearMap ∘ₗ (pderiv (letter (conjEmb τ) i' b hi')).toLinearMap
def rowWt (r : (E →+* ℂ) × ℕ) (x : Letter D n) : ℕ := if x.row = r then 1 else 0
def rowAdd (τ : E →+* ℂ) (j i : ℕ) (hji : j < i) (t : ℤ) :
    MvPolynomial (Letter D n) ℤ →ₐ[ℤ] MvPolynomial (Letter D n) ℤ :=
  bind₁ fun x => if h : x.1.1 = τ ∧ x.1.2.1 = i then
      X x + C t * X (letter τ j x.1.2.2 (by have h3 := x.2; rw [h.1, h.2] at h3; omega))
    else X x
def FF (a : (E →+* ℂ) × ℕ → ℕ) : Submodule ℤ (MvPolynomial (Letter D n) ℤ) :=
  (⨅ (τ : E →+* ℂ) (_ : τ (H.rt : E) = H.rt0) (i : ℕ) (i' : ℕ) (hi : i < D.mult τ) (hi' : i' < D.mult (conjEmb τ)),
      LinearMap.ker (harmOp τ i i' hi hi')) ⊓
    (⨅ r : (E →+* ℂ) × ℕ, weightedHomogeneousSubmodule ℤ (rowWt r) (a r)) ⊓
    ⨅ (τ : E →+* ℂ) (j : ℕ) (i : ℕ) (h : j < i) (t : ℤ),
      LinearMap.ker ((rowAdd τ j i h t).toLinearMap - LinearMap.id)
end Letters
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


