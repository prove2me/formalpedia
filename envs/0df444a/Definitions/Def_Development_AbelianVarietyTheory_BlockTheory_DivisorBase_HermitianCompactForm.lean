-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCompactForm
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCompactForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:58.653264+00:00
-- url     : https://prove2.me/theorems/f11a96d3-e5ed-4338-a5ed-efa90446e26b
-- title:
--   Hermitian Compact Form
-- statement:
--   Definitions and structural lemmas for Hermitian Compact Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HermitianCompactForm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Frames
variable {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] {R : Type} [CommRing R]
abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)
def IsEigAt (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left
def IsCombAt (x : Sp R ⟶ S) {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
def IsEigBasisAt (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigAt act x χ (v i)) ∧ ∀ w, IsEigAt act x χ w → ∃! c : Fin n → R, IsCombAt x c v w
example {k : Type} [Field k] (act : OAct O G) (x : Sp k ⟶ S) (χ : O →+* k) (n : ℕ) :
    (∃ v : Fin n → (epsAt x ⟶ G), IsEigBasisAt act x χ v) ↔ LieMult act x χ n := Iff.rfl
end Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Sections
variable {S X : Scheme.{0}} {F : Type} [Field F]
def Rule (t : SAB H S) (π : X ⟶ S) (p q : ℕ) : Type 1 :=
  ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), (Fin p → (epsAt (x ≫ π) ⟶ t.G)) → (Fin q → (epsAt (x ≫ π) ⟶ t.G)) → R
def IsFrame (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    {R : Type} [CommRing R] (j : F →+* R) (x : Sp R ⟶ X)
    (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G)) : Prop :=
  x ≫ s = spMap j ∧ Set.range x ⊆ V ∧ IsEigBasisAt t.act (x ≫ π) (j.comp χ) v ∧
    IsEigBasisAt t.act (x ≫ π) (j.comp (χ.comp (H.bar : 𝓞 E →+* 𝓞 E))) w
def IsSection (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    (σ : Rule t π p q) : Prop :=
  (∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (gε : DualNumber R →+* DualNumber R')
      (j : F →+* R) (j' : F →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X) v w v' w',
      (∀ a, gε (algebraMap R _ a) = algebraMap R' _ (g a)) → gε DualNumber.eps = DualNumber.eps →
      IsFrame t π s V χ j x v w → IsFrame t π s V χ j' x' v' w' → x' = spMap g ≫ x →
      (∀ i, (v' i).left = spMap gε ≫ (v i).left) → (∀ i, (w' i).left = spMap gε ≫ (w i).left) →
      σ R' x' v' w' = g (σ R x v w)) ∧
  ∀ (R : Type) [CommRing R] (j : F →+* R) (x : Sp R ⟶ X) v w v' w'
      (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R),
      IsFrame t π s V χ j x v w → IsFrame t π s V χ j x v' w' →
      (∀ i, IsCombAt (x ≫ π) (M i) v (v' i)) → (∀ i, IsCombAt (x ≫ π) (N i) w (w' i)) →
      N.det * σ R x v w = M.det * σ R x v' w'
def NowhereZero (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    (σ : Rule t π p q) : Prop :=
  ∀ (R : Type) [CommRing R] (j : F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V χ j x v w → IsUnit (σ R x v w)
def IsMultiple (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    (σ' : Rule t π p q) (a : F) (σ : Rule t π p q) : Prop :=
  ∀ (R : Type) [CommRing R] (j : F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V χ j x v w →
    σ' R x v w = j a * σ R x v w
example (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) (p q : ℕ) :
    IsSection t π s V χ (p := p) (q := q) (fun _ _ _ _ _ => 0) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp⟩
end Sections
section Homology
def herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)
def IsWedgeCoord {g p q : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (y : Fin q ⊕ Fin p → Fin g → ℂ) (Δ : ℂ) : Prop :=
  ∃ a : Fin q ⊕ Fin p → Fin p → ℂ, (∀ k i, herm Hm (y k - ∑ m, a k m • V m) (V i) = 0) ∧
    Δ = Matrix.det (Matrix.of fun k : Fin q ⊕ Fin p =>
      Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) (y k)) (fun i => a k i))
variable {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
def IsTransport {s s' : Sp ℂ ⟶ Sp B} (o : Obj D l b s) (o' : Obj D l b s') {g g' : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ)
    (φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)) : Prop :=
  (∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ) ∧
    (∀ (a : 𝓞 E) z w, u.ex w = u.ex z ≫ o.t.act.act a → u'.ex (φ w) = u'.ex (φ z) ≫ o'.t.act.act a) ∧
    (∀ z w, (herm Hm' (φ z) (φ w)).im = (herm Hm z w).im) ∧
    (∀ a z, u.ex z = o.eta a → u'.ex (φ z) = o'.eta a) ∧
    ∀ a z, u.ex z = o.etaA a → u'.ex (φ z) = o'.etaA a
def IsVecs {S : Scheme.{0}} {G₀ : Over S} {y₀ : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ}
    (u : HolUnif A L g) (ψ : A.left ⟶ G₀.left) (v : Fin n → (epsAt y₀ ⟶ G₀)) (V : Fin n → Fin g → ℂ) : Prop :=
  ∀ i, ∃ v' : epsR ℂ ⟶ A, v'.left ≫ ψ = (v i).left ∧ u.IsDiff (V i) v'
end Homology
variable {D : Datum H} {l : Level H}
def chi (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F :=
  (τ.comp (algebraMap (𝓞 E) E)).codRestrict c.F (fun a => c.conj τ _)
abbrev toX (Xo : Moduli D l) (c : Coeff l) : Xo.XF c ⟶ Xo.X := pullback.fst _ _
abbrev toF (Xo : Moduli D l) (c : Coeff l) : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
def HasTransport (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ) : Prop :=
  ∀ (y y' : Sp ℂ ⟶ Xo.XF c), y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e →
    Set.range y ⊆ U → Set.range y' ⊆ U →
    ∀ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (o' : Obj D l (baseKA l) (y' ≫ toX Xo c ≫ Xo.s)),
      Nonempty (ObjMap o Xo.univ (y ≫ toX Xo c)) → Nonempty (ObjMap o' Xo.univ (y' ≫ toX Xo c)) →
      ∀ (g g' : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
        (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (κ : u.Λ → ℂ) (κ' : u'.Λ → ℂ),
        u.IsAH Hm κ → u'.IsAH Hm' κ' → ∃ φ, IsTransport o o' u u' Hm Hm' φ
def IsFlatAt (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ)
    (σ : Rule Xo.univ.t (toX Xo c) D.p D.q) (e : c.F →+* ℂ) : Prop :=
  ∀ (y y' : Sp ℂ ⟶ Xo.XF c) v w v' w',
    IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) e y v w →
    IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) e y' v' w' →
    ∀ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (o' : Obj D l (baseKA l) (y' ≫ toX Xo c ≫ Xo.s))
      (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (m' : ObjMap o' Xo.univ (y' ≫ toX Xo c))
      (g g' : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
      (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (κ : u.Λ → ℂ) (κ' : u'.Λ → ℂ)
      (φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ))
      (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (V' : Fin D.p → Fin g' → ℂ) (W' : Fin D.q → Fin g' → ℂ)
      (x : Fin D.q ⊕ Fin D.p → Fin g → ℂ) (Δ Δ' : ℂ),
      u.IsAH Hm κ → u'.IsAH Hm' κ' → IsTransport o o' u u' Hm Hm' φ →
      IsVecs u m.toSABMap.φ v V → IsVecs u m.toSABMap.φ w W →
      IsVecs u' m'.toSABMap.φ v' V' → IsVecs u' m'.toSABMap.φ w' W' →
      IsWedgeCoord Hm V W x Δ → IsWedgeCoord Hm' V' W' (fun k => φ (x k)) Δ' →
      σ ℂ y v w * Δ' = σ ℂ y' v' w' * Δ
section Compact
variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def compactOf (Y : Model Xo c β) (U : Set (Xo.XF c)) : Set (pullback Y.s (spMap β) : Scheme.{0}) :=
  closure (Y.jQ '' U)
def SameVecs (Y : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Xo.XF c) {n : ℕ}
    (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G))
    (vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ pullback.fst Y.s (spMap β)) ⟶ Y.t.G)) : Prop :=
  ∀ i, ∃ v₁ : epsAt x ⟶ Y.oF.t.G, v₁.left ≫ Y.m0.toSABMap.φ = (v i).left ∧ v₁.left ≫ Y.m.φ = (vb i).left
def Restricts (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ)
    (σb : Rule Y.t (pullback.fst Y.s (spMap β)) D.p D.q) (σ : Rule Xo.univ.t (toX Xo c) D.p D.q) : Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c) v w vb wb,
    IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) j x v w →
    IsFrame Y.t (pullback.fst Y.s (spMap β)) (pullback.snd Y.s (spMap β)) (compactOf Y U) (chi c τ) j
      (x ≫ Y.jQ) vb wb →
    SameVecs Y x v vb → SameVecs Y x w wb → σb R (x ≫ Y.jQ) vb wb = σ R x v w
end Compact
def DetLineTrivial : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (U : (Xo.XF c).Opens), IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) →
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (∀ e : c.F →+* ℂ, HasTransport Xo c U e) ∧
      ∃ σ : Rule Xo.univ.t (toX Xo c) D.p D.q,
        IsSection Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) σ ∧
        NowhereZero Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) σ ∧
        (∀ e : c.F →+* ℂ, IsFlatAt Xo c U τ σ e) ∧
        (∀ σ' : Rule Xo.univ.t (toX Xo c) D.p D.q, IsSection Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) σ' →
          (∀ e : c.F →+* ℂ, IsFlatAt Xo c U τ σ' e) →
          ∃! a : c.F, IsMultiple Xo.univ.t (toX Xo c) (toF Xo c) U (chi c τ) σ' a σ) ∧
        ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNormalScheme (pullback Y.s (spMap β)) →
          ∃ σb : Rule Y.t (pullback.fst Y.s (spMap β)) D.p D.q,
            IsSection Y.t (pullback.fst Y.s (spMap β)) (pullback.snd Y.s (spMap β)) (compactOf Y U) (chi c τ) σb ∧
            NowhereZero Y.t (pullback.fst Y.s (spMap β)) (pullback.snd Y.s (spMap β)) (compactOf Y U) (chi c τ) σb ∧
            Restricts Y U τ σb σ ∧
            ∀ σ' : Rule Y.t (pullback.fst Y.s (spMap β)) D.p D.q,
              IsSection Y.t (pullback.fst Y.s (spMap β)) (pullback.snd Y.s (spMap β)) (compactOf Y U) (chi c τ) σ' →
              ∃! a : c.F, IsMultiple Y.t (pullback.fst Y.s (spMap β)) (pullback.snd Y.s (spMap β)) (compactOf Y U)
                (chi c τ) σ' a σb
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm


