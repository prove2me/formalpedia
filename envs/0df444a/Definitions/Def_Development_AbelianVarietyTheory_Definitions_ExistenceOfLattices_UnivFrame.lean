-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
-- name    : Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:06.115499+00:00
-- url     : https://prove2.me/theorems/c82a5be5-1467-4591-9f21-8a0a84aa8527
-- title:
--   Univ Frame
-- statement:
--   Definitions and structural lemmas for Univ Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/UnivFrame.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Frames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Ring
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) {R A : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
def FrameRing (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ) : Prop :=
  (∀ τ, IsUnit (X τ).det) ∧
    ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : R →ₐ[K] T) (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (a : Tˣ),
      (∀ τ, IsUnit (g τ).det) → ∃! k : A →ₐ[K] T, k.comp π = ψ ∧ (∀ τ, (X τ).map k = g τ) ∧ k (s : A) = (a : T)
def TriRing (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ) : Prop :=
  (∀ τ i, IsUnit (X τ i i)) ∧ (∀ τ i j, i < j → X τ i j = 0) ∧
    ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : R →ₐ[K] T) (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (a : Tˣ),
      (∀ τ i, IsUnit (g τ i i)) → (∀ τ i j, i < j → g τ i j = 0) →
      ∃! k : A →ₐ[K] T, k.comp π = ψ ∧ (∀ τ, (X τ).map k = g τ) ∧ k (s : A) = (a : T)
end Ring
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
def TanBasis {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) : Prop :=
  (∀ i, IsTanAt x (v i)) ∧ ∀ w, IsTanAt x w → ∃! a : Fin n → S, IsCombAt x v a w
def SecGen {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) : Prop :=
  ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s.f i
def SecNZ {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) : Prop :=
  ∀ p : Sp S, ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = p ∧ q ∈ (Gx x).basicOpen (s.f i)
def SecBC {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) : Prop :=
  ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
      (pm.appLE _ _ h).hom (scal x a i * s.f i) = s'.f i
def FrChg {S : Type} [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)
    (a : S) (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ∧ (∀ τ i, IsCombAt y.x (y.u τ) (g τ i) (y'.u τ i)) ∧ SecBC (RingHom.id S) a y.x y'.x y.s y'.s
def OpenChart {R : Type} [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) : Prop :=
  IsOpenImmersion j ∧ j ≫ pullback.fst _ _ = y₀.x ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F R)
def UnivFrame {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A] [Algebra c.F A] (y₀ : FrPt Xo c R)
    (π : R →ₐ[c.F] A) (X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (s : Aˣ)
    (u : FrPt Xo c A) : Prop :=
  FrameRing (fun τ => Dw.mult τ) π X s ∧ ∃ u₀ : FrPt Xo c A, FrMap π y₀ u₀ ∧ FrChg X (s : A) u₀ u
end GlobalTheory.Frames


