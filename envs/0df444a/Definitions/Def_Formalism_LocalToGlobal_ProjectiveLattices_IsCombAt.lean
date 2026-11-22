-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:25.298027+00:00
-- url     : https://prove2.me/theorems/7189af7a-500b-4a01-94e8-f41b3b05bbd5
-- title:
--   Is Comb At
-- statement:
--   Definitions and structural lemmas for Is Comb At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsCombAt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Dual
variable {S T : Type} [CommRing S] [CommRing T]
def dualMap (φ : S →+* T) : DualNumber S →+* DualNumber T where
  toFun x := TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
def toΓ (S : Type) [CommRing S] : S →+* Γ(Sp S, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
end Dual
variable (Xo : Moduli Dw l) (c : Coeff l)
def sOf (S : Type) [CommRing S] [Algebra c.F S] : Sp S ⟶ Sp (KA l) :=
  spMap ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)
variable {Xo c}
abbrev tEps {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Over Xo.X :=
  Over.mk (spMap (algebraMap S (DualNumber S)) ≫ x)
def IsTanAt {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  v ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x ∧
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = (1 : Over.mk x ⟶ Xo.univ.t.G).left
variable (c) in

def IsEigAt {S : Type} [CommRing S] [Algebra c.F S] (τ : E →+* ℂ)
    (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  ∀ a : 𝓞 E, v ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ v
def IsCombAt {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ u : Fin m → (tEps x ⟶ Xo.univ.t.G), (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ v i) ∧
    ((List.ofFn u).prod).left = w
abbrev Gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Scheme.{0} := (Over.mk x ⊗ Xo.univ.t.G).left
abbrev PPx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : LB (Gx x) :=
  ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk x)
def scal {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) :
    Γ(Gx x, (PPx x).U i) :=
  ReciprocityTheory.ChartRestriction.G.Out.liftFun Xo.univ.t.G ((PPx x).U i) (T := Over.mk x) (toΓ S a)
variable (Xo c)
structure FrPt (S : Type) [CommRing S] [Algebra c.F S] : Type where
  x : Sp S ⟶ Xo.X
  x_over : x ≫ Xo.s = sOf c S
  u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)
  tan : ∀ τ i, IsTanAt x (u τ i)
  eig : ∀ τ i, IsEigAt c τ (u τ i)
  basis : ∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w
  s : LB.Sec (PPx x)
  gen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s.f i
variable {Xo c}
def FrMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) : Prop :=
  z.x = spMap φ.toRingHom ≫ y.x ∧
    (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧
    ∃ pm : Gx z.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap φ.toRingHom ∧
      ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i), (pm.appLE _ _ h).hom (y.s.f i) = z.s.f i
def FrBor {S : Type} [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ∧
    (∀ τ i, ∃ cf : Fin (Dw.mult τ) → S, cf i = (t (some ⟨τ, i⟩) : S) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt y.x (y.u τ) cf (y'.u τ i)) ∧
    ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
      ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
        (pm.appLE _ _ h).hom (scal y.x (t none : S) i * y.s.f i) = y'.s.f i
variable (Xo c)
abbrev Rul : Type := Rules (K := c.F) (fun S _ _ => FrPt Xo c S)
def sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secW (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n)
def evR (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : S :=
  evalAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f y
end Formalism.L2.Pj


