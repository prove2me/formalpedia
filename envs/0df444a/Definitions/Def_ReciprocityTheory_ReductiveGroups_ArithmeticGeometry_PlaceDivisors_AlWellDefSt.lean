-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:22.410575+00:00
-- url     : https://prove2.me/theorems/770c2131-8772-45de-87fd-f4f4d64be306
-- title:
--   Al Well Def St
-- statement:
--   Definitions and structural lemmas for Al Well Def St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/AlWellDefSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Valuation.Integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace ReciprocityTheory.ChartRestriction.G.Pdiv
open ReciprocityTheory.ChartRestriction.G.Semi
section Points
variable (O : Type) [CommRing O]
abbrev specO (R : Type) [CommRing R] [Algebra O R] : Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap O R)))
variable {O}
def ptMap {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') : specO O R' ⟶ specO O R :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact φ.commutes a)
def dualBC {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') : DualNumber R →ₐ[O] DualNumber R' :=
  TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom O R' R').comp φ)
    (((TrivSqZeroExt.inrHom R' R').restrictScalars O).comp φ.toLinearMap)
    (fun x y => by simp)
    (fun r x => by ext <;> simp [mul_comm])
    (fun r x => by ext <;> simp [mul_comm])
def dualScale (a : O) : DualNumber O →ₐ[O] DualNumber O :=
  TrivSqZeroExt.map (a • LinearMap.id)
def unitOf {R : Type} [CommRing R] [Algebra O R] (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    Rˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom
    (res (fun x _ => show w.left.base x ∈ (⊤ : (Gm (Spec (CommRingCat.of O))).left.Opens)
        from trivial)
      (pullU w.left ⊤ (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1))))
end Points
section Tangent
variable {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
def LieG : Type :=
  {x : specO O (DualNumber O) ⟶ G //
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G]}
def omega : Submodule O (LieG G → O) where
  carrier := {f | (∀ (x y : LieG G) (h : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
        toUnit (specO O O) ≫ η[G]), f ⟨x.1 * y.1, h⟩ = f x + f y) ∧
      (∀ (a : O) (x : LieG G) (h : ptMap (TrivSqZeroExt.fstHom O O O) ≫
        (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G]),
        f ⟨ptMap (dualScale a) ≫ x.1, h⟩ = a * f x)}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun x y h => by
        show f _ + g _ = (f x + g x) + (f y + g y)
        rw [hf1 x y h, hg1 x y h]; ring,
      fun a x h => by
        show f _ + g _ = a * (f x + g x)
        rw [hf2 a x h, hg2 a x h]; ring⟩
  zero_mem' := ⟨fun _ _ _ => show (0 : O) = 0 + 0 by simp,
    fun a _ _ => show (0 : O) = a * 0 by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨fun x y h => by
        show c * f _ = c * f x + c * f y
        rw [hf1 x y h]; ring,
      fun a x h => by
        show c * f _ = a * (c * f x)
        rw [hf2 a x h]; ring⟩
def IsCharTors (N : ℕ) (f : torsion G N ⟶ Gm (Spec (CommRingCat.of O))) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of O))) (x y z : T ⟶ torsion G N),
    z ≫ torsion.ι G N = (x ≫ torsion.ι G N) * (y ≫ torsion.ι G N) →
      z ≫ f = (x ≫ f) * (y ≫ f)
variable (p : ℕ)
structure Tv where

  χ : ∀ n : ℕ, torsion G (p ^ n) ⟶ Gm (Spec (CommRingCat.of O))
  isChar : ∀ n, IsCharTors G (p ^ n) (χ n)
  compat : ∀ (n : ℕ) (T : Over (Spec (CommRingCat.of O))) (x : T ⟶ torsion G (p ^ n))
    (y : T ⟶ torsion G (p ^ (n + 1))), x ≫ torsion.ι G (p ^ n) = y ≫ torsion.ι G (p ^ (n + 1)) →
      x ≫ χ n = y ≫ χ (n + 1)
variable {G p}
def IsAl (χ : Tv G p) (f : LieG G → O) : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R], (p : R) ^ n = 0 →
    ∀ (x : LieG G) (w : specO O (DualNumber R) ⟶ torsion G (p ^ n)),
      w ≫ torsion.ι G (p ^ n) = ptMap (dualBC (Algebra.ofId O R)) ≫ x.1 →
        (unitOf (w ≫ χ.χ n) : DualNumber R) =
          TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R (f x))
variable (G p)
def htSpan : Submodule O (LieG G → O) :=
  Submodule.span O {f | f ∈ omega G ∧ ∃ χ : Tv G p, IsAl χ f}
end Tangent
section Statements
def HTChar (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] : Prop :=
  ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (p : C) →
    ∀ f ∈ omega G, c • f ∈ htSpan G p
def AlWellDefSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
      ∀ χ : Tv G p, ∃! f : LieG G → O, f ∈ omega G ∧ IsAl χ f
def AlNatSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (O : Type) [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (a : G ⟶ G),
    IsMonHom a → ∀ (χ χa : Tv G p) (f : LieG G → O),
      (∀ (n : ℕ) (T : Over (Spec (CommRingCat.of O))) (x y : T ⟶ torsion G (p ^ n)),
        x ≫ torsion.ι G (p ^ n) ≫ a = y ≫ torsion.ι G (p ^ n) → x ≫ χa.χ n = y ≫ χ.χ n) →
      IsAl χ f →
      ∀ (da : LieG G → LieG G), (∀ x, (da x).1 = x.1 ≫ a) → IsAl χa (f ∘ da)
def StBad (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (E : SplitExt (Spec (CommRingCat.of O))) (G : Over (Spec (CommRingCat.of O))) [GrpObj G],
      E.IsGt G → HTChar p v E.B → HTChar p v G
end Statements
end ReciprocityTheory.ChartRestriction.G.Pdiv


