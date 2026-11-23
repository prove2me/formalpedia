-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:20.942475+00:00
-- url     : https://prove2.me/theorems/7a5b6aff-fc61-45b5-9888-307b2cbffce2
-- title:
--   Raw Degree Forms
-- statement:
--   Definitions and structural lemmas for Raw Degree Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
structure IsCompleteLocalNormal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop where
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
structure IsAdicNormalPair (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) : Prop where
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete I R
section Points
variable {S : Scheme.{0}} (B : Over S) [GrpObj B]
def laφ {T : Over S} (x y : T ⟶ B) : Fin 4 → (T.left ⟶ B.left) :=
  ![(padd B x y).left, x.left, y.left, (pzero B T).left]
def laε : Fin 4 → ℤ := ![1, -1, -1, 1]
def laDualε : Fin 4 → ℤ := ![-1, 1, 1, -1]
def symφ : Fin 2 → (B.left ⟶ B.left) := ![(GrpObj.inv : B ⟶ B).left, 𝟙 B.left]
def symε : Fin 2 → ℤ := ![1, -1]
def cubeAt {M : RigLB B} (t : CubicalStr B M) {T : Over S} (x y z : T ⟶ B) :
    LB.Gen (LB.LinComb M.L
      (fun k => (lift x (lift y z) : T ⟶ G3 B).left ≫ thφ B (x3 B) k) thε) :=
  LB.pullGen M.L (thφ B (x3 B)) thε t.t (lift x (lift y z) : T ⟶ G3 B).left
end Points
variable (R : Type) [CommRing R] [IsDomain R]
abbrev base : Scheme.{0} := Spec (CommRingCat.of R)
def genPt : Over (base R) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
structure RawDeg where

  P : PolAV (base R)

  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen

  cube : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩

  sym : LB.Gen (LB.LinComb P.L (symφ P.A) symε)
  sym_gen : sym.IsGen

  sym_rig : LB.Gen.Corr P.L _ _ _ _
    (LB.pullGen P.L (symφ P.A) symε sym (eSec P.A)) (LB.oneGen P.L)

  X : Type
  [addCommGroup : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]

  c : X → (𝟙_ (Over (base R)) ⟶ P.A)
  c_add : ∀ χ χ', c (χ + χ') = padd P.A (c χ) (c χ')

  ψ : ∀ χ, LB.Gen (LB.LinComb P.L (K := PUnit)
    (fun _ => (toUnit (genPt R) ≫ c χ).left) (fun _ => -1))
  ψ_gen : ∀ χ, (ψ χ).IsGen
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
namespace RawDeg
variable {R} (D : RawDeg R)
abbrev cT (T : Over (base R)) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ
abbrev cK (χ : D.X) : genPt R ⟶ D.P.A := D.cT (genPt R) χ
theorem cT_add (T : Over (base R)) (χ χ' : D.X) :
    D.cT T (χ + χ') = padd D.P.A (D.cT T χ) (D.cT T χ') := by
  simp only [cT, D.c_add, padd, ← Category.assoc, comp_lift]
def oChi (χ : D.X) : LB D.P.A.left :=
  LB.LinComb D.P.L (laφ D.P.A (D.cT D.P.A χ) (𝟙 D.P.A)) laε
def ψAt (χ : D.X) (i : D.P.L.ι) (V : (genPt R).left.Opens)
    (h : V ≤ (D.cK χ).left ⁻¹ᵁ D.P.L.U i) : Γ((genPt R).left, V)ˣ :=
  res (U := LB.wchart D.P.L (K := PUnit) (fun _ => (D.cK χ).left) (fun _ => i))
    (fun _ hy => Set.mem_iInter.2 fun _ => h hy) ((D.ψ χ).s (fun _ => i))
def rigAt (i : D.P.L.ι) (V : (genPt R).left.Opens)
    (h : V ≤ (pzero D.P.A (genPt R)).left ⁻¹ᵁ D.P.L.U i) : Γ((genPt R).left, V)ˣ :=
  res (U := LB.wchart D.P.L (K := PUnit)
      (fun _ => (toUnit (genPt R)).left ≫ eSec D.P.A) (fun _ => i))
    (fun _ hy => Set.mem_iInter.2 fun _ => h hy)
    ((LB.pullGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig
      (toUnit (genPt R)).left).s (fun _ => i))
def τ (χ χ' : D.X) :
    LB.Gen (LB.LinComb D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) laDualε) where
  s := fun j =>
    D.ψAt (χ + χ') (j 0) _ ((LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 0).trans
      (le_of_eq (congrArg (fun f : genPt R ⟶ D.P.A => f.left ⁻¹ᵁ D.P.L.U (j 0))
        (D.cT_add (genPt R) χ χ').symm))) *
    (D.ψAt χ (j 1) _ (LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 1))⁻¹ *
    (D.ψAt χ' (j 2) _ (LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 2))⁻¹ *
    (D.rigAt (j 3) _ (LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 3))⁻¹
structure PrePt (T : Over (base R)) where

  b : T ⟶ D.P.A

  ev : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (laφ D.P.A (D.cT T χ) b) laDualε)
structure PrePt.IsPt {D : RawDeg R} {T : Over (base R)} (g : D.PrePt T) : Prop where
  gen : ∀ χ, (g.ev χ).IsGen
  mul : ∀ χ χ', LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g.ev (χ + χ'))
      (cubeAt D.P.A D.cube (D.cT T χ) (D.cT T χ') g.b))
    (LB.mulGen D.P.L _ _ _ _ (g.ev χ) (g.ev χ'))
def io (y : D.X) : D.PrePt (genPt R) where
  b := D.cK y
  ev := fun χ => D.τ χ y
def cst (a : R) (U : (𝟙_ (Over (base R))).left.Opens) : Γ((𝟙_ (Over (base R))).left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (base R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a
def lattice (χ : D.X) : LB (𝟙_ (Over (base R))).left :=
  LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
def ψMem (J : Ideal R) (χ : D.X) : Prop :=
  ∃ (m : ℕ) (a : Fin m → R) (s : Fin m → LB.Sec (D.lattice χ)), (∀ n, a n ∈ J) ∧
    ∀ j : PUnit → D.P.L.ι,
      ((D.ψ χ).s j).val =
        ((toUnit (genPt R)).left.appLE ((D.lattice χ).U j)
          (LB.wchart D.P.L (K := PUnit) (fun _ => (D.cK χ).left) j)
          (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)).hom
          (∑ n, cst (a n) _ * (s n).f j)
structure IsDeg (I : Ideal R) : Prop where

  even : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.ψ (-χ))
      (LB.pullGen D.P.L (symφ D.P.A) symε D.sym (D.cK χ).left))
    (D.ψ χ)

  mul_left : ∀ χ₁ χ₂ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.τ (χ₁ + χ₂) χ)
      (cubeAt D.P.A D.cube (D.cK χ₁) (D.cK χ₂) (D.cK χ)))
    (LB.mulGen D.P.L _ _ _ _ (D.τ χ₁ χ) (D.τ χ₂ χ))

  mul_right : ∀ χ χ₁ χ₂, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.τ χ (χ₁ + χ₂))
      (cubeAt D.P.A D.cube (D.cK χ) (D.cK χ₁) (D.cK χ₂)))
    (LB.mulGen D.P.L _ _ _ _ (D.τ χ χ₁) (D.τ χ χ₂))

  mem : ∀ χ, χ ≠ 0 → D.ψMem I χ

  tendsto : ∀ e : ℕ, {χ | ¬ D.ψMem (I ^ e) χ}.Finite
def gAt (f : (genPt R).left ⟶ D.P.A.left) (i i' : D.P.L.ι) (W : (genPt R).left.Opens)
    (h : W ≤ f ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U i')) : Γ((genPt R).left, W)ˣ :=
  res h (pullU f _ (D.P.L.g i i'))
end RawDeg
structure DegData (I : Ideal R) extends RawDeg R where
  isDeg : toRawDeg.IsDeg I
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings


