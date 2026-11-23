-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
-- name    : Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:33.434697+00:00
-- url     : https://prove2.me/theorems/423f2a7d-ed0b-4334-b2ad-46d08a096469
-- title:
--   Is Fin Flat Sub
-- statement:
--   Definitions and structural lemmas for Is Fin Flat Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/IsFinFlatSub.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsTight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_StepOrderRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GR
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
structure TorsRep (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (p : ℕ) where

  A : Type
  [cr : CommRing A]
  [alg : Algebra R A]
  free : Module.Free R A
  fin : Module.Finite R A

  y : sp (R₀ := R) A ⟶ G
  y_p : y ^ p = 1
  univ : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ^ p = 1 →
    ∃! φ : A →ₐ[R] S, spMap φ ≫ y = z
attribute [instance] TorsRep.cr TorsRep.alg
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ}
variable (G p) in

structure IsTorsPts {N : Type} [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)) : Prop where
  inj : Function.Injective pt
  add : ∀ x y, pt (x + y) = pt x * pt y
  range : ∀ z, z ^ p = 1 ↔ ∃ x, pt x = z
def torsFun (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) {N : Type}
    (pt : N → (sp (R₀ := R) R ⟶ G)) : Submodule R (N → C) where
  carrier := {f | ∃ a : T.A, ∀ x (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → f x = algebraMap R C (φ a)}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, fun x φ h => by simp [ha x φ h, hb x φ h]⟩
  zero_mem' := ⟨0, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    exact ⟨c • a, fun x φ h => by simp [ha x φ h, Algebra.smul_def]⟩
def vanIdeal (T : TorsRep G p) {N : Type} (pt : N → (sp (R₀ := R) R ⟶ G)) (K : Set N) : Ideal T.A where
  carrier := {a | ∀ k ∈ K, ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0}
  add_mem' := by
    intro a b ha hb k hk φ h
    simp [ha k hk φ h, hb k hk φ h]
  zero_mem' := fun _ _ _ _ => by simp
  smul_mem' := by
    intro c a ha k hk φ h
    simp [ha k hk φ h]
variable (G) in

structure IsFinFlatSub (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ G) : Prop where
  proj : Module.Projective R B
  fin : Module.Finite R B
  mono : ∀ (S : Type) [CommRing S] [Algebra R S] (φ φ' : B →ₐ[R] S), spMap φ ≫ h = spMap φ' ≫ h → φ = φ'
  one : ∀ (S : Type) [CommRing S] [Algebra R S], ∃ φ : B →ₐ[R] S, spMap φ ≫ h = 1
  mul : ∀ (S : Type) [CommRing S] [Algebra R S] (φ φ' : B →ₐ[R] S),
    ∃ χ : B →ₐ[R] S, spMap χ ≫ h = (spMap φ ≫ h) * (spMap φ' ≫ h)
  inv : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : B →ₐ[R] S),
    ∃ χ : B →ₐ[R] S, (spMap χ ≫ h) * (spMap φ ≫ h) = 1
def tens {C : Type} [Field C] [Algebra R C] {X Y : Type} (M : Submodule R (X → C))
    (M' : Submodule R (Y → C)) : Submodule R (X × Y → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M', F = fun z => g z.1 * h z.2}
def IsAbFactor (p : ℕ) {C : Type} [Field C] [Algebra R C] {N : Type} [AddCommGroup N]
    (M : Submodule R (N → C)) : Prop :=
  ∃ (A : Over (Spec (CommRingCat.of R))) (_ : GrpObj A) (L : LB A.left), IsAbelianScheme A ∧ L.IsLB ∧
    Out.RelAmple A L ∧ ∃ (T : TorsRep A p) (N' : Type) (_ : AddCommGroup N')
      (pt : N' → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt ∧
      ∃ (i : N →+ N') (π : N' →+ N), (∀ x, π (i x) = x) ∧
        (∀ g ∈ torsFun C T pt, (fun x => g (i (π x))) ∈ torsFun C T pt) ∧
        M = (torsFun C T pt).map (LinearMap.funLeft R C (i : N → N'))
end GlobalTheory.CompanionTheory.Ar.GR


