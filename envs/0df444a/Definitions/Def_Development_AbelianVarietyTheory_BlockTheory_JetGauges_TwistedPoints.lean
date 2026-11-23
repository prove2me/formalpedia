-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_TwistedPoints
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_TwistedPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:24.953769+00:00
-- url     : https://prove2.me/theorems/73fbe110-45bb-4c50-be14-959fe8d6fc6e
-- title:
--   Twisted Points
-- statement:
--   Definitions and structural lemmas for Twisted Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/TwistedPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedPoints
attribute [local instance] Over.cartesianMonoidalCategory
def constFun {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (U : Y.Opens) (a : A) :
    Γ(Y, U) :=
  rs (le_top : U ≤ ⊤) (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
def IsSecBasis {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (N : LB Y)
    {n : ℕ} (s : Fin n → LB.Sec N) : Prop :=
  ∀ t : LB.Sec N, ∃! a : Fin n → A, ∀ j : N.ι, t.f j = ∑ i, constFun p (N.U j) (a i) * (s i).f j
abbrev powLB {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))
def nonvanishing {X : Scheme.{0}} {N : LB X} (s : LB.Sec N) : X.Opens :=
  ⨆ j, X.basicOpen (s.f j)
def IsAmple {X : Scheme.{0}} (L : LB X) : Prop :=
  CompactSpace X ∧
    ∀ x : X, ∃ (n : ℕ) (s : LB.Sec (powLB L n)), 1 ≤ n ∧ x ∈ nonvanishing s ∧ IsAffineOpen (nonvanishing s)
section Group
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]
def IsAbelianOfDim (g : ℕ) : Prop :=
  SmoothOfRelativeDimension g B.hom ∧ IsProper B.hom ∧ GeometricallyConnected B.hom
def IsSymmetric (L : LB B.left) : Prop :=
  ∃ t : LB.Iso (L.pull (GrpObj.inv (X := B)).left) L, t.IsGen
def HasTrivialKernel (L : LB B.left) : Prop :=
  ∀ (T : Over S) (x : T ⟶ B),
    (∃ t : LB.Gen (cubeLB B (T := T ⊗ B) ![fst T B ≫ x, snd T B] L), t.IsGen) → x = pzero B T
abbrev TwIdx : Type := PUnit.{1} ⊕ ULift.{0} (Finset (Fin 2))
def twPts (c : 𝟙_ (Over S) ⟶ B) : Fin 2 → (B ⟶ B) := ![toUnit B ≫ c, 𝟙 B]
def twMap (c : 𝟙_ (Over S) ⟶ B) : TwIdx → (B.left ⟶ B.left) :=
  Sum.elim (fun _ => 𝟙 B.left) (fun I => (psum B (twPts B c) I.down).left)
def twExp (k : ℕ) : TwIdx → ℤ :=
  Sum.elim (fun _ => (k : ℤ)) (fun I => (-1) ^ (2 - I.down.card))
abbrev twLB (M : LB B.left) (c : 𝟙_ (Over S) ⟶ B) (k : ℕ) : LB B.left :=
  LB.LinComb M (twMap B c) (twExp k)
end Group
def HasStableBasis {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B]
    (M : LB B.left) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (k n : ℕ) : Prop :=
  ∃ s : Fin n → LB.Sec (twLB B M c k),
    IsSecBasis B.hom (twLB B M c k) s ∧
    ∀ (R' : Type) [CommRing R'] (f : R →+* R') (B' : Scheme.{0}) (h : B' ⟶ B.left)
      (p : B' ⟶ Spec (CommRingCat.of R')),
      IsPullback h p B.hom (Spec.map (CommRingCat.ofHom f)) →
      IsSecBasis p (LB.LinComb M (fun i => h ≫ twMap B c i) (twExp k))
        (fun i => pullSec M (twMap B c) (twExp k) (s i) h)
def TwistedSectionsBaseChange : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (g : ℕ) (M : RigLB B),
    IsAbelianOfDim B g → IsSymmetric B M.L → IsAmple M.L → HasTrivialKernel B M.L →
    ∀ (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (k : ℕ), 1 ≤ k → HasStableBasis B M.L c k (k ^ g)
example {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (c : 𝟙_ (Over S) ⟶ B) (k : ℕ) :
    LB.LinComb M (fun I => twMap B c (Sum.inr I)) (fun I => twExp k (Sum.inr I)) = cubeLB B (twPts B c) M := rfl
example {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B]
    (M : LB B.left) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (k n : ℕ) (H : HasStableBasis B M c k n)
    (R' : Type) [CommRing R'] (f : R →+* R') (B' : Scheme.{0}) (h : B' ⟶ B.left)
    (p : B' ⟶ Spec (CommRingCat.of R')) (sq : IsPullback h p B.hom (Spec.map (CommRingCat.ofHom f)))
    (t : LB.Sec (LB.LinComb M (fun i => h ≫ twMap B c i) (twExp k))) :
    ∃ (s : Fin n → LB.Sec (twLB B M c k)) (a : Fin n → R'), ∀ j,
      t.f j = ∑ i, constFun p _ (a i) * (pullSec M (twMap B c) (twExp k) (s i) h).f j := by
  obtain ⟨s, -, hs⟩ := H
  obtain ⟨a, ha, -⟩ := hs R' f B' h p sq t
  exact ⟨s, a, ha⟩
end GlobalTheory.IndefiniteRowSideFullHecke.TwistedPoints


