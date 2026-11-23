-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:20.243826+00:00
-- url     : https://prove2.me/theorems/7b0435d5-ff2e-4806-80b2-a4a4c040961c
-- title:
--   Final Theorems
-- statement:
--   Definitions and structural lemmas for Final Theorems, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FinalTheorems.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TensorProduct
universe u
namespace ReciprocityTheory.AnForm.R.FinalTheorems
def EffCartier {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}
def Blowup {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  EffCartier (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), EffCartier (I.comap g) → ∃! h : W ⟶ X', h ≫ π = g
def Rsp (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) (x : Fin n → R) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R
def Snc {Y : Scheme.{u}} (D : Y.IdealSheafData) : Prop :=
  ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}
def GeomRegFib (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime] (K : Type u) [Field K] [Algebra P.ResidueField K] [Algebra A K]
    [IsScalarTower A P.ResidueField K], (⊤ : IntermediateField P.ResidueField K).FG →
    IsNoetherianRing (B ⊗[A] K) ∧
      ∀ (Q : Ideal (B ⊗[A] K)) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)
def QERing (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧
  (∀ (P : Ideal A) [P.IsPrime],
    Module.Flat (Localization.AtPrime P)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) ∧
    GeomRegFib (Localization.AtPrime P)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))) ∧
  (∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
    IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)})
def QE (X : Scheme.{u}) : Prop := ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ QERing Γ(X, U.1)
def FFinRes (X : Scheme.{u}) : Prop :=
  ∀ (x : X) (p : ℕ) [Fact p.Prime] [CharP (X.residueField x) p], (frobenius (X.residueField x) p).Finite
def Sing (X : Scheme.{u}) : Set X := {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}
def LogRes (X : Scheme.{u}) (B : TopologicalSpace.Closeds X) : Prop :=
  ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ B ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) ∧
    Snc (Scheme.IdealSheafData.vanishingIdeal
      ⟨π.base ⁻¹' (B : Set X), IsClosed.preimage π.base.hom.continuous B.2⟩)
def GFLogR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogRes X B
def GFLog2R : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ →
      (∀ x ∈ (B : Set X), ringChar (X.residueField x) ≠ 0) → LogRes X B
def GFR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ Sing X ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w))
noncomputable def stalkId {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ (U : X.affineOpens) (hx : x ∈ U.1), Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U)
def LSncAt (X : Scheme.{u}) {q : ℕ} (L : Fin q → TopologicalSpace.Closeds X) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x) ∧
    ∃ (n : ℕ) (r : Fin n → X.presheaf.stalk x) (e : {i : Fin q // x ∈ L i} ↪ Fin n),
      Rsp (X.presheaf.stalk x) n r ∧
        ∀ i : {i : Fin q // x ∈ L i},
          stalkId (Scheme.IdealSheafData.vanishingIdeal (L i.1)) x = Ideal.span {r (e i)}
def CompList {X : Scheme.{u}} (B : Set X) {q : ℕ} (V : Fin q → TopologicalSpace.Closeds X) : Prop :=
  (∀ j, IsIrreducible (V j : Set X)) ∧ (⋃ j, (V j : Set X)) = B ∧ ∀ i j, (V i : Set X) ⊆ V j → i = j
def LocLog0R : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra ℚ A], QERing A →
  ∀ (S : Scheme.{u}) (b : S ⟶ Spec (CommRingCat.of A)) (I : (Spec (CommRingCat.of A)).IdealSheafData),
    Blowup b I → IsReduced S →
    ∀ (B : TopologicalSpace.Closeds S), Sing S ⊆ B → interior (B : Set S) = ∅ →
      b.base ⁻¹' {IsLocalRing.closedPoint A} ⊆ B →
      (∃ E : S.IdealSheafData, EffCartier E ∧ (E.support : Set S) = B) →
    ∀ (q : ℕ) (V : Fin q → TopologicalSpace.Closeds S), CompList (B : Set S) V →
      (∀ x : S, x ∉ b.base ⁻¹' {IsLocalRing.closedPoint A} → LSncAt S V x) →
      ∃ (J : S.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ S),
        (J.support : Set S) ⊆ b.base ⁻¹' {IsLocalRing.closedPoint A} ∧ Blowup π J ∧
          ∃ (r : ℕ) (V' : Fin r → TopologicalSpace.Closeds W), CompList (π.base ⁻¹' (B : Set S)) V' ∧
            ∀ w : W, LSncAt W V' w
def SncAt {Y : Scheme.{u}} (D : Y.IdealSheafData) (y : Y) : Prop :=
  IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}
def LogResSt (X : Scheme.{u}) (B : TopologicalSpace.Closeds X) : Prop :=
  ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ B ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) ∧
    Snc (Scheme.IdealSheafData.vanishingIdeal
      ⟨π.base ⁻¹' (B : Set X), IsClosed.preimage π.base.hom.continuous B.2⟩) ∧
    (∀ x : X, SncAt (Scheme.IdealSheafData.vanishingIdeal B) x →
      ∃ f ∈ nonZeroDivisors (X.presheaf.stalk x), stalkId J x = Ideal.span {f}) ∧
    ∃ U : X.Opens, (U : Set X) = {x : X | SncAt (Scheme.IdealSheafData.vanishingIdeal B) x} ∧ IsIso (π ∣_ U)
def GFLogStR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResSt X B
def GFLog2StR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ →
      (∀ x ∈ (B : Set X), ringChar (X.residueField x) ≠ 0) → LogResSt X B
def GFLogStBR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ →
      (∀ x ∈ (B : Set X), ∀ (p : ℕ) [Fact p.Prime] [CharP (X.residueField x) p],
        (frobenius (X.residueField x) p).Finite) → LogResSt X B
def GFLog2StBR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ →
      (∀ x ∈ (B : Set X), ringChar (X.residueField x) ≠ 0) →
      (∀ x ∈ (B : Set X), ∀ (p : ℕ) [Fact p.Prime] [CharP (X.residueField x) p],
        (frobenius (X.residueField x) p).Finite) → LogResSt X B
end ReciprocityTheory.AnForm.R.FinalTheorems


