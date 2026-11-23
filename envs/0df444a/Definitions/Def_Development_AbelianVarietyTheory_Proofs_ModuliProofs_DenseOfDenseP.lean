-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:11.857827+00:00
-- url     : https://prove2.me/theorems/7b6c39a2-17d0-43bc-bfb4-8bfe3b53c9be
-- title:
--   Dense Of Dense P
-- statement:
--   Definitions and structural lemmas for Dense Of Dense P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DenseOfDenseP.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.NearBuild
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']
abbrev loc (f : R) : R →+* Localization.Away f := algebraMap R (Localization.Away f)
section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
def Good {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) : Prop :=
  s = spMap x ≫ spMap β ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) (fun a => x (v a))
def Den (q₀ : Ideal R) : Prop := DenseP (objPrimes b Mat κ β v) ∧ q₀ ∈ objPrimes b Mat κ β v
def Concl : Prop :=
  ∃ t : TObj g (N' ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → TMap t' t (spMap x)
def NearC (q₀ : Ideal R) : Prop :=
  ∃ f : R, f ∉ q₀ ∧ Concl b Mat κ ((loc f).comp β) (fun a => loc f (v a))
def FibData (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) {Hh : Type} (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ)
    (d : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t →
    ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
      (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)), t.Emb m (Over.mk (𝟙 _)) σ ∧
      ProjRep I (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧
      CutBy I Q d (fun h a => x (p (hh h) a)) ∧
      ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N')).left (fun a => x (p h a))
end
def Fib {b : TBase o (N' ^ 2)} (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
    (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z.left) : Prop :=
  IsPullback φ t.A.hom Z.hom (spMap x) ∧
    (∃ σ, t.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left)
      (w : Ix g (N' ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w) ∧
    LBIso (lbPow t.L (m ^ 2)) (M.pull φ) ∧ ∀ h, (t.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left
section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
  (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z))
def Fam : Prop :=
  (∃ (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) R)) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R),
    ProjRep I Z.hom M th ∧ ∀ h, SecCoord M th (sc h).left (p h)) ∧ Flat Z.hom ∧
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t → ∃ φ, Fib m M th sc x t φ
def AddOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (mu : Z' ⊗ Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z' ⊗ Z').left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ
def EndOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (i : Option J) (F : Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
def AddAt (mu : Z ⊗ Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ
def EndAt (i : Option J) (F : Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
end
def Lab (k : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) : Prop :=
  (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ k = 1) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 →
      ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ Q i)
        (fun i => (c i).val) = y
def GLies {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (y : S' ⟶ S) {s : S' ⟶ Sp o} (t : TObj g (N' ^ 2) J b s)
    (ψ : t.A.left ⟶ A.left) : Prop :=
  IsGrpPullback t.A A y ψ ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ N').left ≫ ψ = y ≫ (Q i).left
section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
def GrpFam (m : ℕ) (A : Over (Sp R)) [GrpObj A] (M : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ M.IsLB ∧ Out.RelAmple A M ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso (lbPow t.L (m ^ 2)) (M.pull ψ)
def PolFam (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧
    Out.RelAmple A L ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso t.L (L.pull ψ)
variable {b Mat κ β v}
end
end GlobalTheory.ZM.NearBuild
end


