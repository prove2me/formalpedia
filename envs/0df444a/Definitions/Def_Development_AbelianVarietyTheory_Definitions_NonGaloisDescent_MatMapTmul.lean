-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:46.806089+00:00
-- url     : https://prove2.me/theorems/869bda1d-5cc4-42f9-99ff-dc8828af5644
-- title:
--   Mat Map Tmul
-- statement:
--   Definitions and structural lemmas for Mat Map Tmul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MatMapTmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
namespace GlobalTheory.Pat
namespace Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
def val (y : E) : A := D.D A (1 ⊗ₜ y)
def chiAt (B : Type) [CommRing B] [Algebra A B] (x : B ⊗[A] E) : B[X] :=
  D.D B[X] (X ⊗ₜ 1 - Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B B[X]) (AlgHom.id A E) x)
def IsCH : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (x : B ⊗[A] E), Polynomial.aeval x (D.chiAt B x) = 0
def Over {C E' : Type} [CommRing C] [Ring E'] [Algebra C E'] (D' : Det n C E') (φ : A →+* C)
    (π : E →+* E') : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra C B], (algebraMap C B).comp φ = algebraMap A B →
    ∀ (m : ℕ) (b : Fin m → B) (x : Fin m → E),
      D.D B (∑ i, b i ⊗ₜ[A] x i) = D'.D B (∑ i, b i ⊗ₜ[C] π (x i))
def HasRank (e : E) (r : ℕ) : Prop := D.D A[X] (1 ⊗ₜ (1 - e) + X ⊗ₜ e) = X ^ r
def grpMap {G : Type} [Group G] (A : Type) [CommRing A] [Algebra A E] (ρ : G →* E) (B : Type) [CommRing B]
    [Algebra A B] : MonoidAlgebra B G →ₐ[B] B ⊗[A] E :=
  MonoidAlgebra.lift B (B ⊗[A] E) G
    ((Algebra.TensorProduct.includeRight : E →ₐ[A] B ⊗[A] E).toMonoidHom.comp ρ)
def toG {G : Type} [Group G] (ρ : G →* E) : GDet n A G where
  D B _ _ := (D.D B).comp (grpMap A ρ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (grpMap A ρ B' _) = f (D.D B (grpMap A ρ B x))
    rw [← D.nat]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp [grpMap, TensorProduct.smul_tmul']
  homog B _ _ b x := by
    change D.D B (grpMap A ρ B (b • x)) = b ^ n * D.D B (grpMap A ρ B x)
    rw [map_smul, D.homog]
def matMap (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] Matrix (Fin n) (Fin n) A →ₐ[B] Matrix (Fin n) (Fin n) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) ((Algebra.ofId A B).mapMatrix)
    (fun b _ => Algebra.commutes b _)
theorem matMap_tmul (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B)
    (M : Matrix (Fin n) (Fin n) A) : matMap n A B (b ⊗ₜ M) = b • M.map (algebraMap A B) := by
  have h : matMap n A B (b ⊗ₜ M) =
      algebraMap B (Matrix (Fin n) (Fin n) B) b * M.map (algebraMap A B) :=
    Algebra.TensorProduct.lift_tmul (Algebra.ofId B _) ((Algebra.ofId A B).mapMatrix)
      (fun b _ => Algebra.commutes b _) b M
  rw [h, ← Algebra.smul_def]
def mat (n : ℕ) (A : Type) [CommRing A] : Det n A (Matrix (Fin n) (Fin n) A) where
  D B _ _ := Matrix.detMonoidHom.comp (matMap n A B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (matMap n A B' _).det = f (matMap n A B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b M =>
      rw [Algebra.TensorProduct.map_tmul, matMap_tmul, matMap_tmul]
      ext i j
      simp
  homog B _ _ b x := by
    change (matMap n A B (b • x)).det = b ^ n * (matMap n A B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]
end Det
def qOf {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing B] [IsLocalRing B]
    (S : Set (MonoidAlgebra B Γ)) {C : Type} [CommRing C] (φ : B →+* C) : Γ →* QAlg S φ :=
  ((TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ φ ''
    (closureIdeal (maximalIdeal B) S : Set (MonoidAlgebra B Γ)))).ringCon.mk').toMonoidHom.comp
    (MonoidAlgebra.of C Γ)
def lagIdem {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (M : E) (a : ι → R) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    Polynomial.aeval M (∏ j ∈ Finset.univ.erase i, (X - C (a j)))
def charExt {R Γ : Type} [CommRing R] [Group Γ] (ψ : Γ →* Rˣ) : MonoidAlgebra R Γ →ₐ[R] R :=
  MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp ψ)
def GDet.coef {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (α : G →₀ ℕ) : A :=
  MvPolynomial.coeff α (D.D (MvPolynomial G A)
    (∑ g ∈ α.support, MonoidAlgebra.single g (MvPolynomial.X g)))
end GlobalTheory.Pat


