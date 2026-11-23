-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.281236+00:00
-- url     : https://prove2.me/theorems/761b70b7-9491-4502-976d-3c5668a72059
-- title:
--   Rep Alg
-- statement:
--   Definitions and structural lemmas for Rep Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/RepAlg.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
import Theorems.Thm_UpperTheory_V_Alg_Lift_map_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.Alg.Lift.map_hom


set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
namespace UpperTheory.V.W
structure Det (n : ℕ) (A E : Type) [CommRing A] [Ring E] [Algebra A E] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], B ⊗[A] E →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : B ⊗[A] E),
    D B' (Algebra.TensorProduct.map f (AlgHom.id A E) x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E), D B (b • x) = b ^ n * D B x
namespace Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
def chi (y : E) : A[X] := D.D A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)
def lam (i : ℕ) (y : E) : A := (-1) ^ i * (D.chi y).coeff (n - i)
def tr (y : E) : A := D.lam 1 y
def Kills (y : E) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] E), D.D B (1 + h * (1 ⊗ₜ y)) = 1
def pull {E' : Type} [Ring E'] [Algebra A E'] (φ : E' →ₐ[A] E) : Det n A E' where
  D B _ _ := (D.D B).comp (Algebra.TensorProduct.map (AlgHom.id B B) φ).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (Algebra.TensorProduct.map (AlgHom.id B' B') φ _) = f (D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ x))
    rw [← D.nat]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  homog B _ _ b x := by
    change D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ (b • x)) = b ^ n * D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ x)
    rw [map_smul, D.homog]
end Det
structure GDet (n : ℕ) (A G : Type) [CommRing A] [Group G] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], MonoidAlgebra B G →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : MonoidAlgebra B G),
    D B' (MonoidAlgebra.mapRingHom G (f : B →+* B') x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : MonoidAlgebra B G), D B (b • x) = b ^ n * D B x
namespace GDet
variable {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
@[ext] theorem ext {D D' : GDet n A G} (h : ∀ (B : Type) [CommRing B] [Algebra A B] (x), D.D B x = D'.D B x) : D = D' := by
  cases D; cases D'; congr; funext B _ _; exact MonoidHom.ext (h B)
def map {A' : Type} [CommRing A'] (f : A →+* A') : GDet n A' G where
  D B _ _ := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.D B
  nat B B' _ _ _ _ g x :=
    letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    letI : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
    D.nat B B' { (g : B →+* B') with commutes' := fun a => g.commutes (f a) } x
  homog B _ _ b x := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.homog B b x
def comap {H : Type} [Group H] (φ : H →* G) : GDet n A H where
  D B _ _ := (D.D B).comp (MonoidAlgebra.mapDomainRingHom B φ).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (MonoidAlgebra.mapDomainRingHom B' φ _) = f (D.D B (MonoidAlgebra.mapDomainRingHom B φ x))
    rw [← D.nat]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp
  homog B _ _ b x := by
    change D.D B (MonoidAlgebra.mapDomainAlgHom B B φ (b • x)) = b ^ n * D.D B (MonoidAlgebra.mapDomainAlgHom B B φ x)
    rw [map_smul, D.homog]
def repAlg {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι A) (B : Type) [CommRing B] [Algebra A B] :
    MonoidAlgebra B G →ₐ[B] Matrix ι ι B :=
  MonoidAlgebra.lift B (Matrix ι ι B) G ((RingHom.mapMatrix (algebraMap A B)).toMonoidHom.comp ρ)
def ofRep (ρ : G →* Matrix (Fin n) (Fin n) A) : GDet n A G where
  D B _ _ := Matrix.detMonoidHom.comp (repAlg ρ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (repAlg ρ B' _).det = f (repAlg ρ B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => ext i j; simp [repAlg]
  homog B _ _ b x := by
    change (repAlg ρ B (b • x)).det = b ^ n * (repAlg ρ B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]
def chi (y : MonoidAlgebra A G) : A[X] := D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
def lam (i : ℕ) (y : MonoidAlgebra A G) : A := (-1) ^ i * (D.chi y).coeff (n - i)
def tr (y : MonoidAlgebra A G) : A := D.lam 1 y
def Kills (y : MonoidAlgebra A G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (h : MonoidAlgebra B G),
    D.D B (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) = 1
def gen {m : ℕ} (y : Fin m → MonoidAlgebra A G) : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
  ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) A) • MonoidAlgebra.mapRingHom G MvPolynomial.C (y j)
def CH : Set (MonoidAlgebra A G) :=
  {z | ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ), ∀ g : G,
    z.coeff g = MvPolynomial.coeff β
      ((Polynomial.aeval (gen y) ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (gen y))).coeff g)}
variable [TopologicalSpace G]
def IsCont (I : Ideal A) : Prop := ∀ i, Alg.AdicCont I fun g : G => D.lam i (MonoidAlgebra.single g 1)
end GDet
def closureIdeal {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A) (S : Set (MonoidAlgebra A G)) :
    TwoSidedIdeal (MonoidAlgebra A G) :=
  ⨅ (N : ℕ) (H : OpenNormalSubgroup G), TwoSidedIdeal.span
    (S ∪ {z | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪ {z | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1})
example (A G : Type) [CommRing A] [Group G] (n : ℕ) : GDet n A G := GDet.ofRep 1
end UpperTheory.V.W


