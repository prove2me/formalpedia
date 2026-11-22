-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
-- name    : Formalism_PeriodIntegrals_FinOrdAd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:27.865497+00:00
-- url     : https://prove2.me/theorems/783dba90-b2d6-487b-b6bc-27e8dcfe2151
-- title:
--   Fin Ord Ad
-- statement:
--   Definitions and structural lemmas for Fin Ord Ad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FinOrdAd.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitKron
import Definitions.Def_Formalism_PeriodIntegrals_PowBddInt
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open NumberField IsDedekindDomain TensorProduct Matrix ComplexOrder
section UnitaryGroups
variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]
def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ
def IsHerm (σ : A →+* A) (J : Matrix ι ι A) : Prop := cT σ J = J
def hform (σ : A →+* A) (J : Matrix ι ι A) (x y : ι → A) : A :=
  ∑ i, ∑ j, σ (x i) * J i j * y j
theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix ι ι A) = 1 := by
  simp [cT]
def UJ (σ : A →+* A) (J : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix ι ι A) * (b : Matrix ι ι A)) * J * ((a : Matrix ι ι A) * (b : Matrix ι ι A))
        = cT σ (b : Matrix ι ι A) * (cT σ (a : Matrix ι ι A) * J * (a : Matrix ι ι A)) *
            (b : Matrix ι ι A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * J * ((g⁻¹ : GL ι A) : Matrix ι ι A)
        = cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * (cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A))
            * ((g⁻¹ : GL ι A) : Matrix ι ι A) := by rw [hg]
      _ = cT σ ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) * J
            * ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
def bc {B : Type} [CommRing B] (φ : A →+* B) : GL ι A →* GL ι B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom
end UnitaryGroups
section Points
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]
def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom
def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom
def UPts (σ : E →ₐ[F] E) (J : Matrix ι ι E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL ι (E ⊗[F] R)) := UJ (sigR σ R) (J.map (inclE (F := F) R))
def IsDef (σ : E →ₐ[F] E) (J : Matrix ι ι E) : Prop :=
  ∀ ι' : F →+* ℝ,
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ 0 < ι' a) ∨
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ ι' a < 0)
@[reducible] def tensTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)
end Points
def FinOrdAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ
def DefPosDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)) ∧
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef)
def TensCpctDen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ e : E, inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) e ∈ C → IsIntegral ℤ ((N : E) * e)
def CpctIntCharpoly : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ),
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ K : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    IsCompact (K : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ γ : GL (Fin k) E, bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ K →
    ∀ i, IsIntegral ℤ ((γ : Matrix (Fin k) (Fin k) E).charpoly.coeff i)
end PI


