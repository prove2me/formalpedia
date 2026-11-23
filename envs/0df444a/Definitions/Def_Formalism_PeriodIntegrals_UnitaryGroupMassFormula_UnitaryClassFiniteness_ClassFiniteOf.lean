-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:31.887949+00:00
-- url     : https://prove2.me/theorems/20277f6a-70fb-462b-ac52-b819b14ee42b
-- title:
--   Class Finite Of
-- statement:
--   Definitions and structural lemmas for Class Finite Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/ClassFiniteOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct ComplexOrder
namespace PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
def SigPos : Prop :=
  ∀ (M : ℕ) (A : Matrix (Fin M) (Fin M) ℂ), HasSignature A M 0 → A.PosDef
def AdelBounds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ D T c0 : ℕ, 0 < D ∧ 0 < T ∧ 0 < c0 ∧ ∀ h : HA (AF F) σ J,
      (∀ x ∈ abelian₂ σ J L h, ∀ e : E, IsIntegral ℤ e → ((c0 : E) * e) • x ∈ abelian₂ σ J L h) ∧
      (∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : E) * e) ∈ abelian₂ σ J L h) ∧
      (∀ x ∈ abelian₂ σ J L h, ∀ y ∈ abelian₂ σ J L h,
        IsIntegral ℤ ((D : E) * PI.HermLatFin.herm (σ : E →+* E) J x y)) ∧
      (∀ y, (∀ x ∈ abelian₂ σ J L h, IsIntegral ℤ ((D : E) * PI.HermLatFin.herm (σ : E →+* E) J x y)) →
        (T : E) • y ∈ abelian₂ σ J L h)
def LatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (D T c0 : ℕ),
    (∀ (τ : E →+* ℂ) (a : E), τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) → 0 < D → 0 < T → 0 < c0 →
    ∃ S : Set (Set (Fin M → E)), S.Finite ∧ ∀ Λ : AddSubgroup (Fin M → E),
      (∀ x ∈ Λ, ∀ e : E, IsIntegral ℤ e → ((c0 : E) * e) • x ∈ Λ) →
      (∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : E) * e) ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((D : E) * PI.HermLatFin.herm σ J x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ ((D : E) * PI.HermLatFin.herm σ J x y)) → (T : E) • y ∈ Λ) →
      ∃ s ∈ S, ∃ g : UJ σ J, (Λ : Set (Fin M → E)) =
        (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' s
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def LamG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) (h : HA (AF F) σ J) :
    AddSubgroup (Fin M → E) where
  carrier := abelian₂ σ J L h
  add_mem' {x y} hx hy := by
    show (finMat σ J h⁻¹).mulVec (vinc (x + y)) ∈ latHat F E L
    have : vinc (F := F) (x + y) = vinc x + vinc y := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_add]
    exact add_mem hx hy
  zero_mem' := by
    show (finMat σ J h⁻¹).mulVec (vinc 0) ∈ latHat F E L
    have : vinc (F := F) (0 : Fin M → E) = 0 := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_zero]
    exact zero_mem _
  neg_mem' {x} hx := by
    show (finMat σ J h⁻¹).mulVec (vinc (-x)) ∈ latHat F E L
    have : vinc (F := F) (-x) = -vinc x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_neg]
    exact neg_mem hx
end PI.UnitaryGroupMassFormula.UJClassFin


