-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CocycleMultiplicative
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CocycleMultiplicative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:49.19284+00:00
-- url     : https://prove2.me/theorems/0134b96a-b018-4471-8cf9-1f9590bdfbc5
-- title:
--   Cocycle Multiplicative
-- statement:
--   Definitions and structural lemmas for Cocycle Multiplicative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CocycleMultiplicative.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.cT :
    {A : Type} → [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
    fun {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) ↦ (M.map (⇑σ : A → A)).transpose
theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    (P Q : Matrix n n A) :
    UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (P * Q) = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ Q * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ P := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]
theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (1 : Matrix n n A) = 1 := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {a b : GL n A},
      a ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
          a * b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J a b ha hb
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [Units.val_mul, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑b : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑a : Matrix n n A) * J * (↑a : Matrix n n A)) * (↑b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]
theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A), UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(1 : GL n A) : Matrix n n A) * J * (↑(1 : GL n A) : Matrix n n A) = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one, Matrix.one_mul, Matrix.mul_one]
theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {g : GL n A},
      g ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        g⁻¹ ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  have h1 : (↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) = 1 := by
    rw [← UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul, h1, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A)) * (↑(g⁻¹) : Matrix n n A) := by
        rw [hg]
    _ = (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A)) * J *
        ((↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
    fun {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
        (J : Matrix n n A) ↦
      { carrier := {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J},
        mul_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 A inst n inst_1 inst_2 σ J, one_mem' := UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 σ J,
        inv_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 A inst n inst_1 inst_2 σ J : Subgroup (GL n A) }
noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → (n : ℕ) → Subgroup (GL (Fin n) E) :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (n : ℕ) ↦
      UpperTheory.Reformulated.B.CocycleMultiplicative.UJ (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom (1 : Matrix (Fin n) (Fin n) E)


