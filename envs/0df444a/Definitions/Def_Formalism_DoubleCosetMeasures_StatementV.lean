-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- name    : Formalism_DoubleCosetMeasures_StatementV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:02.003912+00:00
-- url     : https://prove2.me/theorems/82ea1377-a016-447d-8c39-af9d9f9bb184
-- title:
--   Statement V
-- statement:
--   Definitions and structural lemmas for Statement V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/StatementV.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace Formalism.DoubleCosetMeasures
section Int
variable {F : Type} [Field F]
def intMat (O : Subring F) (n a : ℕ) : Set (Matrix (Fin n) (Fin a) F) := {y | ∀ i j, y i j ∈ O}
theorem isInt_mul' (O : Subring F) {a : ℕ} {x y : Matrix (Fin a) (Fin a) F} (hx : IsInt O x)
    (hy : IsInt O y) : IsInt O (x * y) := fun i j => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hx i k) (hy k j)
def GLint (O : Subring F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | IsInt O (g : Matrix (Fin a) (Fin a) F) ∧
    IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)}
  one_mem' := by
    constructor <;> intro i j <;> by_cases h : i = j <;> simp [h, O.one_mem, O.zero_mem]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using isInt_mul' O hx hy, ?_⟩
    simpa [_root_.mul_inv_rev] using isInt_mul' O hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨by simpa using hx', by simpa using hx⟩
def congSub (O : Subring F) (ϖ : F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | g ∈ GLint O a ∧ IsInt O (ϖ⁻¹ • ((g : Matrix (Fin a) (Fin a) F) - 1))}
  one_mem' := ⟨(GLint O a).one_mem, fun i j => by simp [O.zero_mem]⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨(GLint O a).mul_mem hx hy, ?_⟩
    have e : ϖ⁻¹ • (((x * y : GL (Fin a) F)) - 1 : Matrix (Fin a) (Fin a) F) =
        (ϖ⁻¹ • ((x : Matrix (Fin a) (Fin a) F) - 1)) * (y : Matrix (Fin a) (Fin a) F) +
          ϖ⁻¹ • ((y : Matrix (Fin a) (Fin a) F) - 1) := by
      simp only [Units.val_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, ← smul_add]
      congr 1; abel
    rw [e]; intro i j
    exact O.add_mem (isInt_mul' O hx1 hy.1 i j) (hy1 i j)
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    refine ⟨(GLint O a).inv_mem hx, ?_⟩
    have e : ϖ⁻¹ • (((x⁻¹ : GL (Fin a) F)) - 1 : Matrix (Fin a) (Fin a) F) =
        -(((x⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) *
          (ϖ⁻¹ • ((x : Matrix (Fin a) (Fin a) F) - 1))) := by
      rw [Matrix.mul_smul, Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one, ← smul_neg, neg_sub]
    rw [e]; intro i j
    simpa using O.neg_mem (isInt_mul' O hx.2 hx1 i j)
abbrev kF (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) : Type := O ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : O)}
end Int
def IsLocalAt {F : Type} [Field F] (O : Subring F) (ϖ : F) : Prop :=
  ϖ⁻¹ ∉ O ∧ ∀ x ∈ O, (∀ o ∈ O, x ≠ ϖ * o) → x⁻¹ ∈ O
def GLRed : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → IsLocalAt O ϖ →
    Finite (kF O ϖ hϖ) → ∀ a : ℕ,
      Nat.card ((GLint O a) ⧸ (congSub O ϖ a).subgroupOf (GLint O a)) =
        Nat.card (GL (Fin a) (kF O ϖ hϖ))
def VolJ : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] (O : Subring F),
    IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → IsLocalAt O ϖ →
    Finite (kF O ϖ hϖ) → ∀ (a : ℕ) (μ : Measure (GL (Fin a) F)) [μ.IsMulLeftInvariant]
      (J' : Subgroup (GL (Fin a) F)), congSub O ϖ a ≤ J' → J' ≤ GLint O a →
      μ (J' : Set (GL (Fin a) F)) * (Nat.card (GL (Fin a) (kF O ϖ hϖ)) : ENNReal) =
        (Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') : ENNReal) *
          μ (GLint O a : Set (GL (Fin a) F))
def VolII : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
    [BorelSpace F] (O : Subring F), IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 →
    Finite (kF O ϖ hϖ) → ∀ (n a : ℕ) (ν : Measure (Matrix (Fin n) (Fin a) F))
      [ν.IsAddLeftInvariant],
      ν (IIset O ϖ) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (n * a) = ν (intMat O n a)
def VolJadd : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
    [BorelSpace F] (O : Subring F), IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 →
    IsLocalAt O ϖ → Finite (kF O ϖ hϖ) → ∀ (a : ℕ) (ν : Measure (Matrix (Fin a) (Fin a) F))
      [ν.IsAddLeftInvariant] (J' : Subgroup (GL (Fin a) F)), congSub O ϖ a ≤ J' →
      J' ≤ GLint O a →
      ν (Jset J') * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (a * a) =
        (Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') : ENNReal) * ν (intMat O a a)
end Formalism.DoubleCosetMeasures


