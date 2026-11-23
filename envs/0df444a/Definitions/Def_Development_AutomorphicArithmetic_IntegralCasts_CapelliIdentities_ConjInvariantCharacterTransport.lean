-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjInvariantCharacterTransport
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjInvariantCharacterTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:17.27186+00:00
-- url     : https://prove2.me/theorems/96c17cea-2efe-484e-a428-1eceef5ce5ea
-- title:
--   Conj Invariant Character Transport
-- statement:
--   Definitions and structural lemmas for Conj Invariant Character Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjInvariantCharacterTransport.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.DYhc8.eLast :
    (k : Type) → [Field k] → (n : ℕ) → Fin (n + (1 : ℕ)) → k :=
    fun (k : Type) [Field k] (n : ℕ) ↦ Pi.single (Fin.last n) (1 : k)
theorem UpperTheory.Reformulated.B.DYhc8.aux2 :
    ∀ (k : Type) [inst : Field k] (n : ℕ) {a b : GL (Fin (n + (1 : ℕ))) k},
      a ∈
          {g : GL (Fin (n + (1 : ℕ))) k |
            Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (↑g : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
              UpperTheory.Reformulated.B.DYhc8.eLast k n} →
        b ∈
            {g : GL (Fin (n + (1 : ℕ))) k |
              Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (↑g : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
                UpperTheory.Reformulated.B.DYhc8.eLast k n} →
          a * b ∈
            {g : GL (Fin (n + (1 : ℕ))) k |
              Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (↑g : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
                UpperTheory.Reformulated.B.DYhc8.eLast k n} := by
  intro k _ n a b ha hb
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha, hb]
theorem UpperTheory.Reformulated.B.DYhc8.aux3 :
    ∀ (k : Type) [inst : Field k] (n : ℕ),
      Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n)
          (↑(1 : GL (Fin (n + (1 : ℕ))) k) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
        UpperTheory.Reformulated.B.DYhc8.eLast k n := by
  intro k _ n
  rw [Units.val_one, Matrix.vecMul_one]
theorem UpperTheory.Reformulated.B.DYhc8.aux4 :
    ∀ (k : Type) [inst : Field k] (n : ℕ) {a : GL (Fin (n + (1 : ℕ))) k},
      a ∈
          {g : GL (Fin (n + (1 : ℕ))) k |
            Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (↑g : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
              UpperTheory.Reformulated.B.DYhc8.eLast k n} →
        a⁻¹ ∈
          {g : GL (Fin (n + (1 : ℕ))) k |
            Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (↑g : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
              UpperTheory.Reformulated.B.DYhc8.eLast k n} := by
  intro k _ n a ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  have h : (↑a : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) * (↑a⁻¹ : GL (Fin (n + (1 : ℕ))) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  conv_lhs => rw [← ha]
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
noncomputable def UpperTheory.Reformulated.B.DYhc8.Mir :
    (k : Type) → [inst : Field k] → (n : ℕ) → Subgroup (GL (Fin (n + (1 : ℕ))) k) :=
    fun (k : Type) [inst : Field k] (n : ℕ) ↦
      {
        carrier :=
          {g : GL (Fin (n + (1 : ℕ))) k |
            Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (↑g : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) =
              UpperTheory.Reformulated.B.DYhc8.eLast k n},
        mul_mem' := @UpperTheory.Reformulated.B.DYhc8.aux2 k inst n, one_mem' := UpperTheory.Reformulated.B.DYhc8.aux3 k n,
        inv_mem' := @UpperTheory.Reformulated.B.DYhc8.aux4 k inst n : Subgroup (GL (Fin (n + (1 : ℕ))) k) }
noncomputable def UpperTheory.Reformulated.B.DYhc8.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}
noncomputable def UpperTheory.Reformulated.B.DYhc8.twKer :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      Submodule.span k
        {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[k] V) (↑n : G) : V → V) v - (↑((ψ : ↥N → kˣ) n) : k) • v}
@[reducible] noncomputable def UpperTheory.Reformulated.B.DYhc8.TwJacquet :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Type :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      V ⧸ UpperTheory.Reformulated.B.DYhc8.twKer ρ N ψ
noncomputable def UpperTheory.Reformulated.B.DYhc8.colMat :
    (k : Type) → [Field k] → (n : ℕ) → (Fin n → k) → Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k :=
    fun (k : Type) [Field k] (n : ℕ) (v : Fin n → k) (i j : Fin (n + (1 : ℕ))) ↦
      if j = Fin.last n then Fin.lastCases (0 : k) v i else (0 : k)
theorem colMat_mul (k : Type) [Field k] (n : ℕ) (v w : Fin n → k) :
    UpperTheory.Reformulated.B.DYhc8.colMat k n v * UpperTheory.Reformulated.B.DYhc8.colMat k n w = 0 := by
  ext i j
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.DYhc8.colMat, Matrix.zero_apply]
  rw [Finset.sum_eq_zero]
  intro l _
  by_cases hl : l = Fin.last n
  · subst hl
    simp
  · simp [hl]
theorem colMat_add (k : Type) [Field k] (n : ℕ) (v w : Fin n → k) :
    UpperTheory.Reformulated.B.DYhc8.colMat k n (v + w) =
      UpperTheory.Reformulated.B.DYhc8.colMat k n v + UpperTheory.Reformulated.B.DYhc8.colMat k n w := by
  ext i j
  simp only [UpperTheory.Reformulated.B.DYhc8.colMat, Matrix.add_apply]
  by_cases hj : j = Fin.last n
  · simp only [hj, if_true]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · simp [hj]
theorem colMat_zero (k : Type) [Field k] (n : ℕ) :
    UpperTheory.Reformulated.B.DYhc8.colMat k n 0 = 0 := by
  ext i j
  simp only [UpperTheory.Reformulated.B.DYhc8.colMat, Matrix.zero_apply]
  by_cases hj : j = Fin.last n
  · simp only [hj, if_true]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · simp [hj]
theorem one_add_mul_one_sub (k : Type) [Field k] (n : ℕ) (v : Fin n → k) :
    ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) + UpperTheory.Reformulated.B.DYhc8.colMat k n v) *
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) - UpperTheory.Reformulated.B.DYhc8.colMat k n v) = 1 := by
  rw [add_mul, mul_sub, mul_sub, colMat_mul]
  simp
theorem one_sub_mul_one_add (k : Type) [Field k] (n : ℕ) (v : Fin n → k) :
    ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) - UpperTheory.Reformulated.B.DYhc8.colMat k n v) *
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) + UpperTheory.Reformulated.B.DYhc8.colMat k n v) = 1 := by
  rw [sub_mul, mul_add, mul_add, colMat_mul]
  simp
theorem UpperTheory.Reformulated.B.DYhc8.laurent_T_neg_one_mul_T_one :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Multiplicative (Fin n → k)),
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v)) *
          ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v)) =
        (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n v
  exact one_add_mul_one_sub k n _
theorem UpperTheory.Reformulated.B.DYhc8.aux11 :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Multiplicative (Fin n → k)),
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v)) *
          ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v)) =
        (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n v
  exact one_sub_mul_one_add k n _
theorem UpperTheory.Reformulated.B.DYhc8.aux12 :
    ∀ (k : Type) [inst : Field k] (n : ℕ),
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
            UpperTheory.Reformulated.B.DYhc8.colMat k n
              ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (1 : Multiplicative (Fin n → k)))) *
          ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
            UpperTheory.Reformulated.B.DYhc8.colMat k n
              ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (1 : Multiplicative (Fin n → k)))) =
        (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n
  exact one_add_mul_one_sub k n _
theorem UpperTheory.Reformulated.B.DYhc8.algebra_smulCommClass_complex :
    ∀ (k : Type) [inst : Field k] (n : ℕ),
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
            UpperTheory.Reformulated.B.DYhc8.colMat k n
              ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (1 : Multiplicative (Fin n → k)))) *
          ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
            UpperTheory.Reformulated.B.DYhc8.colMat k n
              ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (1 : Multiplicative (Fin n → k)))) =
        (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n
  exact one_sub_mul_one_add k n _
theorem UpperTheory.Reformulated.B.DYhc8.zero_contDiffOn_supported :
    ∀ (k : Type) [inst : Field k] (n : ℕ),
      {
          val :=
            (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
              UpperTheory.Reformulated.B.DYhc8.colMat k n
                ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (1 : Multiplicative (Fin n → k))),
          inv :=
            (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
              UpperTheory.Reformulated.B.DYhc8.colMat k n
                ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (1 : Multiplicative (Fin n → k))),
          val_inv := UpperTheory.Reformulated.B.DYhc8.aux12 k n, inv_val := UpperTheory.Reformulated.B.DYhc8.algebra_smulCommClass_complex k n :
          (Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)ˣ } =
        (1 : GL (Fin (n + (1 : ℕ))) k) := by
  intro k _ n
  apply Units.ext
  change (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) + UpperTheory.Reformulated.B.DYhc8.colMat k n 0 = 1
  rw [colMat_zero, add_zero]
theorem UpperTheory.Reformulated.B.DYhc8.sign_action_map_comm :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (v w : Multiplicative (Fin n → k)),
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (v * w))) *
          ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (v * w))) =
        (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n v w
  exact one_add_mul_one_sub k n _
theorem UpperTheory.Reformulated.B.DYhc8.column_matrix_mul_inverse :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (v w : Multiplicative (Fin n → k)),
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (v * w))) *
          ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
            UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (v * w))) =
        (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n v w
  exact one_sub_mul_one_add k n _
theorem UpperTheory.Reformulated.B.DYhc8.complex_normed_instance_compat :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (v w : Multiplicative (Fin n → k)),
      {
          val :=
            (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
              UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (v * w)),
          inv :=
            (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
              UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) (v * w)),
          val_inv := UpperTheory.Reformulated.B.DYhc8.sign_action_map_comm k n v w, inv_val := UpperTheory.Reformulated.B.DYhc8.column_matrix_mul_inverse k n v w :
          (Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)ˣ } =
        {
            val :=
              (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
                UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v),
            inv :=
              (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
                UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v),
            val_inv := UpperTheory.Reformulated.B.DYhc8.laurent_T_neg_one_mul_T_one k n v, inv_val := UpperTheory.Reformulated.B.DYhc8.aux11 k n v :
            (Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)ˣ } *
          {
            val :=
              (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
                UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) w),
            inv :=
              (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
                UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) w),
            val_inv := UpperTheory.Reformulated.B.DYhc8.laurent_T_neg_one_mul_T_one k n w, inv_val := UpperTheory.Reformulated.B.DYhc8.aux11 k n w :
            (Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)ˣ } := by
  intro k _ n v w
  apply Units.ext
  change (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
      UpperTheory.Reformulated.B.DYhc8.colMat k n (Multiplicative.toAdd v + Multiplicative.toAdd w) =
    ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
      UpperTheory.Reformulated.B.DYhc8.colMat k n (Multiplicative.toAdd v)) *
    ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
      UpperTheory.Reformulated.B.DYhc8.colMat k n (Multiplicative.toAdd w))
  rw [colMat_add, add_mul, mul_add, mul_add, colMat_mul]
  simp only [one_mul, mul_one, add_zero]
  abel
noncomputable def UpperTheory.Reformulated.B.DYhc8.unip :
    (k : Type) → [inst : Field k] → (n : ℕ) → Multiplicative (Fin n → k) →* GL (Fin (n + (1 : ℕ))) k :=
    fun (k : Type) [Field k] (n : ℕ) ↦
      {
        toFun := fun (v : Multiplicative (Fin n → k)) ↦
          {
            val :=
              (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
                UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v),
            inv :=
              (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) -
                UpperTheory.Reformulated.B.DYhc8.colMat k n ((Multiplicative.toAdd : Multiplicative (Fin n → k) → Fin n → k) v),
            val_inv := UpperTheory.Reformulated.B.DYhc8.laurent_T_neg_one_mul_T_one k n v, inv_val := UpperTheory.Reformulated.B.DYhc8.aux11 k n v :
            (Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)ˣ },
        map_one' := UpperTheory.Reformulated.B.DYhc8.zero_contDiffOn_supported k n, map_mul' := UpperTheory.Reformulated.B.DYhc8.complex_normed_instance_compat k n :
        Multiplicative (Fin n → k) →* GL (Fin (n + (1 : ℕ))) k }
noncomputable def UpperTheory.Reformulated.B.DYhc8.MirU :
    (k : Type) → [inst : Field k] → (n : ℕ) → Subgroup (GL (Fin (n + (1 : ℕ))) k) :=
    fun (k : Type) [Field k] (n : ℕ) ↦ (UpperTheory.Reformulated.B.DYhc8.unip k n).range
noncomputable def UpperTheory.Reformulated.B.DYhc8.MirUin :
    (k : Type) → [inst : Field k] → (n : ℕ) → Subgroup ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n) :=
    fun (k : Type) [Field k] (n : ℕ) ↦ (UpperTheory.Reformulated.B.DYhc8.MirU k n).subgroupOf (UpperTheory.Reformulated.B.DYhc8.Mir k n)
theorem UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_mem :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (m : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m)) (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs m
  rw [Submodule.span_le]
  rintro w ⟨n, v, rfl⟩
  obtain ⟨h, hθ⟩ := hs m n
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  have key : ρ (s m) (ρ (↑n : G) v - (↑(θ n) : ℂ) • v) =
      ρ (↑(⟨s m * (↑n : G) * (s m)⁻¹, h⟩ : ↥N) : G) (ρ (s m) v) -
        (↑(θ ⟨s m * (↑n : G) * (s m)⁻¹, h⟩) : ℂ) • ρ (s m) v := by
    rw [hθ, map_sub, map_smul]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [key]
  exact Submodule.subset_span ⟨_, _, rfl⟩
theorem UpperTheory.Reformulated.B.DYhc8.rootGL_mem_unitary :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        Submodule.span ℂ
            {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
          Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M))) (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  exact UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_mem ρ N θ s hs 1
theorem UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_transport :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M)))
          (UpperTheory.Reformulated.B.DYhc8.rootGL_mem_unitary ρ N θ s hs) =
        (1 : UpperTheory.Reformulated.B.DYhc8.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.DYhc8.TwJacquet ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp [Submodule.mapQ_apply]
theorem UpperTheory.Reformulated.B.DYhc8.span_sub_smul_le_comap_mul_twKer :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (a b : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b))) (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  exact UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_mem ρ N θ s hs (a * b)
theorem UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_apply :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n)
      (a b : M),
      (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b)))
          (UpperTheory.Reformulated.B.DYhc8.span_sub_smul_le_comap_mul_twKer ρ N θ s hs a b) =
        (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) a))
            (UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_mem ρ N θ s hs a) *
          (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) b))
            (UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_mem ρ N θ s hs b) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp [Submodule.mapQ_apply]
  rfl
noncomputable def UpperTheory.Reformulated.B.DYhc8.twAct :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] →
          [inst_2 : _root_.Module ℂ V] →
            (ρ : Representation ℂ G V) →
              (N : Subgroup G) →
                (θ : ↥N →* ℂˣ) →
                  {M : Type} →
                    [inst_3 : Group M] →
                      (s : M →* G) →
                        (∀ (m : M) (n : ↥N),
                            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
                              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
                          Representation ℂ M (UpperTheory.Reformulated.B.DYhc8.TwJacquet ρ N θ) :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
        (θ : ↥N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
        (hs :
          ∀ (m : M) (n : ↥N),
            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) ↦
      {
        toFun := fun (m : M) ↦
          (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.DYhc8.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m))
            (UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_mem ρ N θ s hs m),
        map_one' := UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_transport ρ N θ s hs, map_mul' := UpperTheory.Reformulated.B.DYhc8.conj_invariant_character_apply ρ N θ s hs :
        M →* UpperTheory.Reformulated.B.DYhc8.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.DYhc8.TwJacquet ρ N θ }
noncomputable def UpperTheory.Reformulated.B.DYhc8.glEmbMat :
    (k : Type) → [Field k] → (n : ℕ) → Matrix (Fin n) (Fin n) k → Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k :=
    fun (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (i j : Fin (n + (1 : ℕ))) ↦
      Fin.lastCases (Fin.lastCases (1 : k) (fun (x : Fin n) ↦ (0 : k)) j)
        (fun (i' : Fin n) ↦ Fin.lastCases (0 : k) (fun (j' : Fin n) ↦ A i' j') j) i
theorem UpperTheory.Reformulated.B.DYhc8.glEmbMat_one_eq_one :
    ∀ (k : Type) [inst : Field k] (n : ℕ),
      UpperTheory.Reformulated.B.DYhc8.glEmbMat k n (1 : Matrix (Fin n) (Fin n) k) = (1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) := by
  intro k _ n
  ext i j
  simp only [UpperTheory.Reformulated.B.DYhc8.glEmbMat]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [Matrix.one_apply, (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.one_apply, (Fin.castSucc_lt_last i).ne]
    | cast j => simp [Matrix.one_apply]
theorem UpperTheory.Reformulated.B.DYhc8.glEmbMat_mul_eq_mul :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (A B : Matrix (Fin n) (Fin n) k),
      UpperTheory.Reformulated.B.DYhc8.glEmbMat k n (A * B) = UpperTheory.Reformulated.B.DYhc8.glEmbMat k n A * UpperTheory.Reformulated.B.DYhc8.glEmbMat k n B := by
  intro k _ n A B
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [UpperTheory.Reformulated.B.DYhc8.glEmbMat]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [Matrix.mul_apply]
noncomputable def UpperTheory.Reformulated.B.DYhc8.glEmbHom :
    (k : Type) → [inst : Field k] → (n : ℕ) → Matrix (Fin n) (Fin n) k →* Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k :=
    fun (k : Type) [Field k] (n : ℕ) ↦
      { toFun := UpperTheory.Reformulated.B.DYhc8.glEmbMat k n, map_one' := UpperTheory.Reformulated.B.DYhc8.glEmbMat_one_eq_one k n,
        map_mul' := UpperTheory.Reformulated.B.DYhc8.glEmbMat_mul_eq_mul k n :
        Matrix (Fin n) (Fin n) k →* Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k }
noncomputable def UpperTheory.Reformulated.B.DYhc8.glEmb :
    (k : Type) → [inst : Field k] → (n : ℕ) → GL (Fin n) k →* GL (Fin (n + (1 : ℕ))) k :=
    fun (k : Type) [Field k] (n : ℕ) ↦ Units.map (UpperTheory.Reformulated.B.DYhc8.glEmbHom k n)
theorem UpperTheory.Reformulated.B.DYhc8.glEmb_mem_mirabolic :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (g : GL (Fin n) k),
      (UpperTheory.Reformulated.B.DYhc8.glEmb k n : GL (Fin n) k → GL (Fin (n + (1 : ℕ))) k) g ∈ UpperTheory.Reformulated.B.DYhc8.Mir k n := by
  intro k _ n g
  change Matrix.vecMul (UpperTheory.Reformulated.B.DYhc8.eLast k n) (UpperTheory.Reformulated.B.DYhc8.glEmbMat k n (↑g)) = UpperTheory.Reformulated.B.DYhc8.eLast k n
  ext j
  simp only [UpperTheory.Reformulated.B.DYhc8.eLast, Matrix.single_one_vecMul, UpperTheory.Reformulated.B.DYhc8.glEmbMat, Fin.lastCases_last]
  induction j using Fin.lastCases with
  | last => simp [UpperTheory.Reformulated.B.DYhc8.glEmbMat]
  | cast j => simp [UpperTheory.Reformulated.B.DYhc8.glEmbMat]
noncomputable def UpperTheory.Reformulated.B.DYhc8.levi :
    (k : Type) → [inst : Field k] → (n : ℕ) → GL (Fin n) k →* ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n) :=
    fun (k : Type) [Field k] (n : ℕ) ↦
      (UpperTheory.Reformulated.B.DYhc8.glEmb k n).codRestrict (UpperTheory.Reformulated.B.DYhc8.Mir k n) (UpperTheory.Reformulated.B.DYhc8.glEmb_mem_mirabolic k n)
theorem glEmbMat_mul_colMat (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    UpperTheory.Reformulated.B.DYhc8.glEmbMat k n A * UpperTheory.Reformulated.B.DYhc8.colMat k n v =
      UpperTheory.Reformulated.B.DYhc8.colMat k n (A.mulVec v) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [UpperTheory.Reformulated.B.DYhc8.glEmbMat, UpperTheory.Reformulated.B.DYhc8.colMat]
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp [Matrix.mulVec, dotProduct]
  · simp [hj]
theorem colMat_mul_glEmbMat (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    UpperTheory.Reformulated.B.DYhc8.colMat k n v * UpperTheory.Reformulated.B.DYhc8.glEmbMat k n A =
      UpperTheory.Reformulated.B.DYhc8.colMat k n v := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [UpperTheory.Reformulated.B.DYhc8.glEmbMat, UpperTheory.Reformulated.B.DYhc8.colMat]
  induction j using Fin.lastCases with
  | last => simp [(Fin.castSucc_lt_last _).ne]
  | cast j => simp [(Fin.castSucc_lt_last _).ne]
theorem conj_unip (k : Type) [Field k] (n : ℕ) (g : GL (Fin n) k)
    (v : Multiplicative (Fin n → k)) :
    UpperTheory.Reformulated.B.DYhc8.glEmb k n g * UpperTheory.Reformulated.B.DYhc8.unip k n v * (UpperTheory.Reformulated.B.DYhc8.glEmb k n g)⁻¹ =
      UpperTheory.Reformulated.B.DYhc8.unip k n
        (Multiplicative.ofAdd ((↑g : Matrix (Fin n) (Fin n) k).mulVec (Multiplicative.toAdd v))) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  change UpperTheory.Reformulated.B.DYhc8.glEmbMat k n (↑g) *
      ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
        UpperTheory.Reformulated.B.DYhc8.colMat k n (Multiplicative.toAdd v)) =
    ((1 : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) +
      UpperTheory.Reformulated.B.DYhc8.colMat k n ((↑g : Matrix (Fin n) (Fin n) k).mulVec (Multiplicative.toAdd v))) *
      UpperTheory.Reformulated.B.DYhc8.glEmbMat k n (↑g)
  rw [mul_add, add_mul, mul_one, one_mul, glEmbMat_mul_colMat, colMat_mul_glEmbMat]
theorem UpperTheory.Reformulated.B.DYhc8.levi_conj_unipotent_mem :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (m : GL (Fin n) k) (u : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n)),
      ∃ (h :
        (UpperTheory.Reformulated.B.DYhc8.levi k n : GL (Fin n) k → ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) m * (↑u : ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) *
            ((UpperTheory.Reformulated.B.DYhc8.levi k n : GL (Fin n) k → ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) m)⁻¹ ∈
          UpperTheory.Reformulated.B.DYhc8.MirUin k n),
        ((1 : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n) →* ℂˣ) : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n) → ℂˣ)
            (⟨(UpperTheory.Reformulated.B.DYhc8.levi k n : GL (Fin n) k → ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) m *
                          (↑u : ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) *
                  ((UpperTheory.Reformulated.B.DYhc8.levi k n : GL (Fin n) k → ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) m)⁻¹,
                h⟩ :
              ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n)) =
          ((1 : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n) →* ℂˣ) : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n) → ℂˣ) u := by
  intro k _ _ _ _ n m u
  have hu : ((u : ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) : GL (Fin (n + (1 : ℕ))) k) ∈ (UpperTheory.Reformulated.B.DYhc8.unip k n).range :=
    Subgroup.mem_subgroupOf.mp u.2
  obtain ⟨v, hv⟩ := hu
  have hmem : UpperTheory.Reformulated.B.DYhc8.levi k n m * (↑u : ↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) *
      (UpperTheory.Reformulated.B.DYhc8.levi k n m)⁻¹ ∈ UpperTheory.Reformulated.B.DYhc8.MirUin k n := by
    refine Subgroup.mem_subgroupOf.mpr ⟨Multiplicative.ofAdd ((↑m : Matrix (Fin n) (Fin n) k).mulVec (Multiplicative.toAdd v)), ?_⟩
    rw [← conj_unip, hv]
    rfl
  exact ⟨hmem, rfl⟩
noncomputable def UpperTheory.Reformulated.B.DYhc8.psiMinus :
    (k : Type) →
      [inst : Field k] →
        [inst_1 : ValuativeRel k] →
          [inst_2 : TopologicalSpace k] →
            [IsNonarchimedeanLocalField k] →
              {n : ℕ} →
                {V : Type} →
                  [inst_4 : AddCommGroup V] →
                    [inst_5 : _root_.Module ℂ V] →
                      (τ : Representation ℂ (↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) V) →
                        Representation ℂ (GL (Fin n) k)
                          (UpperTheory.Reformulated.B.DYhc8.TwJacquet τ (UpperTheory.Reformulated.B.DYhc8.MirUin k n)
                            (1 : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n) →* ℂˣ)) :=
    fun (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type}
        [AddCommGroup V] [_root_.Module ℂ V] (τ : Representation ℂ (↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) V) ↦
      UpperTheory.Reformulated.B.DYhc8.twAct τ (UpperTheory.Reformulated.B.DYhc8.MirUin k n) (1 : ↥(UpperTheory.Reformulated.B.DYhc8.MirUin k n) →* ℂˣ)
        (UpperTheory.Reformulated.B.DYhc8.levi k n) (UpperTheory.Reformulated.B.DYhc8.levi_conj_unipotent_mem n)
noncomputable def UpperTheory.Reformulated.B.DYhc8.SmPsiMinus :
    (k : Type) →
      [inst : Field k] → [inst_1 : ValuativeRel k] → [inst_2 : TopologicalSpace k] → [IsNonarchimedeanLocalField k] → Prop :=
    fun (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] ↦
      ∀ (n : ℕ) (V : Type) [inst_4 : AddCommGroup V] [inst_5 : _root_.Module ℂ V]
        (τ : Representation ℂ (↥(UpperTheory.Reformulated.B.DYhc8.Mir k n)) V),
        UpperTheory.Reformulated.B.DYhc8.IsSmooth τ → UpperTheory.Reformulated.B.DYhc8.IsSmooth (UpperTheory.Reformulated.B.DYhc8.psiMinus k τ)


