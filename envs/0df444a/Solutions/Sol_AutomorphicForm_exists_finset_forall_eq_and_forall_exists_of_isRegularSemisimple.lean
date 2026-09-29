-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6f3d09cf-e7b4-5cdc-b3d9-6d5a6f0e59bc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple

set_option autoImplicit false

namespace OrbitalSupport

section Extraction

variable {G : Type*} [Group G]

private theorem exists_finset_of_finset_forall_exists (T : Subgroup G) (U : Set G) (hU1 : (1 : G) ∈ U)
    (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (P : G → Prop) (S₀ : Finset G)
    (hcov₀ : ∀ x : G, P x → ∃ s ∈ S₀, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ S : Finset G,
      (∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s) ∧
      ∀ x : G, P x → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u := by
  classical
  set C : Finset (Finset G) :=
    S₀.powerset.filter (fun S => ∀ s₀ ∈ S₀, ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, s₀ = t * s * u) with hC
  have hS₀C : S₀ ∈ C := by
    rw [hC, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl S₀, fun s₀ hs₀ => ⟨s₀, hs₀, 1, T.one_mem, 1, hU1, by simp⟩⟩
  obtain ⟨S, hSC, hSmin⟩ := C.exists_min_image Finset.card ⟨S₀, hS₀C⟩
  rw [hC, Finset.mem_filter, Finset.mem_powerset] at hSC
  obtain ⟨hSsub, hScov⟩ := hSC
  refine ⟨S, ?_, ?_⟩
  · intro s hs s' hs' t ht u hu hs'eq
    by_contra hne
    have hmem : S.erase s' ∈ C := by
      rw [hC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.Subset.trans (Finset.erase_subset s' S) hSsub, fun s₀ hs₀ => ?_⟩
      obtain ⟨s₁, hs₁, t₁, ht₁, u₁, hu₁, hs₀eq⟩ := hScov s₀ hs₀
      by_cases h₁ : s₁ = s'
      · rw [h₁] at hs₀eq
        refine ⟨s, Finset.mem_erase.2 ⟨fun h => hne h.symm, hs⟩, t₁ * t, T.mul_mem ht₁ ht,
          u * u₁, hUmul u hu u₁ hu₁, ?_⟩
        rw [hs₀eq, hs'eq]
        simp only [mul_assoc]
      · exact ⟨s₁, Finset.mem_erase.2 ⟨h₁, hs₁⟩, t₁, ht₁, u₁, hu₁, hs₀eq⟩
    exact absurd (hSmin _ hmem) (not_le.2 (Finset.card_erase_lt_of_mem hs'))
  · intro x hx
    obtain ⟨s₀, hs₀, t, ht, u, hu, hxeq⟩ := hcov₀ x hx
    obtain ⟨s, hs, t', ht', u', hu', hs₀eq⟩ := hScov s₀ hs₀
    refine ⟨s, hs, t * t', T.mul_mem ht ht', u' * u, hUmul u' hu' u hu, ?_⟩
    rw [hxeq, hs₀eq]
    simp only [mul_assoc]

end Extraction

section IntegralUnits

variable {R : Type*} [CommRing R]

private theorem mul_mem_integralMatrixSet {W : Set R} (hadd : ∀ a ∈ W, ∀ b ∈ W, a + b ∈ W)
    (hmul : ∀ a ∈ W, ∀ b ∈ W, a * b ∈ W) {m n : Matrix (Fin 2) (Fin 2) R}
    (hm : m ∈ AutomorphicForm.integralMatrixSet W) (hn : n ∈ AutomorphicForm.integralMatrixSet W) :
    m * n ∈ AutomorphicForm.integralMatrixSet W := fun i j => by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact hadd _ (hmul _ (hm i 0) _ (hn 0 j)) _ (hmul _ (hm i 1) _ (hn 1 j))

private theorem mul_mem_integralUnitsSet {W : Set R} (hadd : ∀ a ∈ W, ∀ b ∈ W, a + b ∈ W)
    (hmul : ∀ a ∈ W, ∀ b ∈ W, a * b ∈ W) {g h : Matrix.GeneralLinearGroup (Fin 2) R}
    (hg : g ∈ AutomorphicForm.integralUnitsSet W) (hh : h ∈ AutomorphicForm.integralUnitsSet W) :
    g * h ∈ AutomorphicForm.integralUnitsSet W := by
  simp only [AutomorphicForm.integralUnitsSet, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hg₁, hg₂⟩ := hg
  obtain ⟨hh₁, hh₂⟩ := hh
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem_integralMatrixSet hadd hmul hg₁ hh₁
  · rw [mul_inv_rev, Units.val_mul]
    exact mul_mem_integralMatrixSet hadd hmul hh₂ hg₂

private theorem inv_mem_integralUnitsSet {W : Set R} {g : Matrix.GeneralLinearGroup (Fin 2) R}
    (hg : g ∈ AutomorphicForm.integralUnitsSet W) : g⁻¹ ∈ AutomorphicForm.integralUnitsSet W := by
  simp only [AutomorphicForm.integralUnitsSet, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hg₁, hg₂⟩ := hg
  refine ⟨hg₂, ?_⟩
  rw [inv_inv]
  exact hg₁

end IntegralUnits

section Denominators

variable {F : Type*} [Field F] (A : ValuationSubring F)

private theorem exists_mul_mem (x : F) : ∃ d : F, d ∈ A ∧ d ≠ 0 ∧ d * x ∈ A := by
  rcases A.mem_or_inv_mem x with hx | hx
  · exact ⟨1, A.one_mem, one_ne_zero, by rw [one_mul]; exact hx⟩
  · by_cases h0 : x = 0
    · exact ⟨1, A.one_mem, one_ne_zero, by rw [h0, mul_zero]; exact A.zero_mem⟩
    · exact ⟨x⁻¹, hx, inv_ne_zero h0, by rw [inv_mul_cancel₀ h0]; exact A.one_mem⟩

private theorem exists_forall_mul_mem (s : Finset F) : ∃ d : F, d ∈ A ∧ d ≠ 0 ∧ ∀ x ∈ s, d * x ∈ A := by
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨1, A.one_mem, one_ne_zero, fun x hx => by simp at hx⟩
  · intro y s _ ih
    obtain ⟨d, hdA, hd0, hd⟩ := ih
    obtain ⟨e, heA, he0, he⟩ := exists_mul_mem A y
    refine ⟨d * e, mul_mem hdA heA, mul_ne_zero hd0 he0, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [mul_assoc]
      exact mul_mem hdA he
    · rw [mul_comm d e, mul_assoc]
      exact mul_mem heA (hd x hx)

private theorem exists_forall_mul_apply_mem (s : Finset (Matrix (Fin 2) (Fin 2) F)) :
    ∃ d : F, d ∈ A ∧ d ≠ 0 ∧ ∀ m ∈ s, ∀ i j, d * m i j ∈ A := by
  classical
  obtain ⟨d, hdA, hd0, hd⟩ := exists_forall_mul_mem A
    (s.biUnion fun m => (Finset.univ : Finset (Fin 2 × Fin 2)).image fun p => m p.1 p.2)
  exact ⟨d, hdA, hd0, fun m hm i j =>
    hd _ (Finset.mem_biUnion.2 ⟨m, hm, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)⟩

private theorem mul_mul_apply_mem_of_integral_right {d : F} {m : Matrix (Fin 2) (Fin 2) F}
    (hm : ∀ i j, d * m i j ∈ A) {n : Matrix (Fin 2) (Fin 2) F}
    (hn : n ∈ AutomorphicForm.integralMatrixSet (A : Set F)) (i j : Fin 2) :
    d * (m * n) i j ∈ A := by
  have h : d * (m * n) i j = d * m i 0 * n 0 j + d * m i 1 * n 1 j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h]
  exact add_mem (mul_mem (hm i 0) (SetLike.mem_coe.1 (hn 0 j)))
    (mul_mem (hm i 1) (SetLike.mem_coe.1 (hn 1 j)))

private theorem mul_mul_apply_mem_of_integral_left {d : F} {n : Matrix (Fin 2) (Fin 2) F}
    (hn : n ∈ AutomorphicForm.integralMatrixSet (A : Set F)) {m : Matrix (Fin 2) (Fin 2) F}
    (hm : ∀ i j, d * m i j ∈ A) (i j : Fin 2) : d * (n * m) i j ∈ A := by
  have h : d * (n * m) i j = n i 0 * (d * m 0 j) + n i 1 * (d * m 1 j) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h]
  exact add_mem (mul_mem (SetLike.mem_coe.1 (hn i 0)) (hm 0 j))
    (mul_mem (SetLike.mem_coe.1 (hn i 1)) (hm 1 j))

private theorem exists_forall_mul_apply_mem_of_forall_exists (P : Matrix.GeneralLinearGroup (Fin 2) F → Prop)
    (F₀ : Finset (Matrix.GeneralLinearGroup (Fin 2) F))
    (hP : ∀ g, P g → ∃ c ∈ F₀, c⁻¹ * g ∈ AutomorphicForm.integralUnitsSet (A : Set F)) :
    ∃ d : F, d ∈ A ∧ d ≠ 0 ∧
      ∀ g, P g → ∀ i j, d * (g : Matrix (Fin 2) (Fin 2) F) i j ∈ A := by
  classical
  obtain ⟨d, hdA, hd0, hd⟩ :=
    exists_forall_mul_apply_mem A
      (F₀.image fun c : Matrix.GeneralLinearGroup (Fin 2) F => (c : Matrix (Fin 2) (Fin 2) F))
  refine ⟨d, hdA, hd0, fun g hg => ?_⟩
  obtain ⟨c, hc, hu⟩ := hP g hg
  simp only [AutomorphicForm.integralUnitsSet, Set.mem_setOf_eq] at hu
  have hgc : (g : Matrix (Fin 2) (Fin 2) F) = (c : Matrix (Fin 2) (Fin 2) F) *
      ((c⁻¹ * g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [hgc]
  exact mul_mul_apply_mem_of_integral_right A
    (hd (c : Matrix (Fin 2) (Fin 2) F) (Finset.mem_image.2 ⟨c, hc, rfl⟩)) hu.1

end Denominators

section Elements

variable {F : Type*} [Field F]

private def diag₂ (a b : Fˣ) : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private def unip₂ (z : F) : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![1, z; 0, 1]
  inv := !![1, -z; 0, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem diag₂_val (a b : Fˣ) : (diag₂ a b : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, (b : F)] :=
  rfl

private theorem unip₂_val (z : F) : (unip₂ z : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] :=
  rfl

private theorem diag₂_mul_diag₂ (a b a' b' : Fˣ) : diag₂ a b * diag₂ a' b' = diag₂ (a * a') (b * b') :=
  Units.ext (by simp [diag₂])

private theorem diag₂_mul_diag₂_comm (a b a' b' : Fˣ) : diag₂ a b * diag₂ a' b' = diag₂ a' b' * diag₂ a b := by
  rw [diag₂_mul_diag₂, diag₂_mul_diag₂, mul_comm a a', mul_comm b b']

private theorem unip₂_mul_unip₂ (z w : F) : unip₂ z * unip₂ w = unip₂ (z + w) :=
  Units.ext (by simp [unip₂, add_comm])

private theorem diag₂_mul_unip₂ (r : Fˣ) (z : F) : diag₂ r 1 * unip₂ z = unip₂ (r * z) * diag₂ r 1 :=
  Units.ext (by simp [diag₂, unip₂])

private theorem mul_diag₂_self (c : Fˣ) (h : Matrix.GeneralLinearGroup (Fin 2) F) :
    h * diag₂ c c = diag₂ c c * h := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.eta_fin_two (h : Matrix (Fin 2) (Fin 2) F)]
  simp [diag₂, mul_comm]

private theorem diag₂_self_mem_centralizer (c : Fˣ) (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    diag₂ c c ∈ Subgroup.centralizer ({γ} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) :=
  Subgroup.mem_centralizer_iff.2 fun h _ => mul_diag₂_self c h

private theorem diag₂_mem_centralizer_diag₂ (a b a' b' : Fˣ) :
    diag₂ a b ∈ Subgroup.centralizer ({diag₂ a' b'} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) :=
  Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
    exact diag₂_mul_diag₂_comm a' b' a b

private theorem unip₂_mem_integralUnitsSet (A : ValuationSubring F) {z : F} (hz : z ∈ A) :
    unip₂ z ∈ AutomorphicForm.integralUnitsSet (A : Set F) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [unip₂, Units.inv_mk, hz, A.zero_mem, A.one_mem]

private theorem diag₂_mem_integralUnitsSet (A : ValuationSubring F) {a b : Fˣ} (ha : (a : F) ∈ A)
    (ha' : (a : F)⁻¹ ∈ A) (hb : (b : F) ∈ A) (hb' : (b : F)⁻¹ ∈ A) :
    diag₂ a b ∈ AutomorphicForm.integralUnitsSet (A : Set F) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [diag₂, Units.inv_mk, Units.val_inv_eq_inv_val, ha, ha', hb, hb', A.zero_mem]

private def weyl₂ : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private def lunip₂ (y : F) : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![1, 0; y, 1]
  inv := !![1, 0; -y, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem weyl₂_mem_integralUnitsSet (A : ValuationSubring F) :
    (weyl₂ : Matrix.GeneralLinearGroup (Fin 2) F) ∈ AutomorphicForm.integralUnitsSet (A : Set F) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [weyl₂, Units.inv_mk, A.zero_mem, A.one_mem]

private theorem lunip₂_mem_integralUnitsSet (A : ValuationSubring F) {y : F} (hy : y ∈ A) :
    lunip₂ y ∈ AutomorphicForm.integralUnitsSet (A : Set F) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [lunip₂, Units.inv_mk, hy, A.zero_mem, A.one_mem]

private theorem unip₂_mul_weyl₂_apply_zero_zero (t : F) :
    ((unip₂ t * weyl₂ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = t := by
  simp [unip₂, weyl₂]

private theorem unip₂_mul_weyl₂_apply_one_zero (t : F) :
    ((unip₂ t * weyl₂ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  simp [unip₂, weyl₂]

private theorem lunip₂_apply_zero_zero (y : F) : (lunip₂ y : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
  simp [lunip₂]

private theorem lunip₂_apply_one_zero (y : F) : (lunip₂ y : Matrix (Fin 2) (Fin 2) F) 1 0 = y := by
  simp [lunip₂]

private theorem mul_apply_one_zero (x u : Matrix.GeneralLinearGroup (Fin 2) F) :
    ((x * u : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (u : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (u : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

end Elements

section IntegralValuation

variable {F : Type*} [Field F] (A : ValuationSubring F)

private theorem coe_add_closed : ∀ a ∈ (A : Set F), ∀ b ∈ (A : Set F), a + b ∈ (A : Set F) := fun _ ha _ hb =>
  SetLike.mem_coe.2 (add_mem (SetLike.mem_coe.1 ha) (SetLike.mem_coe.1 hb))

private theorem coe_mul_closed : ∀ a ∈ (A : Set F), ∀ b ∈ (A : Set F), a * b ∈ (A : Set F) := fun _ ha _ hb =>
  SetLike.mem_coe.2 (mul_mem (SetLike.mem_coe.1 ha) (SetLike.mem_coe.1 hb))

private theorem mul_mem_integralUnitsSet_coe {g h : Matrix.GeneralLinearGroup (Fin 2) F}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (A : Set F))
    (hh : h ∈ AutomorphicForm.integralUnitsSet (A : Set F)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (A : Set F) :=
  mul_mem_integralUnitsSet (coe_add_closed A) (coe_mul_closed A) hg hh

private theorem one_mem_integralUnitsSet_coe :
    (1 : Matrix.GeneralLinearGroup (Fin 2) F) ∈ AutomorphicForm.integralUnitsSet (A : Set F) :=
  AutomorphicForm.one_mem_integralUnitsSet (SetLike.mem_coe.2 A.zero_mem) (SetLike.mem_coe.2 A.one_mem)

end IntegralValuation

section Decomposition

variable {F : Type*} [Field F] (A : ValuationSubring F)

private theorem exists_mem_and_mul_apply_one_zero_eq_zero (x : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F),
      ((x * u : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  by_cases hc : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact ⟨1, one_mem_integralUnitsSet_coe A, by rw [mul_one]; exact hc⟩
  by_cases hq : (x : Matrix (Fin 2) (Fin 2) F) 1 1 / (x : Matrix (Fin 2) (Fin 2) F) 1 0 ∈ A
  · set q : F := (x : Matrix (Fin 2) (Fin 2) F) 1 1 / (x : Matrix (Fin 2) (Fin 2) F) 1 0 with hq_def
    have hd : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = q * (x : Matrix (Fin 2) (Fin 2) F) 1 0 := by
      rw [hq_def]
      field_simp
    refine ⟨unip₂ (-q) * weyl₂,
      mul_mem_integralUnitsSet_coe A (unip₂_mem_integralUnitsSet A (neg_mem hq)) (weyl₂_mem_integralUnitsSet A),
      ?_⟩
    rw [mul_apply_one_zero, unip₂_mul_weyl₂_apply_zero_zero, unip₂_mul_weyl₂_apply_one_zero, hd]
    ring
  · have hq' : (x : Matrix (Fin 2) (Fin 2) F) 1 0 / (x : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ A := by
      rw [← inv_div]
      exact (A.mem_or_inv_mem _).resolve_left hq
    have hd0 : (x : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro h
      apply hq
      rw [h, zero_div]
      exact A.zero_mem
    set q : F := (x : Matrix (Fin 2) (Fin 2) F) 1 0 / (x : Matrix (Fin 2) (Fin 2) F) 1 1 with hq_def
    have hcq : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = q * (x : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      rw [hq_def]
      field_simp
    refine ⟨lunip₂ (-q), lunip₂_mem_integralUnitsSet A (neg_mem hq'), ?_⟩
    rw [mul_apply_one_zero, lunip₂_apply_zero_zero, lunip₂_apply_one_zero, hcq]
    ring

private theorem exists_eq_diag₂_mul_unip₂_mul (x : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ (p s : Fˣ) (z : F), ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F),
      x = diag₂ p s * unip₂ z * u := by
  obtain ⟨u₀, hu₀, h10⟩ := exists_mem_and_mul_apply_one_zero_eq_zero A x
  set y : Matrix.GeneralLinearGroup (Fin 2) F := x * u₀ with hy_def
  have hdet : IsUnit (y : Matrix (Fin 2) (Fin 2) F).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Units.isUnit y
  have hdet' := hdet.ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet'
  have hy : (y : Matrix (Fin 2) (Fin 2) F) =
      !![(y : Matrix (Fin 2) (Fin 2) F) 0 0, (y : Matrix (Fin 2) (Fin 2) F) 0 1;
        0, (y : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    conv_lhs => rw [Matrix.eta_fin_two (y : Matrix (Fin 2) (Fin 2) F)]
    rw [h10]
  obtain ⟨p, q, s, hpqs, hp, hs⟩ :
      ∃ p q s : F, (y : Matrix (Fin 2) (Fin 2) F) = !![p, q; 0, s] ∧ p ≠ 0 ∧ s ≠ 0 :=
    ⟨_, _, _, hy, left_ne_zero_of_mul hdet', right_ne_zero_of_mul hdet'⟩
  have hz : p * (p⁻¹ * q) = q := by rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  have hxu : y = diag₂ (Units.mk0 p hp) (Units.mk0 s hs) * unip₂ (p⁻¹ * q) := by
    apply Units.ext
    rw [hpqs, Units.val_mul, diag₂_val, unip₂_val, Matrix.mul_fin_two, Units.val_mk0, Units.val_mk0]
    simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, hz]
  refine ⟨Units.mk0 p hp, Units.mk0 s hs, p⁻¹ * q, u₀⁻¹, inv_mem_integralUnitsSet hu₀, ?_⟩
  rw [← hxu, hy_def, mul_inv_cancel_right]

private theorem exists_eq_diag₂_mul_diag₂_mul_unip₂_mul (x : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ (c r : Fˣ) (z : F), ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F),
      x = diag₂ c c * diag₂ r 1 * unip₂ z * u := by
  obtain ⟨p, s, z, u, hu, hx⟩ := exists_eq_diag₂_mul_unip₂_mul A x
  refine ⟨s, s⁻¹ * p, z, u, hu, ?_⟩
  rw [hx, diag₂_mul_diag₂, mul_inv_cancel_left, mul_one]

end Decomposition

section Compactness

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] (A : ValuationSubring F)

private theorem isOpen_setOf_mul_mem (hAo : IsOpen (A : Set F)) (e : F) : IsOpen {z : F | e * z ∈ A} := by
  have h__af := (hAo.preimage (continuous_const.mul continuous_id : Continuous fun z : F => e * z))
  simp only [Set.preimage, SetLike.mem_coe] at h__af
  exact h__af

private theorem isOpen_setOf_sub_mem (hAo : IsOpen (A : Set F)) (z₀ : F) : IsOpen {z : F | z - z₀ ∈ A} := by
  have h__af := (hAo.preimage (continuous_id.sub continuous_const : Continuous fun z : F => z - z₀))
  simp only [Set.preimage, SetLike.mem_coe] at h__af
  exact h__af

private theorem isOpen_setOf_mul_fst_mem_and_mul_snd_mem (hAo : IsOpen (A : Set F)) (a b : F) :
    IsOpen {p : F × F | a * p.1 ∈ A ∧ b * p.2 ∈ A} := by
  have h__af := ((hAo.preimage (continuous_const.mul continuous_fst : Continuous fun p : F × F => a * p.1)).inter
      (hAo.preimage (continuous_const.mul continuous_snd : Continuous fun p : F × F => b * p.2)))
  simp only [Set.preimage, Set.inter_def, Set.mem_setOf_eq, SetLike.mem_coe] at h__af
  exact h__af

private theorem isCompact_setOf_mul_mem (hAc : IsCompact (A : Set F)) {e : F} (he : e ≠ 0) :
    IsCompact {z : F | e * z ∈ A} := by
  have himage : IsCompact ((fun a : F => e⁻¹ * a) '' (A : Set F)) :=
    hAc.image (continuous_const.mul continuous_id)
  convert himage using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hz
    exact ⟨e * z, hz, by rw [← mul_assoc, inv_mul_cancel₀ he, one_mul]⟩
  · rintro ⟨a, ha, rfl⟩
    rw [← mul_assoc, mul_inv_cancel₀ he, one_mul]
    exact ha

private theorem exists_forall_mul_mem_of_isCompact (hAo : IsOpen (A : Set F)) {s : Set F} (hs : IsCompact s) :
    ∃ e : F, e ∈ A ∧ e ≠ 0 ∧ ∀ z ∈ s, e * z ∈ A := by
  classical
  choose d hdA hd0 hdz using fun z : F => exists_mul_mem A z
  obtain ⟨t, -, hcov⟩ := hs.elim_nhds_subcover (fun z₀ => {z : F | d z₀ * z ∈ A}) fun z₀ _ =>
    (isOpen_setOf_mul_mem A hAo (d z₀)).mem_nhds (hdz z₀)
  refine ⟨∏ z₀ ∈ t, d z₀, prod_mem fun z₀ _ => hdA z₀, Finset.prod_ne_zero_iff.2 fun z₀ _ => hd0 z₀,
    fun z hz => ?_⟩
  have hz' := hcov hz
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hz'
  obtain ⟨z₀, hz₀t, hz₀⟩ := hz'
  have h : (∏ x ∈ t, d x) * z = (∏ x ∈ t.erase z₀, d x) * (d z₀ * z) := by
    rw [← Finset.mul_prod_erase t d hz₀t]
    ring
  rw [h]
  exact mul_mem (prod_mem fun x _ => hdA x) hz₀

private theorem exists_finset_forall_exists_sub_mem (hAo : IsOpen (A : Set F)) {s : Set F} (hs : IsCompact s) :
    ∃ Z : Finset F, ∀ z ∈ s, ∃ z₀ ∈ Z, z - z₀ ∈ A := by
  obtain ⟨Z, -, hcov⟩ := hs.elim_nhds_subcover (fun z₀ => {z : F | z - z₀ ∈ A}) fun z₀ _ =>
    (isOpen_setOf_sub_mem A hAo z₀).mem_nhds (show z₀ - z₀ ∈ A by rw [sub_self]; exact A.zero_mem)
  refine ⟨Z, fun z hz => ?_⟩
  have hz' := hcov hz
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hz'
  obtain ⟨z₀, hz₀Z, hz₀⟩ := hz'
  exact ⟨z₀, hz₀Z, hz₀⟩

private theorem exists_finset_forall_exists_inv_mul_mem_and_mul_inv_mem [T2Space F] (hAc : IsCompact (A : Set F))
    (hAo : IsOpen (A : Set F)) {e₁ e₂ : F} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) :
    ∃ R : Finset F, ∀ r : F, r ≠ 0 → e₁ * r ∈ A → e₂ * r⁻¹ ∈ A →
      ∃ r₀ ∈ R, r₀ ≠ 0 ∧ r₀⁻¹ * r ∈ A ∧ r₀ * r⁻¹ ∈ A := by
  classical
  have hK : IsCompact (({r : F | e₁ * r ∈ A} ×ˢ {t : F | e₂ * t ∈ A}) ∩ {p : F × F | p.1 * p.2 = 1}) :=
    ((isCompact_setOf_mul_mem A hAc he₁).prod (isCompact_setOf_mul_mem A hAc he₂)).inter_right
      (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  set K : Set (F × F) := ({r : F | e₁ * r ∈ A} ×ˢ {t : F | e₂ * t ∈ A}) ∩ {p : F × F | p.1 * p.2 = 1}
    with hK_def
  have hnhds : ∀ p₀ ∈ K, {p : F × F | p₀.2 * p.1 ∈ A ∧ p₀.1 * p.2 ∈ A} ∈ nhds p₀ := by
    intro p₀ hp₀
    rw [hK_def] at hp₀
    have h1 : p₀.1 * p₀.2 = 1 := hp₀.2
    apply (isOpen_setOf_mul_fst_mem_and_mul_snd_mem A hAo p₀.2 p₀.1).mem_nhds
    show p₀.2 * p₀.1 ∈ A ∧ p₀.1 * p₀.2 ∈ A
    rw [mul_comm p₀.2 p₀.1, h1]
    exact ⟨A.one_mem, A.one_mem⟩
  obtain ⟨P, hPK, hcov⟩ :=
    hK.elim_nhds_subcover (fun p₀ : F × F => {p : F × F | p₀.2 * p.1 ∈ A ∧ p₀.1 * p.2 ∈ A}) hnhds
  refine ⟨P.image Prod.fst, fun r hr h₁ h₂ => ?_⟩
  have hmem : (r, r⁻¹) ∈ K := by
    rw [hK_def]
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq]
    exact ⟨⟨h₁, h₂⟩, mul_inv_cancel₀ hr⟩
  have hr' := hcov hmem
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hr'
  obtain ⟨p₀, hp₀P, hA₁, hA₂⟩ := hr'
  have hp₀K : p₀ ∈ K := hPK p₀ hp₀P
  rw [hK_def] at hp₀K
  have hprod : p₀.1 * p₀.2 = 1 := hp₀K.2
  have hne : p₀.1 * p₀.2 ≠ 0 := by
    rw [hprod]
    exact one_ne_zero
  have hp₀ : p₀.1 ≠ 0 := left_ne_zero_of_mul hne
  have hsnd : p₀.2 = p₀.1⁻¹ := eq_inv_of_mul_eq_one_right hprod
  refine ⟨p₀.1, Finset.mem_image_of_mem Prod.fst hp₀P, hp₀, ?_, hA₂⟩
  rw [← hsnd]
  exact hA₁

private theorem exists_forall_mul_inv_mem_of_isCompact [ContinuousInv₀ F] (hAo : IsOpen (A : Set F)) {s : Set F}
    (hs : IsCompact s) {g : F → F} (hg : Continuous g) (hg0 : ∀ y ∈ s, g y ≠ 0) :
    ∃ e : F, e ∈ A ∧ e ≠ 0 ∧ ∀ y ∈ s, e * (g y)⁻¹ ∈ A := by
  obtain ⟨e, heA, he0, he⟩ := exists_forall_mul_mem_of_isCompact A hAo
    (hs.image_of_continuousOn (hg.continuousOn.inv₀ hg0))
  exact ⟨e, heA, he0, fun y hy => he _ (Set.mem_image_of_mem _ hy)⟩

end Compactness

section Conjugation

variable {F : Type*} [Field F]

private def tri₂ (r : Fˣ) (z : F) : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![(r : F), (r : F) * z; 0, 1]
  inv := !![(r : F)⁻¹, -z; 0, 1]
  val_inv := by
    simp [Matrix.one_fin_two]
  inv_val := by
    simp [Matrix.one_fin_two]

private theorem diag₂_mul_unip₂_eq_tri₂ (r : Fˣ) (z : F) : diag₂ r 1 * unip₂ z = tri₂ r z := by
  apply Units.ext
  rw [Units.val_mul, diag₂_val, unip₂_val]
  simp [tri₂]

private theorem tri₂_apply₀₀ (r : Fˣ) (z : F) : ((tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 0 = r := rfl

private theorem tri₂_apply₀₁ (r : Fˣ) (z : F) : ((tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 1 = (r : F) * z := rfl

private theorem tri₂_apply₁₀ (r : Fˣ) (z : F) : ((tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl

private theorem tri₂_apply₁₁ (r : Fˣ) (z : F) : ((tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl

private theorem tri₂_inv_apply₀₀ (r : Fˣ) (z : F) : (((tri₂ r z)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 0 = (r : F)⁻¹ := rfl

private theorem tri₂_inv_apply₀₁ (r : Fˣ) (z : F) : (((tri₂ r z)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 1 = -z := rfl

private theorem tri₂_inv_apply₁₀ (r : Fˣ) (z : F) : (((tri₂ r z)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl

private theorem tri₂_inv_apply₁₁ (r : Fˣ) (z : F) : (((tri₂ r z)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl

private theorem diag₂_apply₀₀ (a b : Fˣ) : ((diag₂ a b : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 0 = a := rfl

private theorem diag₂_apply₀₁ (a b : Fˣ) : ((diag₂ a b : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := rfl

private theorem diag₂_apply₁₀ (a b : Fˣ) : ((diag₂ a b : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl

private theorem diag₂_apply₁₁ (a b : Fˣ) : ((diag₂ a b : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 1 = b := rfl

private theorem tri₂_conj_apply₁₀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (r : Fˣ) (z : F) :
    (((tri₂ r z)⁻¹ * γ * tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * r := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, tri₂_apply₀₀, tri₂_apply₁₀,
    tri₂_inv_apply₁₀, tri₂_inv_apply₁₁]
  ring

private theorem tri₂_conj_apply₁₁ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (r : Fˣ) (z : F) :
    (((tri₂ r z)⁻¹ * γ * tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (γ : Matrix (Fin 2) (Fin 2) F) 1 1 + (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * r * z := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, tri₂_apply₀₁, tri₂_apply₁₁,
    tri₂_inv_apply₁₀, tri₂_inv_apply₁₁]
  ring

private theorem tri₂_conj_apply₀₀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (r : Fˣ) (z : F) :
    (((tri₂ r z)⁻¹ * γ * tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (γ : Matrix (Fin 2) (Fin 2) F) 0 0 - (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * r * z := by
  have hr : (r : F)⁻¹ * r = 1 := inv_mul_cancel₀ r.ne_zero
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, tri₂_apply₀₀, tri₂_apply₁₀,
    tri₂_inv_apply₀₀, tri₂_inv_apply₀₁]
  linear_combination (γ : Matrix (Fin 2) (Fin 2) F) 0 0 * hr

private theorem tri₂_conj_apply₀₁ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (r : Fˣ) (z : F) :
    (((tri₂ r z)⁻¹ * γ * tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (r : F)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) F) 0 1 +
        ((γ : Matrix (Fin 2) (Fin 2) F) 0 0 - (γ : Matrix (Fin 2) (Fin 2) F) 1 1) * z -
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * r * z * z := by
  have hr : (r : F)⁻¹ * r = 1 := inv_mul_cancel₀ r.ne_zero
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, tri₂_apply₀₁, tri₂_apply₁₁,
    tri₂_inv_apply₀₀, tri₂_inv_apply₀₁]
  linear_combination ((γ : Matrix (Fin 2) (Fin 2) F) 0 0 * z) * hr

private theorem exists_eq_diag₂_mul_tri₂_mul (A : ValuationSubring F) (x : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ (c r : Fˣ) (z : F) (u : Matrix.GeneralLinearGroup (Fin 2) F),
      u ∈ AutomorphicForm.integralUnitsSet (A : Set F) ∧ x = diag₂ c c * tri₂ r z * u := by
  obtain ⟨c, r, z, u, hu, hx⟩ := exists_eq_diag₂_mul_diag₂_mul_unip₂_mul A x
  exact ⟨c, r, z, u, hu, by rw [hx, mul_assoc (diag₂ c c) (diag₂ r 1) (unip₂ z), diag₂_mul_unip₂_eq_tri₂]⟩

private theorem diag₂_self_mul_inv_mul_mul (c : Fˣ) (γ y : Matrix.GeneralLinearGroup (Fin 2) F) :
    (diag₂ c c * y)⁻¹ * γ * (diag₂ c c * y) = y⁻¹ * γ * y := by
  have hD : (diag₂ c c)⁻¹ * γ * diag₂ c c = γ := by
    rw [mul_assoc, mul_diag₂_self, inv_mul_cancel_left]
  have hre : y⁻¹ * (diag₂ c c)⁻¹ * γ * (diag₂ c c * y) = y⁻¹ * ((diag₂ c c)⁻¹ * γ * diag₂ c c) * y := by
    simp only [mul_assoc]
  rw [mul_inv_rev, hre, hD]

private theorem forall_mul_apply_mem_of_mul_right (A : ValuationSubring F) {d : F}
    {γ y u : Matrix.GeneralLinearGroup (Fin 2) F} (hu : u ∈ AutomorphicForm.integralUnitsSet (A : Set F))
    (h : ∀ i j, d * (((y * u)⁻¹ * γ * (y * u) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j ∈ A) :
    ∀ i j, d * ((y⁻¹ * γ * y : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ A := by
  simp only [AutomorphicForm.integralUnitsSet, Set.mem_setOf_eq] at hu
  have hconj : (y * u)⁻¹ * γ * (y * u) = u⁻¹ * (y⁻¹ * γ * y) * u := by
    rw [mul_inv_rev]
    simp only [mul_assoc]
  have hback : y⁻¹ * γ * y = u * (u⁻¹ * (y⁻¹ * γ * y) * u) * u⁻¹ := by
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  rw [hconj] at h
  rw [hback, Units.val_mul, Units.val_mul]
  exact mul_mul_apply_mem_of_integral_right A (mul_mul_apply_mem_of_integral_left A hu.1 h) hu.2

end Conjugation

section Dichotomy

variable {F : Type*} [Field F]

private theorem inv_mul_mul_eq_diag₂_of_forall_apply_eq {γ h : Matrix.GeneralLinearGroup (Fin 2) F} {l₁ l₂ : Fˣ}
    (H : ∀ i j, ((γ : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F)) i j =
      ((h : Matrix (Fin 2) (Fin 2) F) * ((diag₂ l₁ l₂ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) i j) :
    h⁻¹ * γ * h = diag₂ l₁ l₂ := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  exact H i j

private theorem exists_inv_mul_mul_eq_diag₂_or_forall_ne_zero (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    (∃ (h : Matrix.GeneralLinearGroup (Fin 2) F) (l₁ l₂ : Fˣ), l₁ ≠ l₂ ∧ h⁻¹ * γ * h = diag₂ l₁ l₂) ∨
      ∀ t : F, t * t - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) * t +
        Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
  by_cases hroot : ∃ t : F, t * t - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) * t +
      Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) = 0
  · left
    obtain ⟨t, ht⟩ := hroot
    have hdisc := (AutomorphicForm.isRegularSemisimple_iff_ne_zero γ).1 hγ
    have hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      exact Units.isUnit γ
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at ht hdisc
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨a, ha⟩ : ∃ a : F, a = (γ : Matrix (Fin 2) (Fin 2) F) 0 0 := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : F, b = (γ : Matrix (Fin 2) (Fin 2) F) 0 1 := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : F, c = (γ : Matrix (Fin 2) (Fin 2) F) 1 0 := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : F, e = (γ : Matrix (Fin 2) (Fin 2) F) 1 1 := ⟨_, rfl⟩
    rw [← ha, ← hb, ← hc, ← he] at ht hdisc hdet
    by_cases hc0 : c = 0
    ·
      have hae : a ≠ e := by
        intro hae
        apply hdisc
        linear_combination (a - e) * hae + 4 * b * hc0
      have ha0 : a ≠ 0 := by
        intro ha0
        apply hdet
        linear_combination e * ha0 - b * hc0
      have he0 : e ≠ 0 := by
        intro he0
        apply hdet
        linear_combination a * he0 - b * hc0
      have hM : Matrix.det !![(1 : F), b; 0, e - a] ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        intro h0
        apply hae
        linear_combination (-1 : F) * h0
      obtain ⟨h, hh⟩ : ∃ h : Matrix.GeneralLinearGroup (Fin 2) F,
          (h : Matrix (Fin 2) (Fin 2) F) = !![(1 : F), b; 0, e - a] :=
        ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, rfl⟩
      refine ⟨h, Units.mk0 a ha0, Units.mk0 e he0, ?_, inv_mul_mul_eq_diag₂_of_forall_apply_eq ?_⟩
      · intro h0
        apply hae
        have := congrArg Units.val h0
        simpa using this
      · simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hh, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, diag₂_apply₀₀, diag₂_apply₀₁, diag₂_apply₁₀,
          diag₂_apply₁₁, Units.val_mk0, ← ha, ← hb, ← hc, ← he]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · ring1
        · ring1
        · linear_combination hc0
        · linear_combination b * hc0
    ·
      have hne : t ≠ a + e - t := by
        intro h0
        apply hdisc
        linear_combination (-4 : F) * ht + (2 * t - (a + e)) * h0
      have ht0 : t ≠ 0 := by
        intro h0
        apply hdet
        linear_combination ht + (a + e - t) * h0
      have ht'0 : a + e - t ≠ 0 := by
        intro h0
        apply hdet
        linear_combination ht + t * h0
      have hM : Matrix.det !![t - e, a + e - t - e; c, c] ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        intro h0
        apply hne
        have h1 : c * (t - (a + e - t)) = 0 := by linear_combination h0
        rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 hc0
        · linear_combination h2
      obtain ⟨h, hh⟩ : ∃ h : Matrix.GeneralLinearGroup (Fin 2) F,
          (h : Matrix (Fin 2) (Fin 2) F) = !![t - e, a + e - t - e; c, c] :=
        ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, rfl⟩
      refine ⟨h, Units.mk0 t ht0, Units.mk0 _ ht'0, ?_, inv_mul_mul_eq_diag₂_of_forall_apply_eq ?_⟩
      · intro h0
        apply hne
        have := congrArg Units.val h0
        simpa using this
      · simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hh, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, diag₂_apply₀₀, diag₂_apply₀₁, diag₂_apply₁₀,
          diag₂_apply₁₁, Units.val_mk0, ← ha, ← hb, ← hc, ← he]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · linear_combination (-1 : F) * ht
        · linear_combination (-1 : F) * ht
        · ring1
        · ring1
  · right
    intro t ht
    exact hroot ⟨t, ht⟩

end Dichotomy

section Regimes

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] (A : ValuationSubring F)

private theorem exists_finset_forall_exists_units [T2Space F] (hAc : IsCompact (A : Set F)) (hAo : IsOpen (A : Set F))
    {e₁ e₂ : F} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) :
    ∃ R : Finset Fˣ, ∀ r : Fˣ, e₁ * r ∈ A → e₂ * (r : F)⁻¹ ∈ A →
      ∃ r₀ ∈ R, ((r₀⁻¹ * r : Fˣ) : F) ∈ A ∧ ((r₀⁻¹ * r : Fˣ) : F)⁻¹ ∈ A := by
  classical
  obtain ⟨R₀, hR₀⟩ := exists_finset_forall_exists_inv_mul_mem_and_mul_inv_mem A hAc hAo he₁ he₂
  refine ⟨(R₀.subtype fun r => r ≠ 0).image (fun x => Units.mk0 x.1 x.2), fun r h₁ h₂ => ?_⟩
  obtain ⟨r₀, hr₀R, hr₀, hinv, hmul⟩ := hR₀ r r.ne_zero h₁ h₂
  refine ⟨Units.mk0 r₀ hr₀, Finset.mem_image.2 ⟨⟨r₀, hr₀⟩, Finset.mem_subtype.2 hr₀R, rfl⟩, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact hinv
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_rev, inv_inv, mul_comm]
    exact hmul

private theorem exists_finset_forall_exists_of_diag₂ (hAc : IsCompact (A : Set F)) (hAo : IsOpen (A : Set F))
    {l₁ l₂ : Fˣ} (hl : l₁ ≠ l₂) {d : F} (hd : d ≠ 0) :
    ∃ S₀ : Finset (Matrix.GeneralLinearGroup (Fin 2) F),
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ i j, d * ((x⁻¹ * diag₂ l₁ l₂ * x : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) i j ∈ A) →
          ∃ s ∈ S₀, ∃ t ∈ Subgroup.centralizer ({diag₂ l₁ l₂} : Set (Matrix.GeneralLinearGroup (Fin 2) F)),
            ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F), x = t * s * u := by
  classical
  have he : d * ((l₁ : F) - l₂) ≠ 0 := mul_ne_zero hd (sub_ne_zero.2 fun h => hl (Units.ext h))
  obtain ⟨Z₀, hZ₀⟩ := exists_finset_forall_exists_sub_mem A hAo (isCompact_setOf_mul_mem A hAc he)
  refine ⟨Z₀.image unip₂, fun x hx => ?_⟩
  obtain ⟨c, r, z, u, hu, rfl⟩ := exists_eq_diag₂_mul_tri₂_mul A x
  have hy := forall_mul_apply_mem_of_mul_right A hu hx
  rw [diag₂_self_mul_inv_mul_mul] at hy
  have hval : (((tri₂ r z)⁻¹ * diag₂ l₁ l₂ * tri₂ r z : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = ((l₁ : F) - l₂) * z := by
    rw [tri₂_conj_apply₀₁, diag₂_apply₀₁, diag₂_apply₀₀, diag₂_apply₁₁, diag₂_apply₁₀]
    ring
  have hz := hy 0 1
  rw [hval, ← mul_assoc] at hz
  obtain ⟨z₀, hz₀Z, hzz₀⟩ := hZ₀ z hz
  have hsplit : unip₂ z = unip₂ z₀ * unip₂ (z - z₀) := by
    rw [unip₂_mul_unip₂]
    congr 1
    ring
  refine ⟨unip₂ z₀, Finset.mem_image_of_mem unip₂ hz₀Z, diag₂ c c * diag₂ r 1,
    mul_mem (diag₂_self_mem_centralizer c _) (diag₂_mem_centralizer_diag₂ r 1 l₁ l₂), unip₂ (z - z₀) * u,
    mul_mem_integralUnitsSet_coe A (unip₂_mem_integralUnitsSet A hzz₀) hu, ?_⟩
  rw [← diag₂_mul_unip₂_eq_tri₂, hsplit]
  simp only [mul_assoc]

omit [TopologicalSpace F] [IsTopologicalRing F] in

private theorem exists_finset_forall_exists_of_conj {γ h : Matrix.GeneralLinearGroup (Fin 2) F} {d : F}
    (H : ∃ S₀ : Finset (Matrix.GeneralLinearGroup (Fin 2) F),
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ i j, d * ((x⁻¹ * (h⁻¹ * γ * h) * x : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) i j ∈ A) →
          ∃ s ∈ S₀, ∃ t ∈ Subgroup.centralizer ({h⁻¹ * γ * h} : Set (Matrix.GeneralLinearGroup (Fin 2) F)),
            ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F), x = t * s * u) :
    ∃ S₀ : Finset (Matrix.GeneralLinearGroup (Fin 2) F),
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ i j, d * ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ A) →
          ∃ s ∈ S₀, ∃ t ∈ Subgroup.centralizer ({γ} : Set (Matrix.GeneralLinearGroup (Fin 2) F)),
            ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F), x = t * s * u := by
  classical
  obtain ⟨S₀, hS₀⟩ := H
  refine ⟨S₀.image (fun s => h * s), fun x hx => ?_⟩
  have hx' : ∀ i j, d * (((h⁻¹ * x)⁻¹ * (h⁻¹ * γ * h) * (h⁻¹ * x) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j ∈ A := by
    have hconj : (h⁻¹ * x)⁻¹ * (h⁻¹ * γ * h) * (h⁻¹ * x) = x⁻¹ * γ * x := by
      simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [hconj]
    exact hx
  obtain ⟨s, hs, t, ht, u, hu, hxeq⟩ := hS₀ (h⁻¹ * x) hx'
  refine ⟨h * s, Finset.mem_image_of_mem (fun s => h * s) hs, h * t * h⁻¹, ?_, u, hu, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    have ht' := ht (h⁻¹ * γ * h) (Set.mem_singleton _)
    calc γ * (h * t * h⁻¹) = h * (h⁻¹ * γ * h * t) * h⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]
      _ = h * (t * (h⁻¹ * γ * h)) * h⁻¹ := by rw [ht']
      _ = h * t * h⁻¹ * γ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  · calc x = h * (h⁻¹ * x) := (mul_inv_cancel_left h x).symm
      _ = h * (t * s * u) := by rw [hxeq]
      _ = h * t * h⁻¹ * (h * s) * u := by simp only [mul_assoc, inv_mul_cancel_left]

private theorem exists_finset_forall_exists_of_forall_ne_zero [T2Space F] [ContinuousInv₀ F]
    (hAc : IsCompact (A : Set F)) (hAo : IsOpen (A : Set F)) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hroot : ∀ t : F, t * t - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) * t +
      Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) ≠ 0) {d : F} (hd : d ≠ 0) :
    ∃ S₀ : Finset (Matrix.GeneralLinearGroup (Fin 2) F),
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ i j, d * ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ A) →
          ∃ s ∈ S₀, ∃ t ∈ Subgroup.centralizer ({γ} : Set (Matrix.GeneralLinearGroup (Fin 2) F)),
            ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F), x = t * s * u := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : F, a = (γ : Matrix (Fin 2) (Fin 2) F) 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : F, b = (γ : Matrix (Fin 2) (Fin 2) F) 0 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : F, c = (γ : Matrix (Fin 2) (Fin 2) F) 1 0 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : F, e = (γ : Matrix (Fin 2) (Fin 2) F) 1 1 := ⟨_, rfl⟩
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, ← ha, ← hb, ← hc, ← he] at hroot
  have hc0 : c ≠ 0 := fun hc0 => hroot a (by linear_combination (-b : F) * hc0)

  obtain ⟨d₁, hd₁A, hd₁, hd₁e⟩ := exists_mul_mem A (d * e)
  obtain ⟨d₂, -, hd₂, hd₂c⟩ := exists_mul_mem A c
  obtain ⟨d₃, -, hd₃, hd₃c⟩ := exists_mul_mem A c⁻¹
  have he₁ : d₁ * d ≠ 0 := mul_ne_zero hd₁ hd
  have hQ : Continuous fun w : F => b * c + (a - e) * w - w * w :=
    (continuous_const.add (continuous_const.mul continuous_id)).sub (continuous_id.mul continuous_id)
  have hQ0 : ∀ w : F, b * c + (a - e) * w - w * w ≠ 0 := fun w hw =>
    hroot (e + w) (by linear_combination (-1 : F) * hw)
  obtain ⟨q, -, hq, hQinv⟩ := exists_forall_mul_inv_mem_of_isCompact A hAo (isCompact_setOf_mul_mem A hAc he₁)
    hQ (fun w _ => hQ0 w)
  have he₂ : d * c ≠ 0 := mul_ne_zero hd hc0
  have he₃ : d₂ * d * q ≠ 0 := mul_ne_zero (mul_ne_zero hd₂ hd) hq
  obtain ⟨R, hR⟩ := exists_finset_forall_exists_units A hAc hAo he₂ he₃
  have he₄ : d₁ * d * (d₂ * d * q) * d₃ ≠ 0 := mul_ne_zero (mul_ne_zero he₁ he₃) hd₃
  obtain ⟨Z₀, hZ₀⟩ := exists_finset_forall_exists_sub_mem A hAo (isCompact_setOf_mul_mem A hAc he₄)
  refine ⟨(R ×ˢ Z₀).image (fun p : Fˣ × F => diag₂ p.1 1 * unip₂ p.2), fun x hx => ?_⟩
  obtain ⟨c', r, z, u, hu, rfl⟩ := exists_eq_diag₂_mul_tri₂_mul A x
  have hy := forall_mul_apply_mem_of_mul_right A hu hx
  rw [diag₂_self_mul_inv_mul_mul] at hy
  have hr : (r : F)⁻¹ * r = 1 := inv_mul_cancel₀ r.ne_zero
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0

  have h10 := hy 1 0
  rw [tri₂_conj_apply₁₀, ← hc] at h10
  have h11 := hy 1 1
  rw [tri₂_conj_apply₁₁, ← hc, ← he] at h11
  have h01 := hy 0 1
  rw [tri₂_conj_apply₀₁, ← ha, ← hb, ← hc, ← he] at h01

  have hζ : d₁ * d * (c * r * z) ∈ A := by
    have : d₁ * d * (c * r * z) = d₁ * (d * (e + c * r * z)) - d₁ * (d * e) := by ring
    rw [this]
    exact sub_mem (mul_mem hd₁A h11) hd₁e
  have hr_up : d * c * r ∈ A := by
    rw [mul_assoc]
    exact h10
  have hr_down : d₂ * d * q * (r : F)⁻¹ ∈ A := by
    have hid : (r : F)⁻¹ * (b * c + (a - e) * (c * r * z) - c * r * z * (c * r * z)) =
        c * ((r : F)⁻¹ * b + (a - e) * z - c * r * z * z) := by
      linear_combination ((a - e) * c * z - c * c * r * z * z) * hr
    have hρ : (r : F)⁻¹ = c * ((r : F)⁻¹ * b + (a - e) * z - c * r * z * z) *
        (b * c + (a - e) * (c * r * z) - c * r * z * (c * r * z))⁻¹ := by
      rw [← hid, mul_inv_cancel_right₀ (hQ0 (c * r * z))]
    have : d₂ * d * q * (r : F)⁻¹ = d₂ * c * (d * ((r : F)⁻¹ * b + (a - e) * z - c * r * z * z)) *
        (q * (b * c + (a - e) * (c * r * z) - c * r * z * (c * r * z))⁻¹) := by
      linear_combination (d₂ * d * q) * hρ
    rw [this]
    exact mul_mem (mul_mem hd₂c h01) (hQinv (c * r * z) hζ)
  obtain ⟨r₀, hr₀R, hαA, hαinv⟩ := hR r hr_up hr_down
  obtain ⟨α, hα⟩ : ∃ α : Fˣ, α = r₀⁻¹ * r := ⟨_, rfl⟩
  rw [← hα] at hαA hαinv
  have hrα : r = r₀ * α := by
    rw [hα, mul_inv_cancel_left]
  have hαz : d₁ * d * (d₂ * d * q) * d₃ * ((α : F) * z) ∈ A := by
    have : d₁ * d * (d₂ * d * q) * d₃ * ((α : F) * z) =
        (α : F) * (d₁ * d * (c * r * z)) * (d₂ * d * q * (r : F)⁻¹) * (d₃ * c⁻¹) := by
      linear_combination (-(d₁ * d * (d₂ * d * q) * d₃ * (α : F) * z * (c * c⁻¹))) * hr +
        (-(d₁ * d * (d₂ * d * q) * d₃ * (α : F) * z)) * hcc
    rw [this]
    exact mul_mem (mul_mem (mul_mem hαA hζ) hr_down) hd₃c
  obtain ⟨z₀, hz₀Z, hαzz₀⟩ := hZ₀ ((α : F) * z) hαz
  have hsplit : unip₂ ((α : F) * z) = unip₂ z₀ * unip₂ ((α : F) * z - z₀) := by
    rw [unip₂_mul_unip₂]
    congr 1
    ring
  have hdd : diag₂ (r₀ * α) 1 = diag₂ r₀ 1 * diag₂ α 1 := by
    rw [diag₂_mul_diag₂, mul_one]
  have hα1 : diag₂ α 1 ∈ AutomorphicForm.integralUnitsSet (A : Set F) :=
    diag₂_mem_integralUnitsSet A hαA hαinv (by rw [Units.val_one]; exact A.one_mem)
      (by rw [Units.val_one, inv_one]; exact A.one_mem)
  refine ⟨diag₂ r₀ 1 * unip₂ z₀, Finset.mem_image.2 ⟨(r₀, z₀), Finset.mem_product.2 ⟨hr₀R, hz₀Z⟩, rfl⟩,
    diag₂ c' c', diag₂_self_mem_centralizer c' γ, unip₂ ((α : F) * z - z₀) * diag₂ α 1 * u,
    mul_mem_integralUnitsSet_coe A (mul_mem_integralUnitsSet_coe A (unip₂_mem_integralUnitsSet A hαzz₀) hα1) hu,
    ?_⟩
  rw [← diag₂_mul_unip₂_eq_tri₂, hrα, hdd, mul_assoc (diag₂ r₀ 1) (diag₂ α 1) (unip₂ z), diag₂_mul_unip₂ α z,
    hsplit]
  simp only [mul_assoc]

end Regimes

section FiniteDoubleCosets

variable {F : Type*} [Field F]

private theorem exists_finset_forall_exists_of_forall_mul_apply_mem [TopologicalSpace F] [IsTopologicalRing F]
    [T2Space F] [ContinuousInv₀ F] (A : ValuationSubring F) (hAc : IsCompact (A : Set F))
    (hAo : IsOpen (A : Set F)) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : AutomorphicForm.IsRegularSemisimple γ) {d : F} (hd : d ≠ 0) :
    ∃ S₀ : Finset (Matrix.GeneralLinearGroup (Fin 2) F),
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ i j, d * ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ A) →
          ∃ s ∈ S₀, ∃ t ∈ Subgroup.centralizer ({γ} : Set (Matrix.GeneralLinearGroup (Fin 2) F)),
            ∃ u ∈ AutomorphicForm.integralUnitsSet (A : Set F), x = t * s * u := by
  rcases exists_inv_mul_mul_eq_diag₂_or_forall_ne_zero γ hγ with ⟨h, l₁, l₂, hl, hconj⟩ | hroot
  · refine exists_finset_forall_exists_of_conj A (h := h) ?_
    rw [hconj]
    exact exists_finset_forall_exists_of_diag₂ A hAc hAo hl hd
  · exact exists_finset_forall_exists_of_forall_ne_zero A hAc hAo γ hroot hd

end FiniteDoubleCosets

end OrbitalSupport

open NumberField IsDedekindDomain MeasureTheory

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ g : GL (Fin 2) (v.adicCompletion K), f g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ AutomorphicForm.localIntegralSet K v) :
    ∃ S : Finset (GL (Fin 2) (v.adicCompletion K)),
     (
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s
     ) ∧
     (
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u
     ) := by
  obtain ⟨F₀, hF₀⟩ := hfs
  have hAc : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hAo : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v

  obtain ⟨d, -, hd, hbound⟩ := OrbitalSupport.exists_forall_mul_apply_mem_of_forall_exists
    (v.adicCompletionIntegers K) (fun g => f g ≠ 0) F₀ hF₀

  obtain ⟨S₀, hS₀⟩ := OrbitalSupport.exists_finset_forall_exists_of_forall_mul_apply_mem
    (v.adicCompletionIntegers K) hAc hAo γ hγ hd

  obtain ⟨S, hS₁, hS₂⟩ := OrbitalSupport.exists_finset_of_finset_forall_exists
    (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
    (AutomorphicForm.localIntegralSet K v) (AutomorphicForm.one_mem_localIntegralSet K v)
    (fun _ ha _ hb => OrbitalSupport.mul_mem_integralUnitsSet_coe (v.adicCompletionIntegers K) ha hb)
    (fun x => f (x⁻¹ * γ * x) ≠ 0) S₀ (fun x hx => hS₀ x (hbound (x⁻¹ * γ * x) hx))
  exact ⟨S, hS₁, hS₂⟩

end S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple (solution)
