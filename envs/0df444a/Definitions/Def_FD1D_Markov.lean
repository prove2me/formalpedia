-- Prove2me | Definitions.Def_FD1D_Markov
-- name    : FD1D_Markov
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:37:36.628499+00:00
-- url     : https://prove2.me/theorems/f5afd72f-011a-5f54-bb46-bda5531b9b21
-- title:
--   Markov
-- statement:
--   Definitions and structural lemmas for Markov, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean

import Definitions.Def_FD1D_Basic
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
@[ext]
theorem ext {μ ν : FiniteLaw α} (h : ∀ x, μ.mass x = ν.mass x) : μ = ν := by
  cases μ with
  | mk mass hnon hsum =>
      cases ν with
      | mk mass' hnon' hsum' =>
          have hm : mass = mass' := funext h
          subst mass'
          rfl
def dirac [DecidableEq α] (x : α) : FiniteLaw α where
  mass y := if y = x then 1 else 0
  mass_nonneg y := by split_ifs <;> positivity
  sum_mass := by simp
@[simp]
theorem mass_dirac [DecidableEq α] (x y : α) :
    (dirac x : FiniteLaw α).mass y = if y = x then 1 else 0 :=
  rfl
def uniform [Nonempty α] : FiniteLaw α where
  mass _ := 1 / Fintype.card α
  mass_nonneg _ := by positivity
  sum_mass := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card α : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp
@[simp]
theorem mass_uniform [Nonempty α] (x : α) :
    (uniform : FiniteLaw α).mass x = 1 / Fintype.card α :=
  rfl
def map [DecidableEq β] (f : α → β) (μ : FiniteLaw α) : FiniteLaw β where
  mass y := ∑ x with f x = y, μ.mass x
  mass_nonneg y := Finset.sum_nonneg fun x _ => μ.mass_nonneg x
  sum_mass := by
    classical
    rw [Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (s := Finset.univ)
      (g := f) (f := μ.mass) (by simp)]
    exact μ.sum_mass
@[simp]
theorem mass_map [DecidableEq β] (f : α → β) (μ : FiniteLaw α) (y : β) :
    (μ.map f).mass y = ∑ x with f x = y, μ.mass x :=
  rfl
end FiniteLaw
structure FiniteKernel (α : Type*) [Fintype α] where
  trans : α → α → ℝ
  trans_nonneg : ∀ x y, 0 ≤ trans x y
  sum_trans : ∀ x, ∑ y, trans x y = 1
namespace FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
instance : CoeFun (FiniteKernel α) fun _ => α → α → ℝ :=
  ⟨FiniteKernel.trans⟩
def matrix (K : FiniteKernel α) : Matrix α α ℝ := K.trans
def step (K : FiniteKernel α) (μ : FiniteLaw α) : FiniteLaw α where
  mass y := ∑ x, μ.mass x * K x y
  mass_nonneg y :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.mass_nonneg x) (K.trans_nonneg x y)
  sum_mass := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, K.sum_trans, mul_one]
    exact μ.sum_mass
@[simp]
theorem mass_step (K : FiniteKernel α) (μ : FiniteLaw α) (y : α) :
    (K.step μ).mass y = ∑ x, μ.mass x * K x y :=
  rfl
def iterate (K : FiniteKernel α) : ℕ → FiniteLaw α → FiniteLaw α
  | 0, μ => μ
  | n + 1, μ => K.step (K.iterate n μ)
@[simp]
theorem iterate_zero (K : FiniteKernel α) (μ : FiniteLaw α) :
    K.iterate 0 μ = μ :=
  rfl
@[simp]
theorem iterate_succ (K : FiniteKernel α) (n : ℕ) (μ : FiniteLaw α) :
    K.iterate (n + 1) μ = K.step (K.iterate n μ) :=
  rfl
def pow [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x y : α) : ℝ :=
  (K.matrix ^ n) x y
@[simp]
theorem pow_zero [DecidableEq α] (K : FiniteKernel α) (x y : α) :
    K.pow 0 x y = if x = y then 1 else 0 := by
  simp [pow, Matrix.one_apply]
@[simp]
theorem pow_one [DecidableEq α] (K : FiniteKernel α) (x y : α) :
    K.pow 1 x y = K x y := by
  change (K.matrix ^ 1) x y = K x y
  rw [_root_.pow_one]
  rfl
theorem pow_add [DecidableEq α] (K : FiniteKernel α) (m n : ℕ) (x z : α) :
    K.pow (m + n) x z = ∑ y, K.pow m x y * K.pow n y z := by
  change (K.matrix ^ (m + n)) x z =
    ∑ y, (K.matrix ^ m) x y * (K.matrix ^ n) y z
  rw [_root_.pow_add, Matrix.mul_apply]
theorem mass_iterate [DecidableEq α] (K : FiniteKernel α)
    (n : ℕ) (μ : FiniteLaw α) (y : α) :
    (K.iterate n μ).mass y = ∑ x, μ.mass x * K.pow n x y := by
  induction n generalizing y with
  | zero =>
      simp [pow_zero]
  | succ n ih =>
      rw [iterate_succ, mass_step]
      simp_rw [ih]
      have hpow (x : α) :
          K.pow (n + 1) x y = ∑ z, K.pow n x z * K z y := by
        rw [K.pow_add n 1]
        simp only [FiniteKernel.pow_one]
      simp_rw [hpow]
      simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
def IsStationary (K : FiniteKernel α) (μ : FiniteLaw α) : Prop :=
  K.step μ = μ
theorem IsStationary.iterate {K : FiniteKernel α} {μ : FiniteLaw α}
    (h : K.IsStationary μ) (n : ℕ) : K.iterate n μ = μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ, ih, h]
def orbit [DecidableEq α] (K : FiniteKernel α) (μ : FiniteLaw α)
    (n : ℕ) : α → ℝ :=
  μ.mass ᵥ* K.matrix ^ n
theorem orbit_eq_iterate [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    K.orbit μ n x = (K.iterate n μ).mass x := by
  rw [mass_iterate]
  rfl
theorem orbit_nonneg [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    0 ≤ K.orbit μ n x := by
  rw [orbit_eq_iterate]
  exact (K.iterate n μ).mass_nonneg x
theorem sum_orbit [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    ∑ x, K.orbit μ n x = 1 := by
  simpa only [orbit_eq_iterate] using (K.iterate n μ).sum_mass
def cesaroVec [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) : α → ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ •
    ∑ k ∈ Finset.range (n + 1), K.orbit μ k
def cesaroLaw [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) : FiniteLaw α where
  mass := K.cesaroVec μ n
  mass_nonneg x := by
    apply mul_nonneg
    · positivity
    · simp only [Finset.sum_apply]
      exact Finset.sum_nonneg fun k _ => K.orbit_nonneg μ k x
  sum_mass := by
    simp only [cesaroVec, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [K.sum_orbit μ]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by positivity)
def Reaches [DecidableEq α] (K : FiniteKernel α) (x y : α) : Prop :=
  ∃ n : ℕ, 0 < K.pow n x y
def Irreducible [DecidableEq α] (K : FiniteKernel α) : Prop :=
  ∀ x y, K.Reaches x y
def HasPositiveLoops (K : FiniteKernel α) : Prop :=
  ∀ x, 0 < K x x
def Equivariant (K : FiniteKernel α) (e : Equiv.Perm α) : Prop :=
  ∀ x y, K (e x) (e y) = K x y
def LawInvariant (μ : FiniteLaw α) (e : Equiv.Perm α) : Prop :=
  ∀ x, μ.mass (e x) = μ.mass x
def GroupInvariant {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (μ : FiniteLaw α) : Prop :=
  ∀ g, LawInvariant μ (ρ g)
def GroupEquivariant {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (K : FiniteKernel α) : Prop :=
  ∀ g, K.Equivariant (ρ g)
end FiniteKernel
abbrev InventoryState (ι : Type*) [Fintype ι] (m : ℕ) :=
  {x : ι → ℕ // ∑ i, x i = m}
namespace InventoryState
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[ext]
theorem ext {m : ℕ} {x y : InventoryState ι m}
    (h : ∀ i, x.1 i = y.1 i) : x = y :=
  Subtype.ext (funext h)
instance (m : ℕ) : Fintype (InventoryState ι m) := by
  let encode : InventoryState ι m → (ι → Fin (m + 1)) := fun x i =>
    ⟨x.1 i, by
      rw [Nat.lt_succ_iff]
      calc
        x.1 i ≤ ∑ j, x.1 j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = m := x.2⟩
  exact Fintype.ofInjective encode fun x y h => by
    apply ext
    intro i
    exact congrArg Fin.val (congrFun h i)
instance (m : ℕ) : DecidableEq (InventoryState ι m) :=
  Classical.decEq _
def move {m : ℕ} (x : InventoryState ι m) (d a : ι) : InventoryState ι m :=
  if hd : 0 < x.1 d then
    let removed := Function.update x.1 d (x.1 d - 1)
    ⟨Function.update removed a (removed a + 1), by
      have hremoved : ∑ i, removed i = m - 1 := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ d)]
        have hx :=
          Finset.sum_erase_add Finset.univ x.1 (Finset.mem_univ d)
        rw [x.2] at hx
        simp only [Finset.sdiff_singleton_eq_erase]
        omega
      rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
      have hr :=
        Finset.sum_erase_add Finset.univ removed (Finset.mem_univ a)
      rw [hremoved] at hr
      simp only [Finset.sdiff_singleton_eq_erase]
      have hmpos : 0 < m := by
        calc
          0 < x.1 d := hd
          _ ≤ ∑ i, x.1 i :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
          _ = m := x.2
      omega⟩
  else x
@[simp]
theorem move_empty {m : ℕ} (x : InventoryState ι m) {d a : ι}
    (hd : x.1 d = 0) : move x d a = x := by
  simp [move, hd]
@[simp]
theorem move_self {m : ℕ} (x : InventoryState ι m) (d : ι) :
    move x d d = x := by
  by_cases hd : 0 < x.1 d
  · rw [move, dif_pos hd]
    apply ext
    intro i
    by_cases hi : i = d
    · subst i
      simp [Function.update_apply]
      omega
    · simp [Function.update_apply, hi]
  · simp [move, hd]
end InventoryState
structure DeletionRule (ι : Type*) [Fintype ι] (m : ℕ) where
  prob : InventoryState ι m → ι → ℝ
  nonneg : ∀ x i, 0 ≤ prob x i
  empty : ∀ x i, x.1 i = 0 → prob x i = 0
  occupied_pos : ∀ x i, 0 < x.1 i → 0 < prob x i
  sum_prob : ∀ x, ∑ i, prob x i = 1
namespace DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
def kernel (R : DeletionRule ι m) : FiniteKernel (InventoryState ι m) where
  trans x y :=
    ∑ d, ∑ a, if InventoryState.move x d a = y then
      R.prob x d * (1 / Fintype.card ι : ℝ) else 0
  trans_nonneg x y := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mul_nonneg (R.nonneg x d) (by positivity)
    · positivity
  sum_trans x := by
    classical
    calc
      ∑ y, ∑ d, ∑ a, (if InventoryState.move x d a = y then
          R.prob x d * (1 / Fintype.card ι : ℝ) else 0) =
          ∑ d, ∑ a, ∑ y, (if InventoryState.move x d a = y then
            R.prob x d * (1 / Fintype.card ι : ℝ) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_comm]
      _ = ∑ d, ∑ a, R.prob x d * (1 / Fintype.card ι : ℝ) := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro a _
        simp
      _ = 1 := by
        have hinner (d : ι) :
            (∑ _a : ι, R.prob x d * (1 / Fintype.card ι : ℝ)) =
              R.prob x d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (Fintype.card ι : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          field_simp
        simp_rw [hinner]
        exact R.sum_prob x
end DeletionRule
end
end FD1D


