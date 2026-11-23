-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:54.769665+00:00
-- url     : https://prove2.me/theorems/479bcab4-eb12-44a8-bcaf-a77549e0cd92
-- title:
--   Adjoint Radical
-- statement:
--   Definitions and structural lemmas for Adjoint Radical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/AdjointRadical.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
section Algebra
variable {k : Type} [Field k] {r : ℕ} (b : Fin r → ℕ)
variable (k) in

def lieRadical : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, ¬ b i < b j → X i j = 0}
  add_mem' := by
    intro X Y hX hY i j h
    simp [hX i j h, hY i j h]
  zero_mem' := by intro i j _; rfl
  smul_mem' := by
    intro c X hX i j h
    simp [hX i j h]
variable {b}
theorem mul_mem_lieRadical {A X : Matrix (Fin r) (Fin r) k} (hA : A.BlockTriangular b)
    (hX : X ∈ lieRadical k b) : A * X ∈ lieRadical k b := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b l < b i
  · rw [hA hl, zero_mul]
  · rw [hX l j (by omega), mul_zero]
theorem mem_lieRadical_mul {A X : Matrix (Fin r) (Fin r) k} (hX : X ∈ lieRadical k b)
    (hA : A.BlockTriangular b) : X * A ∈ lieRadical k b := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b j < b l
  · rw [hA hl, mul_zero]
  · rw [hX i l (by omega), zero_mul]
theorem blockTriangular_inv {α : Type} [LinearOrder α] {c : Fin r → α} {g : GL (Fin r) k}
    (hg : (g : Matrix (Fin r) (Fin r) k).BlockTriangular c) :
    ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular c := by
  letI := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg
theorem blockTriangular_of_sub_one {A : Matrix (Fin r) (Fin r) k} (h : A - 1 ∈ lieRadical k b) :
    A.BlockTriangular b := by
  intro i j hij
  have h1 := h i j (by omega)
  have hne : i ≠ j := by rintro rfl; omega
  simpa [Matrix.one_apply_ne hne] using h1
variable (k b) in

def radical : Subgroup (GL (Fin r) k) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) k) - 1 ∈ lieRadical k b}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    have e : ((g * h : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1
        = (g : Matrix (Fin r) (Fin r) k) * ((h : Matrix (Fin r) (Fin r) k) - 1)
          + ((g : Matrix (Fin r) (Fin r) k) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one]; abel
    show _ ∈ lieRadical k b
    rw [e]
    exact add_mem (mul_mem_lieRadical (blockTriangular_of_sub_one hg) hh) hg
  inv_mem' := by
    intro g hg
    have e : ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1
        = -(((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
          * ((g : Matrix (Fin r) (Fin r) k) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul]; abel
    show _ ∈ lieRadical k b
    rw [e]
    exact neg_mem (mul_mem_lieRadical (blockTriangular_inv (blockTriangular_of_sub_one hg)) hg)
variable (k b) in

def levi : Subgroup (GL (Fin r) k) where
  carrier := {g | ∀ i j, b i ≠ b j → (g : Matrix (Fin r) (Fin r) k) i j = 0}
  one_mem' := by
    intro i j h
    have hne : i ≠ j := by rintro rfl; exact h rfl
    simp [Matrix.one_apply_ne hne]
  mul_mem' := by
    intro g h hg hh i j hij
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : b i = b l
    · rw [hh l j (by omega), mul_zero]
    · rw [hg i l hl, zero_mul]
  inv_mem' := by
    intro g hg i j hij
    have h1 : (g : Matrix (Fin r) (Fin r) k).BlockTriangular b := fun i j h => hg i j (by omega)
    have h2 : (g : Matrix (Fin r) (Fin r) k).BlockTriangular (OrderDual.toDual ∘ b) :=
      fun i j h => hg i j (ne_of_lt h)
    rcases lt_or_gt_of_ne hij with h | h
    · exact blockTriangular_inv h2 h
    · exact blockTriangular_inv h1 h
theorem levi_blockTriangular (δ : levi k b) :
    ((δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular b :=
  fun i j h => δ.2 i j (by omega)
def adRadical (δ : levi k b) : lieRadical k b →ₗ[k] lieRadical k b where
  toFun X := ⟨((δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (X : Matrix (Fin r) (Fin r) k)
      * (((δ⁻¹ : levi k b) : GL (Fin r) k) : Matrix (Fin r) (Fin r) k),
    mem_lieRadical_mul (mul_mem_lieRadical (levi_blockTriangular δ) X.2)
      (levi_blockTriangular δ⁻¹)⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp
theorem conj_mem_radical (δ : levi k b) {n : GL (Fin r) k} (hn : n ∈ radical k b) :
    (δ : GL (Fin r) k)⁻¹ * n * δ ∈ radical k b := by
  have e : (((δ : GL (Fin r) k)⁻¹ * n * δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1
      = (((δ⁻¹ : levi k b) : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        * ((n : Matrix (Fin r) (Fin r) k) - 1) * ((δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
    rw [mul_sub, sub_mul, mul_one, Subgroup.coe_inv, Units.inv_mul, Units.val_mul, Units.val_mul]
  show _ ∈ lieRadical k b
  rw [e]
  exact mem_lieRadical_mul (mul_mem_lieRadical (levi_blockTriangular δ⁻¹) hn)
    (levi_blockTriangular δ)
def twistedCommutator (δ : levi k b) (n : radical k b) : radical k b :=
  ⟨(δ : GL (Fin r) k)⁻¹ * (n : GL (Fin r) k)⁻¹ * δ * n,
    mul_mem (conj_mem_radical δ (inv_mem n.2)) n.2⟩
end Algebra
noncomputable def modulus (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
    [LocallyCompactSpace k] (x : k) : ℝ :=
  open Classical in
  if h : x = 0 then 0 else (distribHaarChar k (Units.mk0 x h) : ℝ)
def UnipotentChangeOfVariables : Prop :=
  ∀ (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] [T2Space k]
    [LocallyCompactSpace k] [SecondCountableTopology k], ¬ DiscreteTopology k →
    ∀ (r : ℕ) (b : Fin r → ℕ) (δ : levi k b),
      Function.Bijective (adRadical δ - LinearMap.id : lieRadical k b →ₗ[k] lieRadical k b) →
      IsHomeomorph (twistedCommutator δ) ∧
      ∀ [MeasurableSpace (radical k b)] [BorelSpace (radical k b)]
        (μ : Measure (radical k b)) [μ.IsHaarMeasure] (φ : radical k b → ℂ),
        Continuous φ → HasCompactSupport φ →
        ∫ n, φ (twistedCommutator δ n) ∂μ =
          (((modulus k (LinearMap.det
            (LinearMap.id - adRadical δ⁻¹ : lieRadical k b →ₗ[k] lieRadical k b)))⁻¹ : ℝ) : ℂ)
            * ∫ n, φ n ∂μ
def RegularLeviNoEigenvalueOne : Prop :=
  ∀ (k : Type) [Field k] (r : ℕ) (b : Fin r → ℕ) (γ m : levi k b),
    ((γ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).charpoly.Separable →
    ¬ Module.End.HasEigenvalue (adRadical (m⁻¹ * γ * m)) 1
example : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ∈ lieRadical ℝ (fun i : Fin 2 => (i : ℕ)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all
example (h : UnipotentChangeOfVariables) (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → ℕ) :
    (∀ δ : levi ℝ b, Function.Bijective
      (adRadical δ - LinearMap.id : lieRadical ℝ b →ₗ[ℝ] lieRadical ℝ b) →
        IsHomeomorph (twistedCommutator δ)) ∧
    (∀ δ : levi ℚ_[p] b, Function.Bijective
      (adRadical δ - LinearMap.id : lieRadical ℚ_[p] b →ₗ[ℚ_[p]] lieRadical ℚ_[p] b) →
        IsHomeomorph (twistedCommutator δ)) := by
  have nd : ∀ (k : Type) [NontriviallyNormedField k], ¬ DiscreteTopology k := fun k _ hk => by
    have h0 : (nhdsWithin (0 : k) {0}ᶜ).NeBot := inferInstance
    exact h0.ne (discreteTopology_iff_nhds_ne.1 hk 0)
  exact ⟨fun δ hδ => (h ℝ (nd ℝ) r b δ hδ).1, fun δ hδ => (h ℚ_[p] (nd _) r b δ hδ).1⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical


