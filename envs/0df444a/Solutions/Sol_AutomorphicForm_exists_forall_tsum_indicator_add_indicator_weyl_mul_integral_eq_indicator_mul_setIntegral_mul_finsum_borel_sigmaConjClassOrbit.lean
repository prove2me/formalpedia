-- Prove2me | solution 1 for AutomorphicForm.exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fe16ebd3-0a7d-52bf-9f5a-d8b4b4a3675c

import Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
import Theorems.Thm_LT_TwistedNorm_exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit

set_option autoImplicit false

noncomputable section

namespace R4WeightRegroup

set_option maxHeartbeats 1600000

open MeasureTheory NumberField Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

section FieldAlgebra

variable {L : Type} [Field L]

abbrev wL : GL (Fin 2) L := AutomorphicForm.gl2Weyl

theorem wL_inv : (wL : GL (Fin 2) L)⁻¹ = wL := AutomorphicForm.gl2Weyl_inv

theorem wL_mul_wL : (wL : GL (Fin 2) L) * wL = 1 := by
  calc (wL : GL (Fin 2) L) * wL = (wL : GL (Fin 2) L)⁻¹⁻¹ * wL := by rw [inv_inv]
    _ = 1 := by rw [wL_inv]; exact inv_mul_cancel _

theorem mul_wL_apply (m : GL (Fin 2) L) (i : Fin 2) :
    ((m * wL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0 = (m : Matrix (Fin 2) (Fin 2) L) i 1 ∧
      ((m * wL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 1 = (m : Matrix (Fin 2) (Fin 2) L) i 0 := by
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.gl2Weyl_val]

theorem wL_mul_apply (m : GL (Fin 2) L) (j : Fin 2) :
    ((wL * m : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 j = (m : Matrix (Fin 2) (Fin 2) L) 1 j ∧
      ((wL * m : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 j = (m : Matrix (Fin 2) (Fin 2) L) 0 j := by
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.gl2Weyl_val]

theorem wL_apply_one_zero : ((wL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 1 := by
  simp [AutomorphicForm.gl2Weyl_val]

abbrev BL (L : Type) [Field L] : Subgroup (GL (Fin 2) L) := AutomorphicForm.borelSubgroup L

theorem mem_BL {m : GL (Fin 2) L} : m ∈ BL L ↔ (m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := Iff.rfl

theorem wL_notMem_BL : (wL : GL (Fin 2) L) ∉ BL L := by
  rw [mem_BL, wL_apply_one_zero]; exact one_ne_zero

theorem scalar_comm (u : Lˣ) (g : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (u : L) (fun r' => Commute.all _ r') _).eq

theorem scalar_mem_center (u : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.center (GL (Fin 2) L) :=
  Subgroup.mem_center_iff.mpr fun g => (scalar_comm u g).symm

theorem exists_scalar_of_mem_center {s : GL (Fin 2) L} (hs : s ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ u : Lˣ, s = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  exact ⟨u, hu.symm⟩

theorem scalar_mem_BL (u : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ BL L := by
  rw [mem_BL]
  show Matrix.scalar (Fin 2) (u : L) 1 0 = 0
  simp [Matrix.scalar_apply]

theorem mem_BL_of_diag {d : GL (Fin 2) L} (hd : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : d ∈ BL L := hd

theorem wL_mul_mul_wL_mem_BL {d : GL (Fin 2) L} (hd : (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    wL * d * wL ∈ BL L := by
  rw [mem_BL, (mul_wL_apply (wL * d) 1).1, (wL_mul_apply d 1).2, hd]

theorem wL_mul_inv_mul_wL_mem_BL {d : GL (Fin 2) L} (hd : (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    wL * d⁻¹ * wL ∈ BL L := by
  have : wL * d⁻¹ * wL = (wL * d * wL : GL (Fin 2) L)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, wL_inv, mul_assoc]
  rw [this]
  exact (BL L).inv_mem (wL_mul_mul_wL_mem_BL hd)

theorem wL_mul_mem_BL_of_antidiag {a : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 0 0 = 0) :
    wL * a ∈ BL L := by
  rw [mem_BL, (wL_mul_apply a 0).2, ha]

theorem mul_wL_mem_BL_of_antidiag {a : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) :
    a * wL ∈ BL L := by
  rw [mem_BL, (mul_wL_apply a 1).1, ha]

def Q (γ : GL (Fin 2) L) : Prop := γ ∈ BL L ∨ γ * wL ∈ BL L

theorem not_and_of_Q {γ : GL (Fin 2) L} (h1 : γ ∈ BL L) (h2 : γ * wL ∈ BL L) : False := by
  have : (wL : GL (Fin 2) L) ∈ BL L := by
    have := (BL L).mul_mem ((BL L).inv_mem h1) h2
    rwa [inv_mul_cancel_left] at this
  exact wL_notMem_BL this

theorem Q_of_Q_mul {γ lam : GL (Fin 2) L}
    (hlam : ((lam : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (lam : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((lam : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (lam : Matrix (Fin 2) (Fin 2) L) 1 1 = 0))
    (h : Q (γ * lam)) : Q γ := by
  rcases h with h | h
  · rcases hlam with ⟨h10, h01⟩ | ⟨h00, h11⟩
    ·
      left
      have := (BL L).mul_mem h ((BL L).inv_mem (mem_BL_of_diag h10))
      rwa [mul_inv_cancel_right] at this
    ·
      right
      have := (BL L).mul_mem h ((BL L).inv_mem (wL_mul_mem_BL_of_antidiag h00))
      rwa [mul_inv_rev, wL_inv, ← mul_assoc, mul_inv_cancel_right] at this
  · rcases hlam with ⟨h10, h01⟩ | ⟨h00, h11⟩
    ·
      right
      have := (BL L).mul_mem h (wL_mul_inv_mul_wL_mem_BL h01)
      have e : γ * lam * wL * (wL * lam⁻¹ * wL) = γ * wL := by
        calc γ * lam * wL * (wL * lam⁻¹ * wL) = γ * lam * (wL * wL) * lam⁻¹ * wL := by simp only [mul_assoc]
          _ = γ * wL := by rw [wL_mul_wL, mul_one, mul_inv_cancel_right]
      rwa [e] at this
    ·
      left
      have := (BL L).mul_mem h ((BL L).inv_mem (mul_wL_mem_BL_of_antidiag h11))
      rwa [mul_inv_rev, wL_inv, ← mul_assoc, mul_assoc (γ * lam), wL_mul_wL, mul_one, mul_inv_cancel_right] at this

end FieldAlgebra

section Class

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
variable (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
  (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
  (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
  (I : Set (GL (Fin 2) L))
  (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
    δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
  (Λ : Subgroup (GL (Fin 2) L))
  (hΛ : ∀ γ, γ ∈ Λ ↔
    δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
  {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)

abbrev σG (σ : L ≃ₐ[K] L) : GL (Fin 2) L →* GL (Fin 2) L := Matrix.GeneralLinearGroup.map (σ : L →+* L)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem σG_apply (σ : L ≃ₐ[K] L) (m : GL (Fin 2) L) (i j : Fin 2) :
    ((σG σ m : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = σ ((m : Matrix (Fin 2) (Fin 2) L) i j) := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem σG_wL (σ : L ≃ₐ[K] L) : σG σ (wL : GL (Fin 2) L) = wL := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [σG_apply]
  fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.gl2Weyl_val]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem σG_mem_BL (σ : L ≃ₐ[K] L) {m : GL (Fin 2) L} (hm : m ∈ BL L) : σG σ m ∈ BL L := by
  rw [mem_BL, σG_apply, mem_BL.mp hm, map_zero]

abbrev twL : GL (Fin 2) L := wL * δ₀ * wL

omit [FiniteDimensional K L] [IsGalois K L] in
include hδ₀u hδ₀l in
theorem twL_entries :
    (((twL δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((twL δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
    ((twL δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 ∧
    ((twL δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [(mul_wL_apply (wL * δ₀) 1).1, (wL_mul_apply δ₀ 1).2, hδ₀l]
  · rw [(mul_wL_apply (wL * δ₀) 0).2, (wL_mul_apply δ₀ 0).1, hδ₀u]
  · rw [(mul_wL_apply (wL * δ₀) 0).1, (wL_mul_apply δ₀ 1).1]
  · rw [(mul_wL_apply (wL * δ₀) 1).2, (wL_mul_apply δ₀ 0).2]

include hgen hδ₀u hδ₀l hreg hΛ in

theorem diag_or_antidiag_of_mem {lam : GL (Fin 2) L} (hlam : lam ∈ Λ) :
    ((lam : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (lam : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((lam : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (lam : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) := by
  have h := (LT.TwistedNorm.exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
    hgen δ₀ hδ₀u hδ₀l hreg).2 lam
  rcases h.mp ((hΛ lam).mp hlam) with ⟨hd, -⟩ | ⟨h00, h11, -⟩
  · exact Or.inl hd
  · exact Or.inr ⟨h00, h11⟩

def SQ : Set ι := {i | Q (r i)}

def famSet (S : Set ι) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | ∃ i ∈ S,
    δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈ Subgroup.center (GL (Fin 2) L)}

omit [FiniteDimensional K L] [IsGalois K L] in
include hδ₀u hδ₀l in

theorem apply_one_zero_eq_zero_of_mem_famSet {δ : GL (Fin 2) L} (hδ : δ ∈ famSet δ₀ r (σ := σ) (SQ r)) :
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  obtain ⟨i, hi, hδi⟩ := hδ
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hδi

  have hδeq : δ = r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG σ (r i))⁻¹ := by
    have h1 : (r i)⁻¹ * δ * σG σ (r i) = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      rw [← hu, mul_inv_cancel_left]
    calc δ = r i * ((r i)⁻¹ * δ * σG σ (r i)) * (σG σ (r i))⁻¹ := by group
      _ = _ := by rw [h1, ← mul_assoc]
  rw [← mem_BL, hδeq]
  rcases hi with hB | hBw
  · exact (BL L).mul_mem ((BL L).mul_mem ((BL L).mul_mem hB hδ₀u) (scalar_mem_BL u))
      ((BL L).inv_mem (σG_mem_BL σ hB))
  ·
    set b : GL (Fin 2) L := r i * wL with hb
    have hri : r i = b * wL := by rw [hb, mul_assoc, wL_mul_wL, mul_one]
    have e : r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG σ (r i))⁻¹ =
        b * (wL * δ₀ * wL) * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG σ b)⁻¹ := by
      rw [hri, map_mul, σG_wL, mul_inv_rev, wL_inv]
      have hc := scalar_comm u (wL : GL (Fin 2) L)
      calc b * wL * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (wL * (σG σ b)⁻¹)
          = b * wL * δ₀ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u * wL) * (σG σ b)⁻¹ := by
            simp only [mul_assoc]
        _ = b * wL * δ₀ * (wL * Matrix.GeneralLinearGroup.scalar (Fin 2) u) * (σG σ b)⁻¹ := by rw [hc]
        _ = _ := by simp only [mul_assoc]
    rw [e]
    exact (BL L).mul_mem ((BL L).mul_mem ((BL L).mul_mem hBw (wL_mul_mul_wL_mem_BL hδ₀l)) (scalar_mem_BL u))
      ((BL L).inv_mem (σG_mem_BL σ hBw))

include hgen hδ₀u hδ₀l hreg hΛ hr in

theorem mem_famSet_of_conj {γ g : GL (Fin 2) L} (hQ : Q g)
    (hg : δ₀⁻¹ * (g⁻¹ * γ * σG σ g) ∈ Subgroup.center (GL (Fin 2) L)) :
    γ ∈ famSet δ₀ r (σ := σ) (SQ r) := by
  obtain ⟨i, hiΛ, -⟩ := hr g
  set lam : GL (Fin 2) L := (r i)⁻¹ * g with hlam
  have hg' : r i * lam = g := by rw [hlam, mul_inv_cancel_left]
  refine ⟨i, ?_, ?_⟩
  ·
    have hQ' : Q (r i * lam) := by rw [hg']; exact hQ
    exact Q_of_Q_mul (diag_or_antidiag_of_mem hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ hiΛ) hQ'
  ·
    obtain ⟨s, hs⟩ := exists_scalar_of_mem_center hg
    have hs' := (hΛ lam).mp hiΛ
    obtain ⟨s', hs'eq⟩ := exists_scalar_of_mem_center hs'
    have h1 : g⁻¹ * γ * σG σ g = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
      rw [← hs, mul_inv_cancel_left]
    have h2 : lam * δ₀ * (σG σ lam)⁻¹ = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) s' := by
      rw [← hs'eq, mul_inv_cancel_left]
    have hri : (r i)⁻¹ = lam * g⁻¹ := by rw [hlam, mul_inv_cancel_right]
    have hri' : r i = g * lam⁻¹ := by rw [← hg', hlam, mul_inv_cancel_left, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    have key : (r i)⁻¹ * γ * σG σ (r i) =
        δ₀ * (Matrix.GeneralLinearGroup.scalar (Fin 2) s' * Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
      rw [hri, hri', map_mul, map_inv]
      have hc := scalar_comm s ((σG σ lam)⁻¹)
      calc lam * g⁻¹ * γ * (σG σ g * (σG σ lam)⁻¹)
          = lam * (g⁻¹ * γ * σG σ g) * (σG σ lam)⁻¹ := by simp only [mul_assoc]
        _ = lam * δ₀ * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * (σG σ lam)⁻¹) := by
            rw [h1]; simp only [mul_assoc]
        _ = lam * δ₀ * (σG σ lam)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
            rw [hc]; simp only [mul_assoc]
        _ = _ := by rw [h2, mul_assoc]
    show δ₀⁻¹ * ((r i)⁻¹ * γ * σG σ (r i)) ∈ Subgroup.center (GL (Fin 2) L)
    rw [key, inv_mul_cancel_left]
    exact (Subgroup.center (GL (Fin 2) L)).mul_mem (scalar_mem_center s') (scalar_mem_center s)

include hgen hδ₀u hδ₀l hreg hI hΛ hr in

theorem mem_famSet_of_apply_one_zero_eq_zero {γ : GL (Fin 2) L} (hγ : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hγI : γ ∈ I) : γ ∈ famSet δ₀ r (σ := σ) (SQ r) := by
  obtain ⟨⟨htw10, htw01⟩, htw00, htw11⟩ := twL_entries δ₀ hδ₀u hδ₀l
  have hdict := (LT.TwistedNorm.setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
    hgen δ₀ (twL δ₀) hδ₀u hδ₀l hreg ⟨htw10, htw01⟩ htw00 htw11).1
  have hmem : γ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} :=
    ⟨hγ, (hI γ).mp hγI⟩
  rw [hdict] at hmem
  rcases hmem with ⟨b, hb, hbc⟩ | ⟨b, hb, hbc⟩
  · exact mem_famSet_of_conj hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ r hr (Or.inl hb) hbc
  ·
    refine mem_famSet_of_conj hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ r hr (g := b * wL) (Or.inr ?_) ?_
    · rwa [mul_assoc, wL_mul_wL, mul_one]
    · have e : δ₀⁻¹ * ((b * wL)⁻¹ * γ * σG σ (b * wL)) =
          wL * ((twL δ₀)⁻¹ * (b⁻¹ * γ * σG σ b)) * wL := by
        rw [map_mul, σG_wL, mul_inv_rev, wL_inv]
        show δ₀⁻¹ * (wL * b⁻¹ * γ * (σG σ b * wL)) = wL * ((wL * δ₀ * wL)⁻¹ * (b⁻¹ * γ * σG σ b)) * wL
        rw [mul_inv_rev, mul_inv_rev, wL_inv]
        calc δ₀⁻¹ * (wL * b⁻¹ * γ * (σG σ b * wL))
            = (wL * wL) * δ₀⁻¹ * (wL * b⁻¹ * γ * (σG σ b * wL)) := by rw [wL_mul_wL, one_mul]
          _ = wL * (wL * (δ₀⁻¹ * wL) * (b⁻¹ * γ * σG σ b)) * wL := by simp only [mul_assoc]
      rw [e]
      have hcomm := Subgroup.mem_center_iff.mp hbc (wL : GL (Fin 2) L)
      rw [mul_assoc, ← hcomm, ← mul_assoc, wL_mul_wL, one_mul]
      exact hbc

include hgen hδ₀u hδ₀l hreg hI hΛ hr in

theorem famSet_SQ_eq :
    famSet δ₀ r (σ := σ) (SQ r) = {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I} := by
  ext γ
  constructor
  · intro hγ
    refine ⟨apply_one_zero_eq_zero_of_mem_famSet δ₀ hδ₀u hδ₀l r hγ, ?_⟩
    obtain ⟨i, -, hi⟩ := hγ
    exact (hI γ).mpr ⟨r i, hi⟩
  · rintro ⟨hγ, hγI⟩
    exact mem_famSet_of_apply_one_zero_eq_zero hgen δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr hγ hγI

end Class

section Reduction

variable (L : Type) [Field L] [NumberField L]

theorem lt_adelicHeight_globalPoints_mul_iff {h₀ : ℝ} (hh₀ : 0 < h₀) {R : ℝ} (hR : h₀⁻¹ ≤ Real.exp R)
    {x : AutomorphicForm.AdelicGL2 (𝓞 L) L} (hx : h₀ ≤ NumberField.AdelicHeight.adelicHeight L x)
    (γ : GL (Fin 2) L) :
    Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.globalPoints (𝓞 L) L γ * x) ↔
      γ ∈ BL L ∧ Real.exp R < NumberField.AdelicHeight.adelicHeight L x := by
  by_cases hγ : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
  · rw [NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup L hγ]
    exact ⟨fun h => ⟨hγ, h⟩, fun h => h.2⟩
  · have hle := NumberField.AdelicHeight.adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ x
    have hHx : 0 < NumberField.AdelicHeight.adelicHeight L x := NumberField.AdelicHeight.adelicHeight_pos x
    have h1 : NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.globalPoints (𝓞 L) L γ * x) ≤ h₀⁻¹ := by
      rw [le_inv_comm₀ (NumberField.AdelicHeight.adelicHeight_pos _) hh₀]
      calc h₀ ≤ NumberField.AdelicHeight.adelicHeight L x := hx
        _ ≤ (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.globalPoints (𝓞 L) L γ * x))⁻¹ := by
            rw [le_inv_comm₀ hHx (NumberField.AdelicHeight.adelicHeight_pos _), inv_eq_one_div,
              le_div_iff₀ hHx]
            exact hle
    constructor
    · intro h; exact absurd (h1.trans hR) (not_le.mpr h)
    · rintro ⟨h, -⟩; exact absurd h hγ

end Reduction

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
  (hΩL : IsFundamentalDomain
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
    z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
      ξL ⟨z, Subgroup.mem_top z⟩ = 1)
  (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
  (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
  (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
  (I : Set (GL (Fin 2) L))
  (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
    δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
  (Λ : Subgroup (GL (Fin 2) L))
  (hΛ : ∀ γ, γ ∈ Λ ↔
    δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
  {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
  (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)

def ξf (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)

def Fi (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (i : ι) : ℂ :=
  ∫ z, ξf L ξL z *
    φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL

def KB (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))

def indH (R : ℝ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
    (fun _ => (1 : ℂ)) y

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
open scoped Classical in
theorem indH_apply (R : ℝ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    indH L R y = if Real.exp R < NumberField.AdelicHeight.adelicHeight L y then 1 else 0 := by
  unfold indH
  rw [Set.indicator_apply]
  rfl

include hΩL hgen hξc hξt hc hTc hδ₀u hδ₀l hreg hI hΛ hr hφc hφs in
open scoped Classical in

theorem main :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ x ∈ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂,
        IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL ∧
        (∑' i : ι,
          (Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) +
            Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ
                (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))
            ∂νZL) =
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L

  obtain ⟨h₀, hh₀, hfloor⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact L c u d₁ d₂ hc Tc hTc
  refine ⟨Real.log h₀⁻¹, fun R hR x hx => ?_⟩

  have hindW : ∀ y : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
          Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
        (fun _ => (1 : ℂ)) y = indH L R (AutomorphicForm.adelicWeyl (𝓞 L) L * y) := by
    intro y
    unfold indH
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  simp_rw [hindW]
  show IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z * KB K L D σ I φ x z) ΩL νZL ∧
    (∑' i : ι,
      (indH L R ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) +
        indH L R (AutomorphicForm.adelicWeyl (𝓞 L) L * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) *
      Fi K L νZL D σ ξL δ₀ r φ x i) =
    indH L R x * ∫ z in ΩL, ξf L ξL z * KB K L D σ I φ x z ∂νZL
  have hRexp : h₀⁻¹ ≤ Real.exp R := by
    calc h₀⁻¹ = Real.exp (Real.log h₀⁻¹) := (Real.exp_log (inv_pos.mpr hh₀)).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hR
  have hxfloor : h₀ ≤ NumberField.AdelicHeight.adelicHeight L x := by
    obtain ⟨y, hyU⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hyU
    obtain ⟨g, hg, rfl⟩ := hxy
    exact hfloor g hg y hy
  have key := fun γ : GL (Fin 2) L => lt_adelicHeight_globalPoints_mul_iff L hh₀ hRexp hxfloor γ

  set S : Set ι := SQ r with hSdef
  have hAS := AutomorphicForm.integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
    K L νZL ΩL hΩL D σ ξL hξc hξt δ₀ Λ hΛ r hr S φ hφc hφs x
  obtain ⟨-, -, hint, hfold⟩ := hAS
  have hset : {δ : GL (Fin 2) L | ∃ i ∈ S,
      δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈ Subgroup.center (GL (Fin 2) L)} =
      {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I} :=
    famSet_SQ_eq hgen δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr
  have hKB : ∀ z, ∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ i ∈ S,
      δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈ Subgroup.center (GL (Fin 2) L)},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = KB K L D σ I φ x z :=
    fun z => finsum_mem_congr hset fun _ _ => rfl
  have hfun : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ i ∈ S,
        δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈ Subgroup.center (GL (Fin 2) L)},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) =
      fun z => ξf L ξL z * KB K L D σ I φ x z := funext fun z => by rw [hKB z]; rfl
  rw [hfun] at hint hfold
  refine ⟨hint, ?_⟩

  have hw : ∀ i : ι,
      indH L R ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) +
        indH L R (AutomorphicForm.adelicWeyl (𝓞 L) L * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) =
      indH L R x * S.indicator (fun _ => (1 : ℂ)) i := by
    intro i
    have e1 : (AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x =
        AutomorphicForm.globalPoints (𝓞 L) L (r i)⁻¹ * x := by rw [map_inv]
    have e2 : AutomorphicForm.adelicWeyl (𝓞 L) L * (AutomorphicForm.globalPoints (𝓞 L) L (r i)⁻¹ * x) =
        AutomorphicForm.globalPoints (𝓞 L) L (wL * (r i)⁻¹) * x := by
      rw [map_mul, mul_assoc]; rfl
    have k1 := key (r i)⁻¹
    have k2 := key (wL * (r i)⁻¹)

    have hb1 : (r i)⁻¹ ∈ BL L ↔ r i ∈ BL L := Subgroup.inv_mem_iff (BL L)
    have hb2 : wL * (r i)⁻¹ ∈ BL L ↔ r i * wL ∈ BL L := by
      rw [← Subgroup.inv_mem_iff (BL L), mul_inv_rev, inv_inv, wL_inv]
    rw [indH_apply, indH_apply, indH_apply, e1, e2, Set.indicator_apply]
    simp only [k1, k2, hb1, hb2]
    have hSi : i ∈ S ↔ (r i ∈ BL L ∨ r i * wL ∈ BL L) := Iff.rfl
    by_cases hHx : Real.exp R < NumberField.AdelicHeight.adelicHeight L x
    · by_cases hB : r i ∈ BL L
      · have hBw : ¬ r i * wL ∈ BL L := fun h => not_and_of_Q hB h
        simp [hHx, hB, hBw, hSi]
      · by_cases hBw : r i * wL ∈ BL L
        · simp [hHx, hB, hBw, hSi]
        · simp [hHx, hB, hBw, hSi]
    · simp [hHx]
  calc (∑' i : ι,
          (indH L R ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) +
            indH L R (AutomorphicForm.adelicWeyl (𝓞 L) L * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) *
          Fi K L νZL D σ ξL δ₀ r φ x i)
      = ∑' i : ι, indH L R x * S.indicator (Fi K L νZL D σ ξL δ₀ r φ x) i := by
        refine tsum_congr fun i => ?_
        rw [hw i, mul_assoc]
        congr 1
        by_cases hi : i ∈ S
        · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, one_mul]
        · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, zero_mul]
    _ = indH L R x * ∑' i : ι, S.indicator (Fi K L νZL D σ ξL δ₀ r φ x) i := tsum_mul_left
    _ = indH L R x * ∑' i : S, Fi K L νZL D σ ξL δ₀ r φ x (i : ι) := by rw [tsum_subtype S]
    _ = indH L R x * ∫ z in ΩL, ξf L ξL z * KB K L D σ I φ x z ∂νZL := by
        have hfold' : ∑' i : S, Fi K L νZL D σ ξL δ₀ r φ x (i : ι) =
            ∫ z in ΩL, ξf L ξL z * KB K L D σ I φ x z ∂νZL := hfold.symm
        rw [hfold']

end Main

end R4WeightRegroup

end

section

open MeasureTheory NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ x ∈ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂,
        IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL ∧
        (∑' i : ι,
          (Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) +
            Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ
                (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))
            ∂νZL) =
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL :=
  R4WeightRegroup.main K L νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr
    φ hφc hφs

end

end S_AutomorphicForm_exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit (solution)
