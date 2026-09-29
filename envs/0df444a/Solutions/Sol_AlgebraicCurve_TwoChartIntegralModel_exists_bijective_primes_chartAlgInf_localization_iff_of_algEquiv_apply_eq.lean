-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/547bf5fc-ddc0-59de-aa5c-a04789ad0e73

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq

set_option autoImplicit false

open AlgebraicCurve

namespace CuspTransportAux

variable {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]

def L (B : Subalgebra A T) (y : Ideal ↥B) : Set T := {f | ∃ g h : ↥B, h ∉ y ∧ f * (h : T) = (g : T)}

def M (B : Subalgebra A T) (y : Ideal ↥B) : Set T := {f | ∃ g h : ↥B, h ∉ y ∧ g ∈ y ∧ f * (h : T) = (g : T)}

section Basic

variable (B : Subalgebra A T) (y : Ideal ↥B) [hy : y.IsPrime]

theorem one_notMem : (1 : ↥B) ∉ y := (Ideal.ne_top_iff_one y).mp hy.ne_top

theorem coe_mem_L (b : ↥B) : (b : T) ∈ L B y := ⟨b, 1, one_notMem B y, by simp⟩

theorem M_subset_L {f : T} (hf : f ∈ M B y) : f ∈ L B y := by
  obtain ⟨g, h, hh, -, e⟩ := hf; exact ⟨g, h, hh, e⟩

theorem zero_mem_M : (0 : T) ∈ M B y := ⟨0, 1, one_notMem B y, y.zero_mem, by simp⟩

theorem coe_mem_M_iff (b : ↥B) : (b : T) ∈ M B y ↔ b ∈ y := by
  constructor
  · rintro ⟨g, h, hh, hg, e⟩
    have : b * h = g := Subtype.ext (by simpa using e)
    have hbh : b * h ∈ y := this ▸ hg
    exact (hy.mem_or_mem hbh).resolve_right hh
  · intro hb; exact ⟨b, 1, one_notMem B y, hb, by simp⟩

theorem ne_zero_of_notMem {h : ↥B} (hh : h ∉ y) : (h : T) ≠ 0 := by
  intro h0; apply hh; rw [show h = 0 from Subtype.ext h0]; exact y.zero_mem

theorem mul_mem_L {f₁ f₂ : T} (h₁ : f₁ ∈ L B y) (h₂ : f₂ ∈ L B y) : f₁ * f₂ ∈ L B y := by
  obtain ⟨g₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨g₂, k₂, hk₂, e₂⟩ := h₂
  refine ⟨g₁ * g₂, k₁ * k₂, fun hk => (hy.mem_or_mem hk).elim hk₁ hk₂, ?_⟩
  simp only [Subalgebra.coe_mul]
  calc f₁ * f₂ * ((k₁ : T) * k₂) = (f₁ * k₁) * (f₂ * k₂) := by ring
    _ = g₁ * g₂ := by rw [e₁, e₂]

theorem add_mem_L {f₁ f₂ : T} (h₁ : f₁ ∈ L B y) (h₂ : f₂ ∈ L B y) : f₁ + f₂ ∈ L B y := by
  obtain ⟨g₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨g₂, k₂, hk₂, e₂⟩ := h₂
  refine ⟨g₁ * k₂ + g₂ * k₁, k₁ * k₂, fun hk => (hy.mem_or_mem hk).elim hk₁ hk₂, ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
  calc (f₁ + f₂) * ((k₁ : T) * k₂) = (f₁ * k₁) * k₂ + (f₂ * k₂) * k₁ := by ring
    _ = g₁ * k₂ + g₂ * k₁ := by rw [e₁, e₂]

theorem neg_mem_L {f : T} (h : f ∈ L B y) : -f ∈ L B y := by
  obtain ⟨g, k, hk, e⟩ := h
  exact ⟨-g, k, hk, by simp [← e]⟩

theorem mul_mem_M {f₁ f₂ : T} (h₁ : f₁ ∈ L B y) (h₂ : f₂ ∈ M B y) : f₁ * f₂ ∈ M B y := by
  obtain ⟨g₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨g₂, k₂, hk₂, hg₂, e₂⟩ := h₂
  refine ⟨g₁ * g₂, k₁ * k₂, fun hk => (hy.mem_or_mem hk).elim hk₁ hk₂, y.mul_mem_left _ hg₂, ?_⟩
  simp only [Subalgebra.coe_mul]
  calc f₁ * f₂ * ((k₁ : T) * k₂) = (f₁ * k₁) * (f₂ * k₂) := by ring
    _ = g₁ * g₂ := by rw [e₁, e₂]

theorem add_mem_M {f₁ f₂ : T} (h₁ : f₁ ∈ M B y) (h₂ : f₂ ∈ M B y) : f₁ + f₂ ∈ M B y := by
  obtain ⟨g₁, k₁, hk₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, k₂, hk₂, hg₂, e₂⟩ := h₂
  refine ⟨g₁ * k₂ + g₂ * k₁, k₁ * k₂, fun hk => (hy.mem_or_mem hk).elim hk₁ hk₂,
    y.add_mem (y.mul_mem_right _ hg₁) (y.mul_mem_right _ hg₂), ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
  calc (f₁ + f₂) * ((k₁ : T) * k₂) = (f₁ * k₁) * k₂ + (f₂ * k₂) * k₁ := by ring
    _ = g₁ * k₂ + g₂ * k₁ := by rw [e₁, e₂]

theorem neg_mem_M {f : T} (h : f ∈ M B y) : -f ∈ M B y := by
  obtain ⟨g, k, hk, hg, e⟩ := h
  exact ⟨-g, k, hk, y.neg_mem_iff.mpr hg, by simp [← e]⟩

theorem sum_mem_M {ι : Type} (s : Finset ι) (f : ι → T) (hf : ∀ i ∈ s, f i ∈ M B y) :
    ∑ i ∈ s, f i ∈ M B y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_M B y
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add_mem_M B y (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem pow_mem_M {f : T} (hf : f ∈ M B y) {n : ℕ} (hn : n ≠ 0) : f ^ n ∈ M B y := by
  have key : ∀ m : ℕ, f ^ (m + 1) ∈ M B y := by
    intro m
    induction m with
    | zero => simpa using hf
    | succ m ih => rw [pow_succ]; exact mul_mem_M B y (M_subset_L B y ih) hf
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact key m

theorem inv_notMem_L_of_mem_M {f : T} (hf : f ∈ M B y) (hf0 : f ≠ 0) : f⁻¹ ∉ L B y := by
  rintro ⟨g₂, k₂, hk₂, e₂⟩
  obtain ⟨g₁, k₁, hk₁, hg₁, e₁⟩ := hf
  have : (k₁ : T) * k₂ = g₁ * g₂ := by
    calc (k₁ : T) * k₂ = (f * k₁) * (f⁻¹ * k₂) := by field_simp
      _ = g₁ * g₂ := by rw [e₁, e₂]
  have hB : k₁ * k₂ = g₁ * g₂ := Subtype.ext (by simpa using this)
  have : k₁ * k₂ ∈ y := hB ▸ y.mul_mem_right _ hg₁
  exact (hy.mem_or_mem this).elim hk₁ hk₂

theorem inv_mem_L_of_notMem_M {f : T} (hf : f ∈ L B y) (hfM : f ∉ M B y) : f⁻¹ ∈ L B y := by
  obtain ⟨g, k, hk, e⟩ := hf
  have hg : g ∉ y := fun hg => hfM ⟨g, k, hk, hg, e⟩
  refine ⟨k, g, hg, ?_⟩
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hg
    rw [show g = 0 from Subtype.ext (by simpa using e.symm)]; exact y.zero_mem
  rw [← e]; field_simp

theorem mem_M_iff {f : T} : f ∈ M B y ↔ f ∈ L B y ∧ (f = 0 ∨ f⁻¹ ∉ L B y) := by
  constructor
  · intro hf
    refine ⟨M_subset_L B y hf, ?_⟩
    by_cases h0 : f = 0
    · exact Or.inl h0
    · exact Or.inr (inv_notMem_L_of_mem_M B y hf h0)
  · rintro ⟨hL, h⟩
    rcases h with h0 | hinv
    · rw [h0]; exact zero_mem_M B y
    · by_contra hM
      exact hinv (inv_mem_L_of_notMem_M B y hL hM)

theorem one_notMem_M : (1 : T) ∉ M B y := by
  intro h
  have := (coe_mem_M_iff B y 1).mp (by simpa using h)
  exact one_notMem B y this

end Basic

section Order

variable (B : Subalgebra A T)

theorem L_subset_L_of_le {y₁ y₂ : Ideal ↥B} (h : y₁ ≤ y₂) : L B y₂ ⊆ L B y₁ := by
  rintro f ⟨g, k, hk, e⟩; exact ⟨g, k, fun hk' => hk (h hk'), e⟩

theorem le_of_L_subset_L {y₁ y₂ : Ideal ↥B} [y₁.IsPrime] [y₂.IsPrime] (h : L B y₂ ⊆ L B y₁) : y₁ ≤ y₂ := by
  intro b hb
  by_contra hb₂
  have hinv : (b : T)⁻¹ ∈ L B y₂ := ⟨1, b, hb₂, by simp [ne_zero_of_notMem B y₂ hb₂]⟩
  exact inv_notMem_L_of_mem_M B y₁ ((coe_mem_M_iff B y₁ b).mpr hb) (ne_zero_of_notMem B y₂ hb₂) (h hinv)

theorem le_iff_L_subset_L {y₁ y₂ : Ideal ↥B} [y₁.IsPrime] [y₂.IsPrime] : y₁ ≤ y₂ ↔ L B y₂ ⊆ L B y₁ :=
  ⟨L_subset_L_of_le B, le_of_L_subset_L B⟩

theorem eq_of_L_eq {y₁ y₂ : Ideal ↥B} [y₁.IsPrime] [y₂.IsPrime] (h : L B y₁ = L B y₂) : y₁ = y₂ :=
  le_antisymm (le_of_L_subset_L B h.symm.subset) (le_of_L_subset_L B h.subset)

end Order

end CuspTransportAux

namespace CuspTransportAux

variable {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]

section Contract

variable (B B' : Subalgebra A T) (y : Ideal ↥B) [hy : y.IsPrime] (hB' : ∀ b' : ↥B', (b' : T) ∈ L B y)

def contract : Ideal ↥B' where
  carrier := {b' | (b' : T) ∈ M B y}
  zero_mem' := by simpa using zero_mem_M B y
  add_mem' := fun {a b} ha hb => by simpa using add_mem_M B y ha hb
  smul_mem' := fun c {x} hx => by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subalgebra.coe_mul] at hx ⊢
    exact mul_mem_M B y (hB' c) hx

theorem mem_contract_iff (b' : ↥B') : b' ∈ contract B B' y hB' ↔ (b' : T) ∈ M B y := Iff.rfl

scoped instance contract_isPrime : (contract B B' y hB').IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_contract_iff]
    simpa using one_notMem_M B y
  · intro a b hab
    rw [mem_contract_iff, Subalgebra.coe_mul] at hab
    by_cases ha : (a : T) ∈ M B y
    · exact Or.inl ha
    · right
      have hainv := inv_mem_L_of_notMem_M B y (hB' a) ha
      have ha0 : (a : T) ≠ 0 := fun h0 => ha (by rw [h0]; exact zero_mem_M B y)
      have : (b : T) = (a : T)⁻¹ * ((a : T) * b) := by field_simp
      show (b : T) ∈ M B y
      rw [this]; exact mul_mem_M B y hainv hab

theorem L_contract_subset : L B' (contract B B' y hB') ⊆ L B y := by
  rintro f ⟨g, k, hk, e⟩
  rw [mem_contract_iff] at hk
  have hk0 : (k : T) ≠ 0 := fun h0 => hk (by rw [h0]; exact zero_mem_M B y)
  have : f = (g : T) * (k : T)⁻¹ := by rw [← e]; field_simp
  rw [this]
  exact mul_mem_L B y (hB' g) (inv_mem_L_of_notMem_M B y (hB' k) hk)

theorem M_contract_subset : M B' (contract B B' y hB') ⊆ M B y := by
  rintro f ⟨g, k, hk, hg, e⟩
  rw [mem_contract_iff] at hk hg
  have hk0 : (k : T) ≠ 0 := fun h0 => hk (by rw [h0]; exact zero_mem_M B y)
  have : f = (k : T)⁻¹ * (g : T) := by rw [← e]; field_simp
  rw [this]
  exact mul_mem_M B y (inv_mem_L_of_notMem_M B y (hB' k) hk) hg

theorem L_eq_L_contract (hB : ∀ b : ↥B, (b : T) ∈ L B' (contract B B' y hB')) :
    L B y = L B' (contract B B' y hB') := by
  refine Set.Subset.antisymm ?_ (L_contract_subset B B' y hB')
  rintro f ⟨g, k, hk, e⟩
  have hkM : (k : T) ∉ M B' (contract B B' y hB') := fun hkM =>
    hk ((coe_mem_M_iff B y k).mp (M_contract_subset B B' y hB' hkM))
  have hk0 : (k : T) ≠ 0 := ne_zero_of_notMem B y hk
  have : f = (g : T) * (k : T)⁻¹ := by rw [← e]; field_simp
  rw [this]
  exact mul_mem_L B' _ (hB g) (inv_mem_L_of_notMem_M B' _ (hB k) hkM)

end Contract

section MfromL

variable (B₁ B₂ : Subalgebra A T) (y₁ : Ideal ↥B₁) (y₂ : Ideal ↥B₂) [y₁.IsPrime] [y₂.IsPrime]

theorem M_eq_of_L_eq (h : L B₁ y₁ = L B₂ y₂) : M B₁ y₁ = M B₂ y₂ := by
  ext f
  rw [mem_M_iff B₁ y₁, mem_M_iff B₂ y₂, h]

end MfromL

section Transport

variable (B : Subalgebra A T) (σ : T ≃ₐ[A] T) (hσ' : ∀ b : ↥B, σ.symm b ∈ B)

def resInv : ↥B →+* ↥B where
  toFun b := ⟨σ.symm b, hσ' b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

def transport (𝔶 : Ideal ↥B) : Ideal ↥B := 𝔶.comap (resInv B σ hσ')

theorem mem_transport_iff (𝔶 : Ideal ↥B) (b : ↥B) :
    b ∈ transport B σ hσ' 𝔶 ↔ (⟨σ.symm b, hσ' b⟩ : ↥B) ∈ 𝔶 := Iff.rfl

scoped instance transport_isPrime (𝔶 : Ideal ↥B) [𝔶.IsPrime] : (transport B σ hσ' 𝔶).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_L_transport_iff (hσ : ∀ b : ↥B, σ b ∈ B) (𝔶 : Ideal ↥B) (f : T) :
    f ∈ L B (transport B σ hσ' 𝔶) ↔ σ.symm f ∈ L B 𝔶 := by
  constructor
  · rintro ⟨g, k, hk, e⟩
    refine ⟨⟨σ.symm g, hσ' g⟩, ⟨σ.symm k, hσ' k⟩, hk, ?_⟩
    show σ.symm f * σ.symm (k : T) = σ.symm (g : T)
    rw [← map_mul, e]
  · rintro ⟨g, k, hk, e⟩
    refine ⟨⟨σ g, hσ g⟩, ⟨σ k, hσ k⟩, ?_, ?_⟩
    · rw [mem_transport_iff]
      have : (⟨σ.symm (σ (k : T)), hσ' ⟨σ k, hσ k⟩⟩ : ↥B) = k := Subtype.ext (by simp)
      rw [this]; exact hk
    · show f * σ (k : T) = σ (g : T)
      rw [← e, map_mul, AlgEquiv.apply_symm_apply]

theorem mem_M_transport_iff (hσ : ∀ b : ↥B, σ b ∈ B) (𝔶 : Ideal ↥B) (f : T) :
    f ∈ M B (transport B σ hσ' 𝔶) ↔ σ.symm f ∈ M B 𝔶 := by
  constructor
  · rintro ⟨g, k, hk, hg, e⟩
    refine ⟨⟨σ.symm g, hσ' g⟩, ⟨σ.symm k, hσ' k⟩, hk, hg, ?_⟩
    show σ.symm f * σ.symm (k : T) = σ.symm (g : T)
    rw [← map_mul, e]
  · rintro ⟨g, k, hk, hg, e⟩
    refine ⟨⟨σ g, hσ g⟩, ⟨σ k, hσ k⟩, ?_, ?_, ?_⟩
    · rw [mem_transport_iff]
      have : (⟨σ.symm (σ (k : T)), hσ' ⟨σ k, hσ k⟩⟩ : ↥B) = k := Subtype.ext (by simp)
      rw [this]; exact hk
    · rw [mem_transport_iff]
      have : (⟨σ.symm (σ (g : T)), hσ' ⟨σ g, hσ g⟩⟩ : ↥B) = g := Subtype.ext (by simp)
      rw [this]; exact hg
    · show f * σ (k : T) = σ (g : T)
      rw [← e, map_mul, AlgEquiv.apply_symm_apply]

end Transport

end CuspTransportAux
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq.CuspTransportAux"

namespace CuspTransportAux

variable {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]

section Charts

open AlgebraicCurve.TwoChartIntegralModel

theorem coe_mem_L_of_swap (j j' : T) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (h3 : ∀ c, c ∈ chartAlgInf A T j' → ∃ s, s ∈ chartAlgInf A T j ∧
        (∃ a, a ∈ chartAlgInf A T j ∧ s = 1 + j⁻¹ * a) ∧ s * c ∈ chartAlgInf A T j)
    (y : Ideal ↥(chartAlgInf A T j)) [hy : y.IsPrime] (hjy : jInvChartInf A T j ∈ y) :
    ∀ b' : ↥(chartAlgInf A T j'), (b' : T) ∈ L (chartAlgInf A T j) y := by
  intro b'
  obtain ⟨s, hs, ⟨a, ha, hsa⟩, hsc⟩ := h3 b' b'.2
  refine ⟨⟨s * b', hsc⟩, ⟨s, hs⟩, ?_, by simp [mul_comm]⟩
  intro hsy
  apply one_notMem _ y
  have h1 : (⟨s, hs⟩ : ↥(chartAlgInf A T j)) - jInvChartInf A T j * ⟨a, ha⟩ = 1 :=
    Subtype.ext (by simp [hsa, coe_jInvChartInf])
  rw [← h1]
  exact y.sub_mem hsy (y.mul_mem_right _ hjy)

theorem inv_mem_M_of_isIntegral (j j' : T) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hint' : IsIntegral ↥(Algebra.adjoin A ({j'} : Set T)) j)
    (y : Ideal ↥(chartAlgInf A T j)) [hy : y.IsPrime] (hjy : jInvChartInf A T j ∈ y)
    (hL : (j'⁻¹ : T) ∈ L (chartAlgInf A T j) y) :
    (j'⁻¹ : T) ∈ M (chartAlgInf A T j) y := by
  classical
  rw [mem_M_iff]
  refine ⟨hL, Or.inr ?_⟩
  rw [inv_inv]
  intro hj'L

  have hadj : ∀ z ∈ Algebra.adjoin A ({j'} : Set T), z ∈ L (chartAlgInf A T j) y := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hj'L
    | algebraMap a =>
        have : algebraMap A T a = ((algebraMap A ↥(chartAlgInf A T j) a : ↥(chartAlgInf A T j)) : T) := rfl
        rw [this]; exact coe_mem_L _ y _
    | add x z _ _ hx hz => exact add_mem_L _ y hx hz
    | mul x z _ _ hx hz => exact mul_mem_L _ y hx hz
  have hjM : (j⁻¹ : T) ∈ M (chartAlgInf A T j) y := by
    have := (coe_mem_M_iff _ y (jInvChartInf A T j)).mpr hjy
    simpa [coe_jInvChartInf] using this

  obtain ⟨p, hpm, hp0⟩ := hint'
  set N := p.natDegree with hN
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hp0
  have hj0 : (j : T) ≠ 0 := Fact.out
  have hpow : ∀ i ∈ Finset.range N, (j⁻¹) ^ N * j ^ i = (j⁻¹) ^ (N - i) := by
    intro i hi
    have hi' : i ≤ N := (Finset.mem_range.mp hi).le
    conv_lhs => rw [← Nat.sub_add_cancel hi', pow_add]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hj0, one_pow, mul_one]
  have key : (1 : T) = -∑ i ∈ Finset.range N,
      algebraMap ↥(Algebra.adjoin A ({j'} : Set T)) T (p.coeff i) * (j⁻¹) ^ (N - i) := by
    have h := congrArg (fun z => (j⁻¹) ^ N * z) hp0
    simp only [mul_zero, mul_add, Finset.mul_sum] at h
    rw [← mul_pow, inv_mul_cancel₀ hj0, one_pow] at h
    rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hpow i hi]; ring
  apply one_notMem_M _ y
  rw [key]
  refine neg_mem_M _ y (sum_mem_M _ y _ _ fun i hi => ?_)
  refine mul_mem_M _ y (hadj _ (p.coeff i).2) (pow_mem_M _ y hjM ?_)
  have := Finset.mem_range.mp hi
  omega

theorem isIntegral_adjoin_map {K K' : Type} [Field K] [Field K'] [Algebra A K] [Algebra A K']
    (τ : K →ₐ[A] K') (t b : K) (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K')) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K') :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem map_mem_chartAlgInf (j' : T) [Fact (j' ≠ 0)] (τ : T ≃ₐ[A] T) (hτ : τ j' = j')
    (b : ↥(chartAlgInf A T j')) : τ (b : T) ∈ chartAlgInf A T j' := by
  have h := isIntegral_adjoin_map (τ : T →ₐ[A] T) j'⁻¹ b b.2
  rw [AlgEquiv.coe_algHom, map_inv₀, hτ] at h
  exact h

end Charts
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq.CuspTransportAux"

end CuspTransportAux
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq.CuspTransportAux"

open CuspTransportAux AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 6400000 in
theorem solution
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]
    (j j' : T) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hint : IsIntegral ↥(Algebra.adjoin A ({j} : Set T)) j') (hint' : IsIntegral ↥(Algebra.adjoin A ({j'} : Set T)) j)
    (h3 : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf A T j' →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf A T j ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf A T j ∧ s = 1 + j⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf A T j)
    (h4 : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf A T j →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf A T j' ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf A T j' ∧ s = 1 + j'⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf A T j')
    (σ : T ≃ₐ[A] T) (hσ : σ j' = j') :
    ∃ Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) //
              y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y} →
            {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) //
              y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y},
      Function.Bijective Φ ∧
      (∀ y₁ y₂ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) //
              y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y},
        y₁.1 ≤ y₂.1 ↔ (Φ y₁).1 ≤ (Φ y₂).1) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ y.1 ∧ σ.symm f * (h : T) = (g : T))) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ (Φ y).1 ∧ g ∈ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A T j), h ∉ y.1 ∧ g ∈ y.1 ∧ σ.symm f * (h : T) = (g : T))) := by
  classical

  have S1 : ∀ (y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j)) [y.IsPrime], jInvChartInf A T j ∈ y → ∀ b' : ↥(TwoChartIntegralModel.chartAlgInf A T j'), (b' : T) ∈ L (TwoChartIntegralModel.chartAlgInf A T j) y :=
    fun y _ hjy => coe_mem_L_of_swap j j' h3 y hjy
  have S1' : ∀ (𝔶 : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j')) [𝔶.IsPrime], jInvChartInf A T j' ∈ 𝔶 → ∀ b : ↥(TwoChartIntegralModel.chartAlgInf A T j), (b : T) ∈ L (TwoChartIntegralModel.chartAlgInf A T j') 𝔶 :=
    fun 𝔶 _ hj𝔶 => coe_mem_L_of_swap j' j h4 𝔶 hj𝔶
  have S2 : ∀ (y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j)) [y.IsPrime], jInvChartInf A T j ∈ y → ((jInvChartInf A T j' : ↥(TwoChartIntegralModel.chartAlgInf A T j')) : T) ∈ M (TwoChartIntegralModel.chartAlgInf A T j) y :=
    fun y _ hjy => inv_mem_M_of_isIntegral j j' hint' y hjy (S1 y hjy (jInvChartInf A T j'))
  have S2' : ∀ (𝔶 : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j')) [𝔶.IsPrime], jInvChartInf A T j' ∈ 𝔶 → ((jInvChartInf A T j : ↥(TwoChartIntegralModel.chartAlgInf A T j)) : T) ∈ M (TwoChartIntegralModel.chartAlgInf A T j') 𝔶 :=
    fun 𝔶 _ hj𝔶 => inv_mem_M_of_isIntegral j' j hint 𝔶 hj𝔶 (S1' 𝔶 hj𝔶 (jInvChartInf A T j))

  have construct : ∀ (τ : T ≃ₐ[A] T), τ j' = j' → ∀ y : {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) // y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y}, ∃ y' : {y : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) // y.IsPrime ∧ TwoChartIntegralModel.jInvChartInf A T j ∈ y}, ∀ f : T, f ∈ L (TwoChartIntegralModel.chartAlgInf A T j) y'.1 ↔ τ.symm f ∈ L (TwoChartIntegralModel.chartAlgInf A T j) y.1 := by
    intro τ hτ y
    have hτ' : τ.symm j' = j' := by rw [← hτ, AlgEquiv.symm_apply_apply]; exact hτ.symm ▸ rfl
    have hτB : ∀ b' : ↥(TwoChartIntegralModel.chartAlgInf A T j'), τ (b' : T) ∈ (TwoChartIntegralModel.chartAlgInf A T j') := map_mem_chartAlgInf j' τ hτ
    have hτB' : ∀ b' : ↥(TwoChartIntegralModel.chartAlgInf A T j'), τ.symm (b' : T) ∈ (TwoChartIntegralModel.chartAlgInf A T j') := map_mem_chartAlgInf j' τ.symm hτ'
    haveI := y.2.1
    let 𝔶 : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j') := contract (TwoChartIntegralModel.chartAlgInf A T j) (TwoChartIntegralModel.chartAlgInf A T j') y.1 (S1 y.1 y.2.2)
    have hj𝔶 : jInvChartInf A T j' ∈ 𝔶 := (mem_contract_iff _ _ _ _ _).mpr (S2 y.1 y.2.2)
    have hL1 : L (TwoChartIntegralModel.chartAlgInf A T j) y.1 = L (TwoChartIntegralModel.chartAlgInf A T j') 𝔶 := L_eq_L_contract _ _ _ _ (S1' 𝔶 hj𝔶)
    let 𝔶τ : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j') := transport (TwoChartIntegralModel.chartAlgInf A T j') τ hτB' 𝔶
    have hj𝔶τ : jInvChartInf A T j' ∈ 𝔶τ := by
      rw [mem_transport_iff]
      have : (⟨τ.symm ((jInvChartInf A T j' : ↥(TwoChartIntegralModel.chartAlgInf A T j')) : T), hτB' _⟩ : ↥(TwoChartIntegralModel.chartAlgInf A T j')) = jInvChartInf A T j' :=
        Subtype.ext (by simp [coe_jInvChartInf, hτ'])
      rw [this]; exact hj𝔶
    have hL2 : ∀ f : T, f ∈ L (TwoChartIntegralModel.chartAlgInf A T j') 𝔶τ ↔ τ.symm f ∈ L (TwoChartIntegralModel.chartAlgInf A T j') 𝔶 := mem_L_transport_iff (TwoChartIntegralModel.chartAlgInf A T j') τ hτB' hτB 𝔶
    let y' : Ideal ↥(TwoChartIntegralModel.chartAlgInf A T j) := contract (TwoChartIntegralModel.chartAlgInf A T j') (TwoChartIntegralModel.chartAlgInf A T j) 𝔶τ (S1' 𝔶τ hj𝔶τ)
    have hjy' : jInvChartInf A T j ∈ y' := (mem_contract_iff _ _ _ _ _).mpr (S2' 𝔶τ hj𝔶τ)
    have hL3 : L (TwoChartIntegralModel.chartAlgInf A T j') 𝔶τ = L (TwoChartIntegralModel.chartAlgInf A T j) y' := L_eq_L_contract _ _ _ _ (S1 y' hjy')
    refine ⟨⟨y', inferInstance, hjy'⟩, fun f => ?_⟩
    show f ∈ L (TwoChartIntegralModel.chartAlgInf A T j) y' ↔ τ.symm f ∈ L (TwoChartIntegralModel.chartAlgInf A T j) y.1
    rw [← hL3, hL2, hL1]

  choose Φ hΦ using construct σ hσ
  have hσ' : σ.symm j' = j' := by
    conv_lhs => rw [← hσ]
    exact σ.symm_apply_apply j'
  choose Ψ hΨ using construct σ.symm hσ'
  have hΨΦ : ∀ y, Ψ (Φ y) = y := by
    intro y
    haveI := y.2.1; haveI := (Φ y).2.1; haveI := (Ψ (Φ y)).2.1
    apply Subtype.ext
    apply eq_of_L_eq (TwoChartIntegralModel.chartAlgInf A T j)
    ext f
    rw [hΨ, hΦ]
    simp
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y
    haveI := y.2.1; haveI := (Ψ y).2.1; haveI := (Φ (Ψ y)).2.1
    apply Subtype.ext
    apply eq_of_L_eq (TwoChartIntegralModel.chartAlgInf A T j)
    ext f
    rw [hΦ, hΨ]
    simp
  refine ⟨Φ, Function.bijective_iff_has_inverse.mpr ⟨Ψ, hΨΦ, hΦΨ⟩, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂
    haveI := y₁.2.1; haveI := y₂.2.1; haveI := (Φ y₁).2.1; haveI := (Φ y₂).2.1
    rw [le_iff_L_subset_L (TwoChartIntegralModel.chartAlgInf A T j), le_iff_L_subset_L (TwoChartIntegralModel.chartAlgInf A T j) (y₁ := (Φ y₁).1)]
    constructor
    · intro h f hf
      rw [hΦ] at hf ⊢
      exact h hf
    · intro h f hf
      have := h (show σ f ∈ L (TwoChartIntegralModel.chartAlgInf A T j) (Φ y₂).1 from by rw [hΦ]; simpa using hf)
      rw [hΦ] at this
      simpa using this
  · intro y f
    exact hΦ y f
  · intro y f
    haveI := y.2.1; haveI := (Φ y).2.1
    show f ∈ M (TwoChartIntegralModel.chartAlgInf A T j) (Φ y).1 ↔ σ.symm f ∈ M (TwoChartIntegralModel.chartAlgInf A T j) y.1
    rw [mem_M_iff, mem_M_iff, hΦ, ← map_inv₀, hΦ]
    simp

end S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq (solution)
