-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/df8d012d-4d3e-5de3-aac2-6232651b0e85

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff

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
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff.CuspTransportAux"

open CuspTransportAux AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 6400000 in
theorem solution
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T] (j : T)
    (σ : T ≃ₐ[A] T)
    (hσ : ∀ b : T, b ∈ TwoChartIntegralModel.chartAlgFin A T j ↔ σ b ∈ TwoChartIntegralModel.chartAlgFin A T j) :
    ∃ Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} →
            {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
      Function.Bijective Φ ∧
      (∀ y₁ y₂ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
        y₁.1 ≤ y₂.1 ↔ (Φ y₁).1 ≤ (Φ y₂).1) ∧
      (∀ (y : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime})
        (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)),
        b ∈ (Φ y).1 ↔ (⟨σ.symm b, (hσ (σ.symm b)).2 (by rw [AlgEquiv.apply_symm_apply]; exact b.2)⟩ :
          ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ σ.symm f * (h : T) = (g : T))) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ g ∈ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ g ∈ y.1 ∧ σ.symm f * (h : T) = (g : T))) := by
  classical
  have hσB : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A T j), σ (b : T) ∈ (TwoChartIntegralModel.chartAlgFin A T j) := fun b => (hσ b).mp b.2
  have hσB' : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A T j), σ.symm (b : T) ∈ (TwoChartIntegralModel.chartAlgFin A T j) := fun b =>
    (hσ (σ.symm b)).mpr (by rw [AlgEquiv.apply_symm_apply]; exact b.2)
  have hσsB' : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A T j), σ.symm.symm (b : T) ∈ (TwoChartIntegralModel.chartAlgFin A T j) := fun b => by simpa using hσB b
  let Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} → {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} := fun y =>
    ⟨transport (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' y.1, by haveI := y.2; exact transport_isPrime (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' y.1⟩
  let Ψ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} → {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} := fun y =>
    ⟨transport (TwoChartIntegralModel.chartAlgFin A T j) σ.symm hσsB' y.1, by haveI := y.2; exact transport_isPrime (TwoChartIntegralModel.chartAlgFin A T j) σ.symm hσsB' y.1⟩
  have hΦ : ∀ y (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)), b ∈ (Φ y).1 ↔ (⟨σ.symm b, hσB' b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1 := fun y b => Iff.rfl
  have hΨ : ∀ y (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)), b ∈ (Ψ y).1 ↔ (⟨σ b, by simpa using hσsB' b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1 := by
    intro y b
    show (⟨σ.symm.symm b, hσsB' b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1 ↔ _
    simp only [AlgEquiv.symm_symm]
  have hΨΦ : ∀ y, Ψ (Φ y) = y := by
    intro y; apply Subtype.ext; ext b
    rw [hΨ, hΦ]
    simp
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y; apply Subtype.ext; ext b
    rw [hΦ, hΨ]
    simp
  refine ⟨Φ, Function.bijective_iff_has_inverse.mpr ⟨Ψ, hΨΦ, hΦΨ⟩, ?_, ?_, ?_, ?_⟩
  · intro y₁ y₂
    constructor
    · intro h b hb
      rw [hΦ] at hb ⊢
      exact h hb
    · intro h b hb
      have e : (⟨σ.symm ((⟨σ b, hσB b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) : T), hσB' ⟨σ b, hσB b⟩⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) = b := Subtype.ext (by simp)
      have hmem : (⟨σ b, hσB b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ (Φ y₁).1 := by rw [hΦ, e]; exact hb
      have h2 := h hmem
      rw [hΦ, e] at h2
      exact h2
  · intro y b
    exact hΦ y b
  · intro y f
    exact mem_L_transport_iff (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' hσB y.1 f
  · intro y f
    exact mem_M_transport_iff (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' hσB y.1 f

end S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff (solution)
