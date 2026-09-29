-- Prove2me | Definitions.Def_QuaternionAlgebra_EichlerOrder
-- name    : QuaternionAlgebra_EichlerOrder
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/69fee893-b43a-5555-ac4e-a01f5b0779c5
-- title:
--   Maximal and Eichler orders in a rational quaternion algebra
-- statement:
--   Throughout, $a,b\in\mathbb{Q}$ and $\Lambda$ ranges over $\mathbb{Z}$-submodules of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$; the project notion `IsOrder` requires $1\in\Lambda$, closure of $\Lambda$ under multiplication, $\mathbb{Q}\cdot\Lambda=\mathbb{H}[\mathbb{Q},a,b]$ (the $\mathbb{Q}$-span is $\top$) and finite generation of $\Lambda$ over $\mathbb{Z}$. A preliminary lemma records that any $y$ in the $\mathbb{Q}$-span of $\Lambda$ admits a nonzero natural number $n$ with $n\cdot y\in\Lambda$; from it follows `IsOrder.inf`, that the intersection $\Lambda_1\sqcap\Lambda_2$ of two orders is again an order, all four defining conditions being verified.
--
--   Three predicates are introduced. `IsMaximalOrder Λ` asserts that $\Lambda$ is an order and that every order $\Lambda'$ with $\Lambda\le\Lambda'$ satisfies $\Lambda'=\Lambda$, i.e. maximality for inclusion of $\mathbb{Z}$-submodules. `IsEichlerOrder Λ N`, for $N\in\mathbb{N}$, asserts the existence of maximal orders $\Lambda_1,\Lambda_2$ with $\Lambda=\Lambda_1\sqcap\Lambda_2$ and with relative index $N$ of the additive group of $\Lambda$ in that of $\Lambda_1$, the index being `AddSubgroup.relIndex`. Two consequences are recorded: such a $\Lambda$ is an order, and there exists a maximal order $\Lambda_1\ge\Lambda$ realising the index $N$. Finally `IsDefiniteRamifiedExactlyAt a b q`, for $q\in\mathbb{N}$, asserts $a<0$, $b<0$, and that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra — stated as: every nonzero element is a unit — if and only if the image of $q$ lies in the prime ideal of $v$. Two accessors extract $a<0$ and $b<0$.
--
--   **Relation to Mathlib.** Mathlib supplies the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, the height-one spectrum and the adic completions used here; the predicates for maximal orders, Eichler orders of given level and definite algebras ramified exactly at a given prime are the project's own, phrased on top of the project's `IsOrder`.
--
--   **Where it is used.** These predicates specify the arithmetic input for the quaternionic side of the argument: a definite quaternion algebra over $\mathbb{Q}$ ramified exactly at $q$ and $\infty$, together with an Eichler order of prescribed level, as needed to speak of quaternionic automorphic forms and their Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_QuaternionAlgebra_EichlerOrder.lean

import Mathlib
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace QuaternionAlgebra

variable {a b : ℚ}

theorem exists_natCast_smul_mem_of_mem_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {y : ℍ[ℚ, a, b]}
    (hy : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) :
    ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmu
    · rw [Nat.cast_mul, mul_smul]; exact Submodule.smul_mem _ _ hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have : (((c.den * n : ℕ) : ℤ)) • c • u = c.num • (((n : ℕ) : ℤ) • u) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ c.num,
        ← Int.cast_smul_eq_zsmul ℚ ((n : ℕ) : ℤ), smul_smul, smul_smul]
      congr 1
      push_cast
      rw [← Rat.mul_den_eq_num c]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ hnu

theorem IsOrder.inf {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : IsOrder Λ₁) (h₂ : IsOrder Λ₂) :
    IsOrder (Λ₁ ⊓ Λ₂) where
  one_mem := ⟨h₁.one_mem, h₂.one_mem⟩
  mul_mem := fun _ _ hx hy => ⟨h₁.mul_mem hx.1 hy.1, h₂.mul_mem hx.2 hy.2⟩
  spanTop := by
    refine top_unique ?_
    rw [← h₂.spanTop]
    refine Submodule.span_le.mpr fun y hy => ?_
    have hy' : y ∈ Submodule.span ℚ (Λ₁ : Set ℍ[ℚ, a, b]) := by rw [h₁.spanTop]; trivial
    obtain ⟨n, hn, hny⟩ := exists_natCast_smul_mem_of_mem_span hy'
    have hmem : ((n : ℕ) : ℤ) • y ∈ Λ₁ ⊓ Λ₂ := ⟨hny, Submodule.smul_mem _ _ hy⟩
    have : y = ((n : ℚ)⁻¹) • ((((n : ℕ) : ℤ) • y : ℍ[ℚ, a, b])) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  fg := by
    haveI : Module.Finite ℤ Λ₁ := Module.Finite.iff_fg.mpr h₁.fg
    haveI : Module.Finite ℤ ↥(Λ₁ ⊓ Λ₂) :=
      Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
    exact Module.Finite.iff_fg.mp inferInstance

def IsMaximalOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  IsOrder Λ ∧ ∀ Λ' : Submodule ℤ ℍ[ℚ, a, b], IsOrder Λ' → Λ ≤ Λ' → Λ' = Λ

theorem IsMaximalOrder.isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsMaximalOrder Λ) : IsOrder Λ :=
  h.1

def IsEichlerOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) : Prop :=
  ∃ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₁ ∧ IsMaximalOrder Λ₂ ∧ Λ = Λ₁ ⊓ Λ₂ ∧
    Λ.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N

theorem IsEichlerOrder.isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (h : IsEichlerOrder Λ N) :
    IsOrder Λ := by
  obtain ⟨Λ₁, Λ₂, h₁, h₂, rfl, -⟩ := h
  exact h₁.isOrder.inf h₂.isOrder

theorem IsEichlerOrder.exists_le_isMaximalOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (h : IsEichlerOrder Λ N) :
    ∃ Λ₁ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₁ ∧ Λ ≤ Λ₁ ∧
      Λ.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N := by
  obtain ⟨Λ₁, Λ₂, h₁, -, rfl, hN⟩ := h
  exact ⟨Λ₁, h₁, inf_le_left, hN⟩

variable (a b) in

def IsDefiniteRamifiedExactlyAt (q : ℕ) : Prop :=
  a < 0 ∧ b < 0 ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔ ((q : 𝓞 ℚ) ∈ v.asIdeal)

theorem IsDefiniteRamifiedExactlyAt.neg_left {q : ℕ} (h : IsDefiniteRamifiedExactlyAt a b q) : a < 0 :=
  h.1

theorem IsDefiniteRamifiedExactlyAt.neg_right {q : ℕ} (h : IsDefiniteRamifiedExactlyAt a b q) : b < 0 :=
  h.2.1

end QuaternionAlgebra


