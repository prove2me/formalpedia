-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
-- name    : InfoLossLAR_Native_AFT_FiniteProbability
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:18:59.221415+00:00
-- url     : https://prove2.me/theorems/dc7c105e-8fd3-45fa-adb1-478a0303b381
-- title:
--   Finite probability laws and their elementary channels
-- statement:
--   For a finite set $X$, a probability law is a real weight function $p$ satisfying $$p(x)\ge 0,\qquad\sum_{x\in X}p(x)=1.$$ The accompanying operations are deterministic pushforward, independent products, mixtures of finite probability kernels, and the uniform law. These provide the finite probability model for the affine sampler.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/FiniteProbability.lean; migrated source SHA256 56623ca6312cf835a70ffd80a11dc49e996edec1eebf1d560e191b6a78367eba; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Mathlib


/-!
# Finite probability for affine fiber transports

Finite probability distributions are real nonnegative weights summing to one.
The preservation theorems below formalize the conditioning argument of V7,
Lemma `lem:t-aft-properties`: a random permutation of an independent uniform
input is uniform, and remains independent of any function of the randomness.
-/

namespace AFT

/-- A probability distribution on a finite type, with real-valued weights. -/
structure FiniteDist (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  sum_one : ∑ a, weight a = 1

namespace FiniteDist

open scoped Classical

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[ext] theorem ext {p q : FiniteDist α} (h : ∀ a, p.weight a = q.weight a) : p = q := by
  cases p
  cases q
  congr
  exact funext h

/-- Push forward a finite distribution along a deterministic function. -/
noncomputable def map (p : FiniteDist α) (f : α → β) : FiniteDist β := by
  classical
  exact {
    weight := fun b => ∑ a, if f a = b then p.weight a else 0
    nonneg := fun b => Finset.sum_nonneg fun a _ => by split_ifs <;> simp [p.nonneg]
    sum_one := by
      rw [Finset.sum_comm]
      simp [p.sum_one]
  }

theorem map_weight (p : FiniteDist α) (f : α → β) (b : β) :
    (p.map f).weight b = ∑ a, if f a = b then p.weight a else 0 := rfl

/-- Deterministic pushforwards compose exactly. -/
@[simp] theorem map_map (p : FiniteDist α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (fun a => g (f a)) := by
  classical
  ext c
  simp only [map_weight]
  trans ∑ b, ∑ a, if f a = b then (if g b = c then p.weight a else 0) else 0
  · apply Finset.sum_congr rfl
    intro b _
    by_cases h : g b = c <;> simp [h]
  · rw [Finset.sum_comm]
    simp

/-- Independently draw the kernel's fresh randomness after drawing `p`. -/
noncomputable def mix (p : FiniteDist α) (k : α → FiniteDist β) : FiniteDist β where
  weight b := ∑ a, p.weight a * (k a).weight b
  nonneg b := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) ((k a).nonneg b)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_one, mul_one]
    exact p.sum_one

@[simp] theorem mix_weight (p : FiniteDist α) (k : α → FiniteDist β) (b : β) :
    (p.mix k).weight b = ∑ a, p.weight a * (k a).weight b := rfl

/-- Product law for independent samples. -/
noncomputable def prod (p : FiniteDist α) (q : FiniteDist β) : FiniteDist (α × β) where
  weight ab := p.weight ab.1 * q.weight ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) (q.nonneg ab.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_one, mul_one]
    exact p.sum_one

@[simp] theorem prod_weight (p : FiniteDist α) (q : FiniteDist β) (ab : α × β) :
    (p.prod q).weight ab = p.weight ab.1 * q.weight ab.2 := rfl

/-- Exact uniform law on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteDist α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    simp [Fintype.card_ne_zero]

@[simp] theorem uniform_weight [Nonempty α] (a : α) :
    (uniform α).weight a = (Fintype.card α : ℝ)⁻¹ := rfl

@[simp] theorem mix_const (p : FiniteDist α) (q : FiniteDist β) :
    p.mix (fun _ => q) = q := by
  ext b
  simp only [mix_weight, ← Finset.sum_mul, p.sum_one, one_mul]

/-- An equivalence pushes a distribution's weight to its inverse image. -/
@[simp] theorem map_equiv_weight (p : FiniteDist α) (e : α ≃ β) (b : β) :
    (p.map e).weight b = p.weight (e.symm b) := by
  classical
  simp only [map_weight, e.apply_eq_iff_eq_symm_apply]
  simp

/-- Every permutation preserves the exact uniform law. -/
@[simp] theorem uniform_map_equiv [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  ext b
  simp only [map_equiv_weight, uniform_weight, Fintype.card_congr e]











end FiniteDist
end AFT


