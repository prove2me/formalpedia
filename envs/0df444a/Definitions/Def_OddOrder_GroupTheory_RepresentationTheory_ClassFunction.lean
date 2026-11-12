-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
-- name    : OddOrder_GroupTheory_RepresentationTheory_ClassFunction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:13.888612+00:00
-- url     : https://prove2.me/theorems/02e0e0f7-ae9c-4f55-a30a-875c4ae13f5e
-- title:
--   Class functions on a group
-- statement:
--   Defines class functions: functions $G\to k$ into a commutative ring $k$ that are constant on conjugacy classes. Mathlib has no `ClassFunction` type, so this module introduces one as the starting point of the Peterfalvi development, to handle $\mathrm{CF}(G)$, $\mathrm{CF}(G,A)$ and inner products $\langle\alpha,\beta\rangle_G$ uniformly (Dade isometry and coherence, §3–§8).
--
--   Main definitions: `classFunctionSubmodule` (the submodule of conjugation-invariant functions), `ClassFunction` (the class-function type, with its additive group and module structure), `restrict` (restriction to a subgroup), and `compHom` (pullback along a group homomorphism).
--
--   The bundle also proves 49 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

namespace OddOrder.RepresentationTheory

/-- The submodule of class functions on `G` valued in `k`:
functions `f : G → k` satisfying `f (h * g * h⁻¹) = f g`. -/
def classFunctionSubmodule (G : Type*) [Group G] (k : Type*) [CommRing k] :
    Submodule k (G → k) where
  carrier := { f | ∀ g h : G, f (h * g * h⁻¹) = f g }
  add_mem' {f₁ f₂} h₁ h₂ g h := by
    simp only [Pi.add_apply]
    rw [h₁ g h, h₂ g h]
  zero_mem' _ _ := rfl
  smul_mem' c f hf g h := by
    simp only [Pi.smul_apply]
    rw [hf]

/-- A **class function** on `G` valued in `k`: a function `G → k` constant on
conjugacy classes. -/
def ClassFunction (G : Type*) [Group G] (k : Type*) [CommRing k] : Type _ :=
  ↥(classFunctionSubmodule G k)

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

instance instAddCommGroup : AddCommGroup (ClassFunction G k) :=
  inferInstanceAs (AddCommGroup ↥(classFunctionSubmodule G k))

instance instModule : Module k (ClassFunction G k) :=
  inferInstanceAs (Module k ↥(classFunctionSubmodule G k))

instance : CoeFun (ClassFunction G k) (fun _ => G → k) :=
  ⟨fun φ => (φ.val : G → k)⟩

@[simp] theorem coe_mk (f : G → k) (hf) :
    ((⟨f, hf⟩ : ClassFunction G k) : G → k) = f := rfl

/-- Conjugation invariance: the defining property of a class function. -/
theorem conj_eq (φ : ClassFunction G k) (g h : G) : φ (h * g * h⁻¹) = φ g :=
  φ.property g h

/-- A class function is constant on conjugacy classes (`IsConj` form). -/
theorem of_isConj (φ : ClassFunction G k) {g₁ g₂ : G} (hg : IsConj g₁ g₂) :
    φ g₁ = φ g₂ := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hg
  exact (φ.conj_eq g₁ h).symm

@[ext]
theorem ext {φ ψ : ClassFunction G k} (h : ∀ g, φ g = ψ g) : φ = ψ :=
  Subtype.ext (funext h)

@[simp] theorem zero_apply (g : G) : (0 : ClassFunction G k) g = 0 := rfl

@[simp] theorem add_apply (φ ψ : ClassFunction G k) (g : G) :
    (φ + ψ) g = φ g + ψ g := rfl

@[simp] theorem neg_apply (φ : ClassFunction G k) (g : G) : (-φ) g = -φ g := rfl

@[simp] theorem sub_apply (φ ψ : ClassFunction G k) (g : G) :
    (φ - ψ) g = φ g - ψ g := rfl

@[simp] theorem smul_apply (c : k) (φ : ClassFunction G k) (g : G) :
    (c • φ) g = c * φ g := rfl

section Restrict

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- The **restriction** `Res^G_H φ : ClassFunction ↥H k` of a class function on `G`
to a subgroup `H ≤ G`. -/
def restrict (H : Subgroup G) (φ : ClassFunction G k) : ClassFunction ↥H k :=
  ⟨fun h => φ (h : G), fun h₁ h₂ => by
    change φ ((h₂ : G) * (h₁ : G) * ((h₂⁻¹ : H) : G)) = φ (h₁ : G)
    rw [show ((h₂⁻¹ : H) : G) = (h₂ : G)⁻¹ from rfl]
    exact φ.conj_eq h₁ h₂⟩

@[simp] theorem restrict_apply (H : Subgroup G) (φ : ClassFunction G k) (h : H) :
    (restrict H φ) h = φ (h : G) := rfl

@[simp] theorem restrict_zero (H : Subgroup G) :
    restrict H (0 : ClassFunction G k) = 0 := by
  ext h; simp

theorem restrict_add (H : Subgroup G) (φ ψ : ClassFunction G k) :
    restrict H (φ + ψ) = restrict H φ + restrict H ψ := by
  ext h; simp

theorem restrict_smul (H : Subgroup G) (c : k) (φ : ClassFunction G k) :
    restrict H (c • φ) = c • restrict H φ := by
  ext h; simp

end Restrict

section CompHom

variable {G : Type*} [Group G] {H : Type*} [Group H] {k : Type*} [CommRing k]

/-- The **pullback** `φ ∘ f : ClassFunction H k` of a class function on `G` along a group
homomorphism `f : H →* G`.  Conjugation invariance is preserved because `f` is a
homomorphism: `f (h₂ * h₁ * h₂⁻¹) = f h₂ * f h₁ * (f h₂)⁻¹`.

This generalizes `restrict` (the special case `f = H.subtype`); it is the construction
behind Peterfalvi (2.9)'s `α_B = α ∘ f_B`, where `f_B : M(B) →* L` is the quotient map of
the semidirect decomposition `M(B) = H(B) ⋊ N_L(B)`. -/
def compHom (f : H →* G) (φ : ClassFunction G k) : ClassFunction H k :=
  ⟨fun h => φ (f h), fun h₁ h₂ => by
    change φ (f (h₂ * h₁ * h₂⁻¹)) = φ (f h₁)
    rw [map_mul, map_mul, map_inv]
    exact φ.conj_eq (f h₁) (f h₂)⟩

@[simp] theorem compHom_apply (f : H →* G) (φ : ClassFunction G k) (h : H) :
    compHom f φ h = φ (f h) := rfl

variable {K : Type*} [Group K] in
/-- Pullback is contravariantly functorial: `(φ ∘ f) ∘ g = φ ∘ (f ∘ g)`. -/
theorem compHom_comp (f : H →* G) (g : K →* H) (φ : ClassFunction G k) :
    compHom g (compHom f φ) = compHom (f.comp g) φ := rfl

@[simp] theorem compHom_zero (f : H →* G) :
    compHom f (0 : ClassFunction G k) = 0 := by ext h; simp

theorem compHom_add (f : H →* G) (φ ψ : ClassFunction G k) :
    compHom f (φ + ψ) = compHom f φ + compHom f ψ := by ext h; simp

theorem compHom_smul (f : H →* G) (c : k) (φ : ClassFunction G k) :
    compHom f (c • φ) = c • compHom f φ := by ext h; simp

end CompHom

section Support

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- The **support** of a class function: `{ g | φ g ≠ 0 }`. Closed under
conjugation by the defining property. -/
def support (φ : ClassFunction G k) : Set G := { g | φ g ≠ 0 }

@[simp] theorem mem_support {φ : ClassFunction G k} {g : G} :
    g ∈ φ.support ↔ φ g ≠ 0 := Iff.rfl

@[simp] theorem support_zero : (0 : ClassFunction G k).support = ∅ := by
  ext g; simp

@[simp] theorem support_neg (φ : ClassFunction G k) : (-φ).support = φ.support := by
  ext g
  simp [support]

/-- The support of a sum is contained in the union of the supports. -/
theorem support_add_subset (φ ψ : ClassFunction G k) :
    (φ + ψ).support ⊆ φ.support ∪ ψ.support := by
  intro g hg
  by_cases hφ : φ g = 0
  · right
    by_contra hψ
    have hψ_zero : ψ g = 0 := by simpa [mem_support] using hψ
    exact hg (by simp [hφ, hψ_zero])
  · left
    exact hφ

/-- The support of a scalar multiple is contained in the original support. -/
theorem support_smul_subset (c : k) (φ : ClassFunction G k) :
    (c • φ).support ⊆ φ.support := by
  intro g hg
  by_contra hφ
  have hφ_zero : φ g = 0 := by simpa [mem_support] using hφ
  exact hg (by simp [hφ_zero])

theorem support_sub_subset (φ ψ : ClassFunction G k) :
    (φ - ψ).support ⊆ φ.support ∪ ψ.support := by
  simpa [sub_eq_add_neg] using support_add_subset φ (-ψ)

@[simp] theorem support_restrict (H : Subgroup G) (φ : ClassFunction G k) :
    (restrict H φ).support = {h : H | (h : G) ∈ φ.support} := by
  ext h
  rfl

/-- The submodule of class functions supported on `A`.

This is Peterfalvi's `CF(G, A)`. -/
def supportedSubmodule (A : Set G) : Submodule k (ClassFunction G k) where
  carrier := { φ | φ.support ⊆ A }
  zero_mem' := by
    intro g hg
    simp [support] at hg
  add_mem' {φ ψ} hφ hψ := by
    intro g hg
    rcases support_add_subset φ ψ hg with h | h
    · exact hφ h
    · exact hψ h
  smul_mem' c φ hφ := by
    intro g hg
    exact hφ (support_smul_subset c φ hg)

@[simp] theorem mem_supportedSubmodule {A : Set G} {φ : ClassFunction G k} :
    φ ∈ supportedSubmodule (G := G) (k := k) A ↔ φ.support ⊆ A := Iff.rfl

end Support

section Inner

variable {G : Type*} [Group G] [Fintype G]

variable {k : Type*} [CommRing k] [StarRing k]

/-- The **unscaled inner sum** of two class functions: `Σ_g φ(g) * star(ψ(g))`.

Peterfalvi's `(α, β)_G = (1/|G|) Σ_g α(g) · β̄(g)` corresponds to this sum
divided by `Nat.card G`. We expose the bare sum here so that the user can
choose how to invert `|G|` (e.g. in a field of characteristic prime to `|G|`,
or formally as `Nat.card G : ℂ`). -/
def innerSum (φ ψ : ClassFunction G k) : k :=
  ∑ g : G, φ g * star (ψ g)

/-- Peterfalvi's normalized class-function inner product.

The explicit `Invertible` assumption keeps the definition available over any
coefficient ring where `|G|` has a chosen inverse. -/
def inner [Invertible (Nat.card G : k)] (φ ψ : ClassFunction G k) : k :=
  ⅟(Nat.card G : k) * innerSum φ ψ

@[simp] theorem inner_eq_inv_card_mul_innerSum [Invertible (Nat.card G : k)]
    (φ ψ : ClassFunction G k) :
    inner φ ψ = ⅟(Nat.card G : k) * innerSum φ ψ :=
  rfl

@[simp] theorem card_mul_inner [Invertible (Nat.card G : k)]
    (φ ψ : ClassFunction G k) :
    (Nat.card G : k) * inner φ ψ = innerSum φ ψ := by
  rw [inner, ← mul_assoc, mul_invOf_self, one_mul]

/-- The unscaled inner sum is star-symmetric: `Σ φ(g)·star(ψ(g)) = star (Σ ψ(g)·star(φ(g)))`. -/
theorem innerSum_star_comm (φ ψ : ClassFunction G k) :
    innerSum φ ψ = star (innerSum ψ φ) := by
  unfold innerSum
  rw [show star (∑ g : G, ψ g * star (φ g)) = ∑ g : G, star (ψ g * star (φ g)) from
    map_sum starAddEquiv _ _]
  simp only [star_mul, star_star]

/-- The normalized inner product is star-symmetric: `⟨φ, ψ⟩ = star ⟨ψ, φ⟩`. -/
theorem inner_star_comm [Invertible (Nat.card G : k)] (φ ψ : ClassFunction G k) :
    inner φ ψ = star (inner ψ φ) := by
  have hstar : (Nat.card G : k) * star (inner ψ φ) = star ((Nat.card G : k) * inner ψ φ) := by
    rw [star_mul, star_natCast]
    exact mul_comm _ _
  have h : (Nat.card G : k) * inner φ ψ = (Nat.card G : k) * star (inner ψ φ) := by
    rw [card_mul_inner, innerSum_star_comm, hstar, card_mul_inner]
  calc inner φ ψ = ⅟(Nat.card G : k) * ((Nat.card G : k) * inner φ ψ) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = ⅟(Nat.card G : k) * ((Nat.card G : k) * star (inner ψ φ)) := by rw [h]
    _ = star (inner ψ φ) := by rw [← mul_assoc, invOf_mul_self, one_mul]

/-- If two class functions have disjoint supports, their unscaled inner sum vanishes:
every summand `φ g * star (ψ g)` is zero because `g` lies outside at least one support. -/
theorem innerSum_eq_zero_of_disjoint_support {φ ψ : ClassFunction G k}
    (h : Disjoint φ.support ψ.support) : innerSum φ ψ = 0 := by
  refine Finset.sum_eq_zero fun g _ => ?_
  by_cases hφ : g ∈ φ.support
  · have hψ : g ∉ ψ.support := Set.disjoint_left.mp h hφ
    rw [show ψ g = 0 from not_not.mp hψ, star_zero, mul_zero]
  · rw [show φ g = 0 from not_not.mp hφ, zero_mul]

@[simp] theorem innerSum_zero_left (ψ : ClassFunction G k) :
    innerSum (0 : ClassFunction G k) ψ = 0 := by
  simp [innerSum]

@[simp] theorem innerSum_zero_right (φ : ClassFunction G k) :
    innerSum φ (0 : ClassFunction G k) = 0 := by
  simp [innerSum]

theorem innerSum_add_left (φ₁ φ₂ ψ : ClassFunction G k) :
    innerSum (φ₁ + φ₂) ψ = innerSum φ₁ ψ + innerSum φ₂ ψ := by
  simp [innerSum, add_mul, Finset.sum_add_distrib]

theorem innerSum_add_right (φ ψ₁ ψ₂ : ClassFunction G k) :
    innerSum φ (ψ₁ + ψ₂) = innerSum φ ψ₁ + innerSum φ ψ₂ := by
  simp [innerSum, star_add, mul_add, Finset.sum_add_distrib]

theorem innerSum_smul_left (c : k) (φ ψ : ClassFunction G k) :
    innerSum (c • φ) ψ = c * innerSum φ ψ := by
  rw [innerSum, innerSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smul_apply, mul_assoc]

theorem innerSum_smul_right (c : k) (φ ψ : ClassFunction G k) :
    innerSum φ (c • ψ) = star c * innerSum φ ψ := by
  rw [innerSum, innerSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smul_apply, star_mul']
  exact mul_left_comm _ _ _

theorem innerSum_neg_left (φ ψ : ClassFunction G k) :
    innerSum (-φ) ψ = -innerSum φ ψ := by
  simp [innerSum, neg_mul, Finset.sum_neg_distrib]

theorem innerSum_neg_right (φ ψ : ClassFunction G k) :
    innerSum φ (-ψ) = -innerSum φ ψ := by
  simp [innerSum, mul_neg, Finset.sum_neg_distrib]

@[simp] theorem inner_zero_left [Invertible (Nat.card G : k)] (ψ : ClassFunction G k) :
    inner (0 : ClassFunction G k) ψ = 0 := by
  simp [inner]

@[simp] theorem inner_zero_right [Invertible (Nat.card G : k)] (φ : ClassFunction G k) :
    inner φ (0 : ClassFunction G k) = 0 := by
  simp [inner]

/-- **Peterfalvi §2 (orthogonality of disjointly-supported class functions).**
If `φ` and `ψ` have disjoint supports then `⟨φ, ψ⟩_G = 0`. This is the basic
vanishing used throughout the Dade isometry / coherence arguments: characters
supported on disjoint sets of group elements are orthogonal. -/
theorem inner_eq_zero_of_disjoint_support [Invertible (Nat.card G : k)]
    {φ ψ : ClassFunction G k} (h : Disjoint φ.support ψ.support) :
    inner φ ψ = 0 := by
  rw [inner_eq_inv_card_mul_innerSum, innerSum_eq_zero_of_disjoint_support h, mul_zero]

theorem inner_add_left [Invertible (Nat.card G : k)]
    (φ₁ φ₂ ψ : ClassFunction G k) :
    inner (φ₁ + φ₂) ψ = inner φ₁ ψ + inner φ₂ ψ := by
  simp [inner, innerSum_add_left, mul_add]

theorem inner_add_right [Invertible (Nat.card G : k)]
    (φ ψ₁ ψ₂ : ClassFunction G k) :
    inner φ (ψ₁ + ψ₂) = inner φ ψ₁ + inner φ ψ₂ := by
  simp [inner, innerSum_add_right, mul_add]

theorem inner_smul_left [Invertible (Nat.card G : k)]
    (c : k) (φ ψ : ClassFunction G k) :
  inner (c • φ) ψ = c * inner φ ψ := by
  rw [inner, innerSum_smul_left, inner]
  rw [← mul_assoc, mul_comm (⅟(Nat.card G : k)) c, mul_assoc]

theorem inner_smul_right [Invertible (Nat.card G : k)]
    (c : k) (φ ψ : ClassFunction G k) :
  inner φ (c • ψ) = star c * inner φ ψ := by
  rw [inner, innerSum_smul_right, inner]
  rw [← mul_assoc, mul_comm (⅟(Nat.card G : k)) (star c), mul_assoc]

theorem inner_neg_left [Invertible (Nat.card G : k)] (φ ψ : ClassFunction G k) :
    inner (-φ) ψ = -inner φ ψ := by
  simp [inner, innerSum_neg_left]

theorem inner_neg_right [Invertible (Nat.card G : k)] (φ ψ : ClassFunction G k) :
    inner φ (-ψ) = -inner φ ψ := by
  simp [inner, innerSum_neg_right]

theorem inner_sub_left [Invertible (Nat.card G : k)]
    (φ₁ φ₂ ψ : ClassFunction G k) :
    inner (φ₁ - φ₂) ψ = inner φ₁ ψ - inner φ₂ ψ := by
  rw [sub_eq_add_neg, inner_add_left, inner_neg_left, sub_eq_add_neg]

theorem inner_sub_right [Invertible (Nat.card G : k)]
    (φ ψ₁ ψ₂ : ClassFunction G k) :
    inner φ (ψ₁ - ψ₂) = inner φ ψ₁ - inner φ ψ₂ := by
  rw [sub_eq_add_neg, inner_add_right, inner_neg_right, sub_eq_add_neg]

end Inner

end ClassFunction

end OddOrder.RepresentationTheory


