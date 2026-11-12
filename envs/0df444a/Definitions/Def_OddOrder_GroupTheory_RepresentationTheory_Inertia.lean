-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Inertia
-- name    : OddOrder_GroupTheory_RepresentationTheory_Inertia
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:25.497846+00:00
-- url     : https://prove2.me/theorems/a0d006a8-6602-45f2-aa38-ebd24422946e
-- title:
--   Conjugation action on class functions and the inertia group
-- statement:
--   For a normal subgroup $H\trianglelefteq G$ and a class function $\theta$ on $H$, defines the conjugate $\theta^g(h)=\theta(ghg^{-1})$ (Peterfalvi's $\theta^g$), giving a $G$-action on class functions of $H$, and the inertia group $I_G(\theta)=\{g\in G:\theta^g=\theta\}$. Used heavily in Peterfalvi §3 (1.5)/(1.7) (Clifford) and §4–§8.
--
--   Main definitions: `conjBy` (the conjugate class function), `conjByEquiv` (the permutation of $H$ induced by conjugation by an ambient element), `conjByMulEquiv` (the induced group automorphism of $H$) and `inertia` ($I_G(\theta)$).
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/Inertia.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/Inertia.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable {k : Type*} [CommRing k]

/-- The conjugate of `θ : ClassFunction ↥H k` by `g : G`. Defined by
`(θ.conjBy g) h = θ (g * h * g⁻¹)`. Well-defined since `H ⊴ G`. -/
def conjBy (g : G) (θ : ClassFunction ↥H k) : ClassFunction ↥H k where
  val h := θ ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.property g⟩
  property h₁ h₂ := by
    have hy : g * (h₂ : G) * g⁻¹ ∈ H := hH.conj_mem (h₂ : G) h₂.property g
    let y : ↥H := ⟨g * (h₂ : G) * g⁻¹, hy⟩
    have key : (⟨g * ((h₂ * h₁ * h₂⁻¹ : ↥H) : G) * g⁻¹,
                  hH.conj_mem _ (h₂ * h₁ * h₂⁻¹ : ↥H).property g⟩ : ↥H)
             = y * ⟨g * (h₁ : G) * g⁻¹, hH.conj_mem _ h₁.property g⟩ * y⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      change g * ((h₂ : G) * (h₁ : G) * (h₂ : G)⁻¹) * g⁻¹
        = (g * (h₂ : G) * g⁻¹) * (g * (h₁ : G) * g⁻¹) * (g * (h₂ : G) * g⁻¹)⁻¹
      group
    change θ ⟨g * ((h₂ * h₁ * h₂⁻¹ : ↥H) : G) * g⁻¹, _⟩
         = θ ⟨g * (h₁ : G) * g⁻¹, _⟩
    rw [key]
    exact θ.conj_eq _ y

@[simp] theorem conjBy_apply (g : G) (θ : ClassFunction ↥H k) (h : ↥H) :
    (conjBy g θ) h = θ ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.property g⟩ := rfl

/-- Conjugation by an element **already in `H`** acts trivially on class functions
of `H`: if `g ∈ H` then `θ^g = θ`. Indeed `conjBy g θ` evaluates `θ` at the
`H`-conjugate `⟨g, hg⟩ * h * ⟨g, hg⟩⁻¹`, and class functions are constant on
`H`-conjugacy classes.

This is the elementary fact underlying the well-definedness in Peterfalvi (1.5)(a)
of the conjugate `θ^x` as a function of the left coset `I_G(θ)·x`: the relation
`θ^x = θ^y ⇔ y ∈ I(θ)x` rests on `θ^g = θ` for `g ∈ H ⊆ I_G(θ)`, which lets
`conjBy w θ` be constant on the coset `wH` in the Mackey restriction formula. -/
theorem conjBy_eq_self_of_mem {g : G} (hg : g ∈ H) (θ : ClassFunction ↥H k) :
    conjBy g θ = θ := by
  ext h
  rw [conjBy_apply]
  let y : ↥H := ⟨g, hg⟩
  have hconj :
      (⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.property g⟩ : ↥H) =
        y * h * y⁻¹ :=
    Subtype.ext rfl
  rw [hconj]
  exact θ.conj_eq h y

/-- The permutation of `H` induced by conjugation by an ambient element `g : G`.

Normality of `H` is exactly what makes this an equivalence of the subtype `H`. -/
def conjByEquiv (g : G) : H ≃ H where
  toFun h := ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.property g⟩
  invFun h := ⟨g⁻¹ * (h : G) * g, by
    simpa using hH.conj_mem (h : G) h.property g⁻¹⟩
  left_inv h := by
    apply Subtype.ext
    group
  right_inv h := by
    apply Subtype.ext
    group

@[simp] theorem conjByEquiv_apply (g : G) (h : H) :
    (conjByEquiv (G := G) (H := H) g h : G) = g * (h : G) * g⁻¹ :=
  rfl

/-- The group automorphism of `H` induced by conjugation by an ambient element. -/
def conjByMulEquiv (g : G) : H ≃* H where
  __ := conjByEquiv (G := G) (H := H) g
  map_mul' h₁ h₂ := by
    apply Subtype.ext
    simp [conjByEquiv]

@[simp] theorem conjByMulEquiv_apply (g : G) (h : H) :
    (conjByMulEquiv (G := G) (H := H) g h : G) = g * (h : G) * g⁻¹ :=
  rfl

@[simp] theorem conjByMulEquiv_one (h : H) :
    conjByMulEquiv (G := G) (H := H) (1 : G) h = h :=
  Subtype.ext (by simp)

/-- Conjugation automorphisms compose like a left action:
`conj_{g₁} ∘ conj_{g₂} = conj_{g₁ g₂}`. -/
theorem conjByMulEquiv_mul (g₁ g₂ : G) (h : H) :
    conjByMulEquiv (G := G) (H := H) g₁ (conjByMulEquiv (G := G) (H := H) g₂ h)
      = conjByMulEquiv (G := G) (H := H) (g₁ * g₂) h :=
  Subtype.ext (by simp only [conjByMulEquiv_apply]; group)

@[simp] theorem conjBy_one (θ : ClassFunction ↥H k) : conjBy (1 : G) θ = θ := by
  ext h
  simp

theorem conjBy_mul (g₁ g₂ : G) (θ : ClassFunction ↥H k) :
    conjBy (g₁ * g₂) θ = conjBy g₂ (conjBy g₁ θ) := by
  ext h
  let h' : ↥H := ⟨g₂ * (h : G) * g₂⁻¹, hH.conj_mem _ h.property g₂⟩
  change θ ⟨(g₁ * g₂) * (h : G) * (g₁ * g₂)⁻¹, _⟩
      = θ ⟨g₁ * (h' : G) * g₁⁻¹, _⟩
  apply congrArg θ
  apply Subtype.ext
  change (g₁ * g₂) * (h : G) * (g₁ * g₂)⁻¹ = g₁ * (g₂ * (h : G) * g₂⁻¹) * g₁⁻¹
  group

@[simp] theorem conjBy_inv_conjBy (g : G) (θ : ClassFunction ↥H k) :
    conjBy (G := G) (H := H) g⁻¹ (conjBy (G := G) (H := H) g θ) = θ := by
  simpa using (conjBy_mul (G := G) (H := H) g g⁻¹ θ).symm

@[simp] theorem conjBy_conjBy_inv (g : G) (θ : ClassFunction ↥H k) :
    conjBy (G := G) (H := H) g (conjBy (G := G) (H := H) g⁻¹ θ) = θ := by
  simpa using (conjBy_mul (G := G) (H := H) g⁻¹ g θ).symm

/-- Restricting an ambient class function to a normal subgroup gives a function
invariant under all ambient conjugations, not only conjugations by subgroup
elements. -/
theorem conjBy_restrict (g : G) (χ : ClassFunction G k) :
    conjBy (G := G) (H := H) g (restrict H χ) = restrict H χ := by
  ext h
  exact χ.conj_eq (h : G) g

section Inner

variable [Fintype H] [StarRing k]

theorem innerSum_conjBy_conjBy (g : G) (φ ψ : ClassFunction H k) :
    innerSum (conjBy (G := G) (H := H) g φ) (conjBy (G := G) (H := H) g ψ) =
      innerSum φ ψ := by
  simpa [innerSum, conjByEquiv] using
    Fintype.sum_equiv (conjByEquiv (G := G) (H := H) g)
      (fun h : H => φ (conjByEquiv (G := G) (H := H) g h) *
        star (ψ (conjByEquiv (G := G) (H := H) g h)))
      (fun h : H => φ h * star (ψ h))
      (fun _ => rfl)

theorem inner_conjBy_conjBy [Invertible (Nat.card H : k)]
    (g : G) (φ ψ : ClassFunction H k) :
    inner (conjBy (G := G) (H := H) g φ) (conjBy (G := G) (H := H) g ψ) =
      inner φ ψ := by
  simp [inner, innerSum_conjBy_conjBy]

end Inner

/-- The **inertia group** of a class function `θ` under `G`-conjugation:
`I_G(θ) = { g ∈ G | θ^g = θ }`. -/
def inertia (θ : ClassFunction ↥H k) : Subgroup G where
  carrier := { g | conjBy g θ = θ }
  one_mem' := by
    change conjBy (1 : G) θ = θ
    exact conjBy_one θ
  mul_mem' {g₁ g₂} hg₁ hg₂ := by
    change conjBy g₁ θ = θ at hg₁
    change conjBy g₂ θ = θ at hg₂
    change conjBy (g₁ * g₂) θ = θ
    rw [conjBy_mul, hg₁, hg₂]
  inv_mem' {g} hg := by
    change conjBy g θ = θ at hg
    change conjBy g⁻¹ θ = θ
    have hprod : conjBy (g * g⁻¹) θ = θ := by
      simp
    rw [conjBy_mul, hg] at hprod
    simpa using hprod

@[simp] theorem mem_inertia {θ : ClassFunction ↥H k} {g : G} :
    g ∈ inertia θ ↔ conjBy g θ = θ := Iff.rfl

/-- The normal subgroup `H` is contained in the inertia group of every class
function on `H`, because class functions are invariant under conjugation by
elements of `H`. -/
theorem subgroup_le_inertia (θ : ClassFunction ↥H k) : H ≤ inertia θ := by
  intro h hh
  rw [mem_inertia]
  exact conjBy_eq_self_of_mem hh θ

/-- Since `H ⊴ G`, the subgroup `H` remains normal inside the inertia group
`I_G(θ)`. -/
theorem subgroupOf_inertia_normal (θ : ClassFunction ↥H k) :
    (H.subgroupOf (inertia θ)).Normal :=
  hH.subgroupOf (inertia θ)

/-- Membership in `H` after viewing it as a subgroup of `I_G(θ)`. -/
@[simp] theorem mem_subgroupOf_inertia {θ : ClassFunction ↥H k} {g : inertia θ} :
    g ∈ H.subgroupOf (inertia θ) ↔ (g : G) ∈ H :=
  Subgroup.mem_subgroupOf

end ClassFunction

end OddOrder.RepresentationTheory


