-- Prove2me | Definitions.Def_LocalLanglands_GelfandInvolution
-- name    : LocalLanglands_GelfandInvolution
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/35be94bb-8dc4-5dea-b9c2-5238586f0984
-- title:
--   Gelfand involutions and commutativity of Hecke algebras
-- statement:
--   Let $G$ be a group, $U \le G$ a subgroup and $R_0$ a commutative ring, and let $H =$ `HeckeAlgebra U R₀` be the $R_0$-algebra of functions $f : G \to R_0$ that are invariant under left and right translation by $U$ and whose support has finite image in $G/U$, with convolution $(f_1 * f_2)(x) = \sum_{yU \in G/U} f_1(y)\,f_2(y^{-1}x)$ as product. Two preliminary lemmas record that such an $f$ is constant on the double coset $UgU$ (defined as the pointwise product $U\{g\}U$), and that membership $x \in UgU$ forces $UxU = UgU$.
--
--   The structure `IsGelfandInvolution U τ` is a predicate on a map $\tau : G \to G$ with four fields: $\tau(xy) = \tau(y)\tau(x)$ for all $x,y$; $\tau(\tau x) = x$ for all $x$; $\tau(u) \in U$ for every $u \in U$; and $\tau(g) \in UgU$ for every $g \in G$. From these it is deduced that $\tau(1) = 1$, $\tau(x^{-1}) = (\tau x)^{-1}$, that $\tau$ is bijective, and that $f(\tau x) = f(x)$ for every $f \in H$. For fixed $x \in G$ the maps $yU \mapsto x(\tau y)^{-1}U$ and $zU \mapsto \tau(z^{-1}x)U$ are well defined on $G/U$ and mutually inverse; comparing the convolution terms through the first of them gives $(f_1 * f_2)(\tau x) = (f_2 * f_1)(x)$ and hence $f_1 * f_2 = f_2 * f_1$ for all $f_1, f_2 \in H$. The corresponding `CommRing` structure on $H$ is provided as a definition, `commRing`, refining the existing ring structure by this commutativity rather than being registered as an instance. Finally, `of_forall_exists_fixedRep` builds a Gelfand involution from the first three conditions together with the hypothesis that every $g \in G$ lies in $UdU$ for some $d$ with $\tau(d) = d$.
--
--   **Relation to Mathlib.** Mathlib has no Hecke algebra of an abstract Hecke pair and no notion of Gelfand involution; both the algebra $H$ (in the imported module) and the predicate here are the project's own, built on Mathlib's quotient groups, pointwise set products and unconditionally convergent sums (`finsum`).
--
--   **Where it is used.** This is the abstract form of Gelfand's involution argument used to obtain commutativity of the local spherical Hecke algebra of $\mathrm{GL}_2$ over a local field relative to $\mathrm{GL}_2(\mathcal{O})$: transposition satisfies the four conditions, the double-coset condition coming from a Cartan decomposition with symmetric representatives via `of_forall_exists_fixedRep`. Commutativity is what makes the local Hecke theory used in the automorphic side of the argument a theory of characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_GelfandInvolution.lean

import Mathlib
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G}
variable {R₀ : Type*} [CommRing R₀]

theorem apply_eq_of_mem_doubleCoset (f : HeckeAlgebra U R₀) {g x : G}
    (hx : x ∈ doubleCoset U g) : (f : G → R₀) x = (f : G → R₀) g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  rw [apply_mul_right f hv, apply_left_mul f hu]

theorem doubleCoset_eq_of_mem {g x : G} (hx : x ∈ doubleCoset U g) :
    doubleCoset U x = doubleCoset U g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hw
    exact mem_doubleCoset_iff.mpr ⟨a * u, mul_mem ha hu, v * b, mul_mem hv hb, by group⟩
  · intro hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hw
    exact mem_doubleCoset_iff.mpr
      ⟨a * u⁻¹, mul_mem ha (inv_mem hu), v⁻¹ * b, mul_mem (inv_mem hv) hb, by group⟩

variable (U) in

structure IsGelfandInvolution (τ : G → G) : Prop where

  map_mul : ∀ x y, τ (x * y) = τ y * τ x

  involutive : ∀ x, τ (τ x) = x

  map_mem : ∀ u ∈ U, τ u ∈ U

  mem_doubleCoset : ∀ g, τ g ∈ doubleCoset U g

namespace IsGelfandInvolution

variable {τ : G → G} (hτ : IsGelfandInvolution U τ)

include hτ

theorem map_one : τ 1 = 1 := by
  have h := hτ.map_mul 1 1
  rw [one_mul] at h

  exact (mul_right_cancel (a := (1 : G)) (b := τ 1) (by rw [one_mul, ← h])).symm

theorem map_inv (x : G) : τ x⁻¹ = (τ x)⁻¹ := by
  have h : τ x⁻¹ * τ x = 1 := by rw [← hτ.map_mul, mul_inv_cancel, hτ.map_one]
  exact eq_inv_of_mul_eq_one_left h

theorem bijective : Function.Bijective τ :=
  Function.Involutive.bijective hτ.involutive

theorem apply_tau (f : HeckeAlgebra U R₀) (x : G) : (f : G → R₀) (τ x) = (f : G → R₀) x :=
  apply_eq_of_mem_doubleCoset f (hτ.mem_doubleCoset x)

protected def reindex (x : G) : G ⧸ U → G ⧸ U :=
  Quotient.lift (fun y => (QuotientGroup.mk (x * (τ y)⁻¹) : G ⧸ U)) <| by
    intro a b hab
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, a * u = b :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    refine (QuotientGroup.eq.mpr ?_).symm

    rw [hτ.map_mul a u]
    have hgrp : (x * (τ u * τ a)⁻¹)⁻¹ * (x * (τ a)⁻¹) = τ u := by group
    rw [hgrp]
    exact hτ.map_mem u hu

@[simp] theorem reindex_mk (x y : G) :
    hτ.reindex x (QuotientGroup.mk y) = QuotientGroup.mk (x * (τ y)⁻¹) := rfl

protected def reindexInv (x : G) : G ⧸ U → G ⧸ U :=
  Quotient.lift (fun z => (QuotientGroup.mk (τ (z⁻¹ * x)) : G ⧸ U)) <| by
    intro a b hab
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, a * u = b :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    refine (QuotientGroup.eq.mpr ?_).symm

    have hexp : (a * u)⁻¹ * x = u⁻¹ * (a⁻¹ * x) := by group
    rw [hexp, hτ.map_mul, hτ.map_inv]
    have hgrp : (τ (a⁻¹ * x) * (τ u)⁻¹)⁻¹ * τ (a⁻¹ * x) = τ u := by group
    rw [hgrp]
    exact hτ.map_mem u hu

@[simp] theorem reindexInv_mk (x z : G) :
    hτ.reindexInv x (QuotientGroup.mk z) = QuotientGroup.mk (τ (z⁻¹ * x)) := rfl

theorem bijective_reindex (x : G) : Function.Bijective (hτ.reindex x) := by
  have hleft : ∀ c, hτ.reindexInv x (hτ.reindex x c) = c := by
    refine fun c => Quotient.inductionOn c fun y => ?_
    rw [reindex_mk, reindexInv_mk]
    refine congrArg _ ?_
    have h1 : (x * (τ y)⁻¹)⁻¹ * x = τ y := by group
    rw [h1, hτ.involutive]
  have hright : ∀ c, hτ.reindex x (hτ.reindexInv x c) = c := by
    refine fun c => Quotient.inductionOn c fun z => ?_
    rw [reindexInv_mk, reindex_mk]
    refine congrArg _ ?_
    rw [hτ.involutive]
    group
  exact Function.bijective_iff_has_inverse.mpr ⟨hτ.reindexInv x, hleft, hright⟩

theorem convTerm_tau (f₁ f₂ : HeckeAlgebra U R₀) (x : G) (c : G ⧸ U) :
    convTerm f₁ f₂ (τ x) c = convTerm f₂ f₁ x (hτ.reindex x c) := by
  refine Quotient.inductionOn c fun y => ?_
  rw [reindex_mk, convTerm_mk, convTerm_mk]

  have h2 : (x * (τ y)⁻¹)⁻¹ * x = τ y := by group
  rw [h2, hτ.apply_tau f₁ y]

  have h1 : (f₂ : G → R₀) (y⁻¹ * τ x) = (f₂ : G → R₀) (x * (τ y)⁻¹) := by
    conv_lhs => rw [← hτ.apply_tau f₂ (y⁻¹ * τ x)]
    rw [hτ.map_mul, hτ.involutive, hτ.map_inv]
  rw [h1, mul_comm]

theorem mul_apply_tau (f₁ f₂ : HeckeAlgebra U R₀) (x : G) :
    ((f₁ * f₂ : HeckeAlgebra U R₀) : G → R₀) (τ x)
      = ((f₂ * f₁ : HeckeAlgebra U R₀) : G → R₀) x := by
  rw [mul_apply, mul_apply]
  exact finsum_eq_of_bijective (hτ.reindex x) (hτ.bijective_reindex x)
    (hτ.convTerm_tau f₁ f₂ x)

theorem heckeMul_comm (f₁ f₂ : HeckeAlgebra U R₀) : f₁ * f₂ = f₂ * f₁ := by
  ext x

  rw [← hτ.apply_tau (f₁ * f₂) x, hτ.mul_apply_tau f₁ f₂ x]

@[reducible] protected def commRing : CommRing (HeckeAlgebra U R₀) :=
  { (inferInstance : Ring (HeckeAlgebra U R₀)) with
    mul_comm := hτ.heckeMul_comm }

end IsGelfandInvolution

theorem IsGelfandInvolution.of_forall_exists_fixedRep {τ : G → G}
    (hmul : ∀ x y, τ (x * y) = τ y * τ x) (hinv : ∀ x, τ (τ x) = x)
    (hU : ∀ u ∈ U, τ u ∈ U)
    (hrep : ∀ g : G, ∃ d, τ d = d ∧ g ∈ doubleCoset U d) :
    IsGelfandInvolution U τ := by
  refine ⟨hmul, hinv, hU, fun g => ?_⟩
  obtain ⟨d, hd, hgd⟩ := hrep g

  rw [doubleCoset_eq_of_mem hgd]
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hgd
  rw [hmul, hmul, hd]
  exact mem_doubleCoset_iff.mpr ⟨τ v, hU v hv, τ u, hU u hu, by group⟩

end

end HeckePair


