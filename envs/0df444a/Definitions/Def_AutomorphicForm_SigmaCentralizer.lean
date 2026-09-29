-- Prove2me | Definitions.Def_AutomorphicForm_SigmaCentralizer
-- name    : AutomorphicForm_SigmaCentralizer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/3fdd8d5d-5def-5fd2-b723-bd5878ee70ea
-- title:
--   The σ-twisted centralizer of a group element
-- statement:
--   For a group $G$, a monoid endomorphism $\sigma : G \to G$ and an element $\delta \in G$, [`AutomorphicForm.sigmaCentralizer`](../def/AutomorphicForm_SigmaCentralizer.html#L10) is the subgroup of $G$ whose underlying set is $\{t \in G \mid t\,\delta\,\sigma(t)^{-1} = \delta\}$, i.e. the stabiliser of $\delta$ under the $\sigma$-twisted conjugation action $(t,\delta) \mapsto t\,\delta\,\sigma(t)^{-1}$. The subgroup axioms are verified directly: $1$ lies in the set because $\sigma(1) = 1$; closure under multiplication uses $\sigma(ab) = \sigma(a)\sigma(b)$ together with the identity $ab\,\delta\,\sigma(ab)^{-1} = a\,(b\,\delta\,\sigma(b)^{-1})\,\sigma(a)^{-1}$; and closure under inverses follows from the rearrangement $\delta\,\sigma(a) = a\,\delta$ of the defining equation.
--
--   Three mutually equivalent descriptions of membership are recorded. The defining one, `mem_sigmaCentralizer_iff`, is the equation $t\,\delta\,\sigma(t)^{-1} = \delta$; `mem_sigmaCentralizer_iff_fixed` rewrites it as $\delta\,\sigma(t)\,\delta^{-1} = t$, exhibiting membership as $t$ being fixed by the map $g \mapsto \delta\,\sigma(g)\,\delta^{-1}$; and `mem_sigmaCentralizer_iff_inv` rewrites it as $t^{-1}\,\delta\,\sigma(t) = \delta$. Two degenerate cases are identified. When $\sigma$ is the identity endomorphism, `sigmaCentralizer_id` shows that the $\sigma$-twisted centralizer coincides with Mathlib's centralizer $\mathrm{Subgroup.centralizer}\,\{\delta\}$ of the singleton $\{\delta\}$. When $\sigma$ is the trivial homomorphism sending everything to $1$, `sigmaCentralizer_one_eq_bot` shows the subgroup is trivial: the defining equation becomes $t\,\delta = \delta$, forcing $t = 1$. No symmetry or transitivity properties of $\sigma$-conjugacy are established here; the endomorphism $\sigma$ enters only through the homomorphism laws $\sigma(1) = 1$ and $\sigma(ab) = \sigma(a)\sigma(b)$.
--
--   **Relation to Mathlib.** Mathlib provides the ordinary centralizer `Subgroup.centralizer`; the twisted variant is the project's own, and `sigmaCentralizer_id` identifies it with `Subgroup.centralizer {δ}` in the untwisted case.
--
--   **Where it is used.** Twisted conjugation and its stabilisers are the group-theoretic substrate of the automorphic side of the argument, where $\sigma$-conjugacy classes (for $\sigma$ induced by a field automorphism) index the terms to be compared; this module supplies the stabiliser subgroup over which such comparisons are organised.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SigmaCentralizer.lean

import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AutomorphicForm

variable {G : Type*} [Group G]

def sigmaCentralizer (σ : G →* G) (δ : G) : Subgroup G where
  carrier := {t | t * δ * (σ t)⁻¹ = δ}
  one_mem' := by
    simp only [Set.mem_setOf_eq, one_mul, map_one, inv_one, mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have key : a * b * δ * (σ (a * b))⁻¹ = a * (b * δ * (σ b)⁻¹) * (σ a)⁻¹ := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [key, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, inv_inv]
    have h2 : δ * σ a = a * δ := by
      calc δ * σ a = (a * δ * (σ a)⁻¹) * σ a := by rw [ha]
        _ = a * δ := by group
    calc a⁻¹ * δ * σ a = a⁻¹ * (δ * σ a) := by group
      _ = a⁻¹ * (a * δ) := by rw [h2]
      _ = δ := by group

@[simp] theorem mem_sigmaCentralizer_iff {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t * δ * (σ t)⁻¹ = δ := Iff.rfl

theorem mem_sigmaCentralizer_iff_fixed {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ δ * σ t * δ⁻¹ = t := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem mem_sigmaCentralizer_iff_inv {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t⁻¹ * δ * σ t = δ := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact eq_comm

theorem sigmaCentralizer_id (δ : G) :
    sigmaCentralizer (MonoidHom.id G) δ = Subgroup.centralizer {δ} := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_centralizer_singleton_iff, MonoidHom.id_apply,
    mul_inv_eq_iff_eq_mul]

theorem sigmaCentralizer_one_eq_bot (δ : G) :
    sigmaCentralizer (1 : G →* G) δ = ⊥ := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : t * δ = δ := by
      simpa using h
    exact mul_right_cancel (by rw [one_mul]; exact h1)
  · rintro rfl
    simp


