-- Prove2me | Definitions.Def_ClassFunction_Induced
-- name    : ClassFunction_Induced
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/6da7d777-202a-5bfa-af88-d20a7bd4a27c
-- title:
--   Induced class functions by Frobenius' formula
-- statement:
--   Throughout, $G$ is a finite group, $K$ a field, and $H \le G$ a subgroup. For a function $\varphi \colon G \to K$, [`ClassFunction.induced H φ`](../def/ClassFunction_Induced.html#L13) is the function $G \to K$ given by Frobenius' formula
--   $$g \mapsto (\#H)^{-1}\sum_{x \in G} \begin{cases} \varphi(x^{-1}gx) & x^{-1}gx \in H \\ 0 & \text{otherwise,}\end{cases}$$
--   the cardinality being `Nat.card H` cast into $K$ and its inverse taken in $K$ (so no invertibility hypothesis is imposed at the level of the definition). The object produced is a bare $K$-valued function on $G$, not an element of a type of class functions; its conjugation invariance is a separate assertion.
--
--   The accompanying lemmas record the elementary calculus of this operation. `induced_apply` restates the defining formula with a decidability instance for membership in $H$ in place of the classical one. `induced_congr`: the result depends only on the restriction $\varphi|_H$. `induced_conj`: $\operatorname{Ind}_H^G\varphi(y^{-1}gy) = \operatorname{Ind}_H^G\varphi(g)$, i.e. the induced function is a class function. `induced_add`, `induced_zero`, `induced_const_mul` and `induced_sum` give additivity, vanishing on $0$, homogeneity $\operatorname{Ind}_H^G(c\varphi) = c\,\operatorname{Ind}_H^G\varphi$, and commutation with finite sums indexed by a `Finset`. `induced_mul_of_conj_invariant` is the projection formula: for $f \colon G \to K$ invariant under conjugation, $\operatorname{Ind}_H^G(\varphi)(g)\,f(g) = \operatorname{Ind}_H^G(\varphi \cdot f)(g)$. `induced_top_of_conj_invariant` states that over a field of characteristic zero, induction from $H = \top$ returns a conjugation-invariant $\varphi$ unchanged. `induced_induced` is transitivity, over a field of characteristic zero: for $L \le H$ and $\psi \colon H \to K$, inducing from $H$ the extension by zero of $\operatorname{Ind}_L^H\psi$ agrees with inducing, from the image $L$ under the inclusion $H \hookrightarrow G$, the extension by zero of $\psi$ (extension by zero being taken by cases on membership in $H$).
--
--   **Relation to Mathlib.** Mathlib has no operator of this kind on $K$-valued functions on a finite group; [`ClassFunction.induced`](../def/ClassFunction_Induced.html#L13) is the project's own, and is defined on plain functions $G \to K$ rather than on a type of class functions.
--
--   **Where it is used.** These are the formal properties of induction of $K$-valued class functions on finite groups on which induction theorems for characters rest, and the module is used by several of the representation-theoretic developments in the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ClassFunction_Induced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ClassFunction

variable {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]

open scoped Classical in

def induced (H : Subgroup G) (φ : G → K) : G → K :=
  fun g => (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0

theorem induced_apply (H : Subgroup G) [DecidablePred (· ∈ H)] (φ : G → K) (g : G) :
    induced H φ g =
      (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0 := by
  unfold induced
  congr 1
  exact Finset.sum_congr rfl fun x _ => by congr

theorem induced_congr (H : Subgroup G) {φ ψ : G → K} (h : ∀ x ∈ H, φ x = ψ x) :
    induced H φ = induced H ψ := by
  classical
  funext g
  rw [induced_apply, induced_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · exact h _ hx
  · rfl

theorem induced_conj (H : Subgroup G) (φ : G → K) (y g : G) :
    induced H φ (y⁻¹ * g * y) = induced H φ g := by
  classical
  rw [induced_apply, induced_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
  have : x⁻¹ * (y⁻¹ * g * y) * x = (y * x)⁻¹ * g * (y * x) := by group
  simp only [Equiv.coe_mulLeft, this]

theorem induced_add (H : Subgroup G) (φ ψ : G → K) :
    induced H (φ + ψ) = induced H φ + induced H ψ := by
  classical
  funext g
  simp only [Pi.add_apply, induced_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem induced_zero (H : Subgroup G) : induced H (0 : G → K) = 0 := by
  classical
  funext g
  rw [induced_apply, Pi.zero_apply]
  simp only [Pi.zero_apply, ite_self, Finset.sum_const_zero, mul_zero]

theorem induced_const_mul (H : Subgroup G) (c : K) (φ : G → K) :
    induced H (fun x => c * φ x) = fun g => c * induced H φ g := by
  classical
  funext g
  simp only [induced_apply]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem induced_sum {ι : Type*} (H : Subgroup G) (s : Finset ι) (φ : ι → G → K) :
    induced H (fun x => ∑ i ∈ s, φ i x) = fun g => ∑ i ∈ s, induced H (φ i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact induced_zero H
  | insert i s hi ih =>
    funext g
    simp only [Finset.sum_insert hi]
    have : (fun x => φ i x + ∑ j ∈ s, φ j x) = φ i + fun x => ∑ j ∈ s, φ j x := by
      funext x; simp
    rw [this, induced_add, Pi.add_apply, ih]

theorem induced_mul_of_conj_invariant (H : Subgroup G) (φ f : G → K)
    (hf : ∀ x g : G, f (x⁻¹ * g * x) = f g) (g : G) :
    induced H φ g * f g = induced H (fun y => φ y * f y) g := by
  classical
  simp only [induced_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [hf]
  · simp

theorem induced_top_of_conj_invariant [CharZero K] (φ : G → K)
    (hφ : ∀ x g : G, φ (x⁻¹ * g * x) = φ g) : induced (⊤ : Subgroup G) φ = φ := by
  classical
  funext g
  rw [induced_apply, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp only [Subgroup.mem_top, if_true, hφ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← mul_assoc]
  have hG : (Fintype.card G : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hG, one_mul]

theorem induced_induced [CharZero K] (H : Subgroup G) [Fintype H] [DecidablePred (· ∈ H)]
    (L : Subgroup H) (ψ : H → K) :
    induced H (fun g => if hg : g ∈ H then induced L ψ ⟨g, hg⟩ else 0) =
      induced (L.map H.subtype) (fun g => if hg : g ∈ H then ψ ⟨g, hg⟩ else 0) := by
  classical
  funext g
  rw [induced_apply, induced_apply]

  set ψ' : G → K := fun g => if hg : g ∈ H then ψ ⟨g, hg⟩ else 0 with hψ'
  set L' : Subgroup G := L.map H.subtype with hL'
  have hLcard : (Nat.card L' : K) = Nat.card L := by
    congr 1
    exact Nat.card_congr (L.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm
  have hmemL : ∀ y : G, y ∈ L' ↔ ∃ hy : y ∈ H, (⟨y, hy⟩ : H) ∈ L := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, by simpa using hz⟩
    · rintro ⟨hy, hL⟩
      exact ⟨⟨y, hy⟩, hL, rfl⟩
  have hL'H : L' ≤ H := by
    intro y hy
    rw [hmemL] at hy
    exact hy.1

  set F : G → K := fun z => if z⁻¹ * g * z ∈ L' then ψ' (z⁻¹ * g * z) else 0 with hF
  have hH0 : (Nat.card H : K) ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne'

  have hinner : ∀ x : G,
      (if x⁻¹ * g * x ∈ H then
        (if hx : x⁻¹ * g * x ∈ H then induced L ψ ⟨x⁻¹ * g * x, hx⟩ else 0) else 0) =
      (Nat.card L : K)⁻¹ * ∑ y : G, if y ∈ H then F (x * y) else 0 := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [if_pos hx, dif_pos hx, induced_apply]
      congr 1
      have key : ∀ y : H, (if y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y ∈ L then
          ψ (y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y) else 0) = F (x * y) := by
        intro y
        have hcoe : (x * y)⁻¹ * g * (x * y) = ((y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y : H) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        have hmemL' : ∀ w : H, (w : G) ∈ L' ↔ w ∈ L := by
          intro w
          rw [hmemL]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨w.2, h⟩⟩
        rw [hF]
        dsimp only
        rw [hcoe, hmemL']
        split_ifs with hw
        · rw [hψ']
          beta_reduce
          split_ifs with h'
          · rfl
          · exact absurd (Subtype.coe_prop _) h'
        · rfl
      rw [Finset.sum_congr rfl (fun y _ => key y)]

      rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (by simp) (fun y => F (x * y)),
        Finset.sum_filter]
    · rw [if_neg hx]
      symm
      rw [mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right_iff]
      intro hy
      rw [hF]
      dsimp only
      rw [if_neg]
      intro hyL
      apply hx
      have hmem : (x * y)⁻¹ * g * (x * y) ∈ H := hL'H hyL
      have : x⁻¹ * g * x = y * ((x * y)⁻¹ * g * (x * y)) * y⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem hy hmem) (H.inv_mem hy)

  have hswap : ∑ x : G, (Nat.card L : K)⁻¹ * ∑ y : G, (if y ∈ H then F (x * y) else 0) =
      (Nat.card L : K)⁻¹ * ((Nat.card H : K) * ∑ z : G, F z) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    have : ∀ y : G, ∑ x : G, (if y ∈ H then F (x * y) else 0) =
        if y ∈ H then ∑ z : G, F z else 0 := by
      intro y
      split_ifs with hy
      · exact Fintype.sum_equiv (Equiv.mulRight y) _ _ fun x => rfl
      · simp
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
      rw [← Fintype.card_subtype]
      convert (Nat.card_eq_fintype_card (α := H)).symm
    exact_mod_cast this
  have hL0 : (Nat.card L : K) ≠ 0 := by
    have : 0 < Nat.card L := Nat.card_pos
    exact_mod_cast this.ne'
  simp_rw [hinner]
  rw [hswap, hLcard]
  field_simp

end ClassFunction

end


