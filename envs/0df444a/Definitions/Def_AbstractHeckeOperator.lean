-- Prove2me | Definitions.Def_AbstractHeckeOperator
-- name    : AbstractHeckeOperator
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f8568ed8-1d2d-5cbb-8afd-c84313042483
-- title:
--   Abstract double-coset Hecke operators on fixed points
-- statement:
--   Fix a group $G$ acting on an additive commutative monoid $A$ by a distributive action, subgroups $U, V \le G$ and an element $g \in G$. The module first equips Mathlib's set of fixed points `fixedPoints V A` with algebraic structure: it is an additive commutative monoid (as the fixed-point additive submonoid), and for a scalar type $R$ acting on $A$ commutingly with $G$ it carries the induced scalar multiplication, giving a `MulAction` and, when $R$ is a ring acting on $A$ by a module structure, a `Module` structure; `coe_zero`, `coe_add`, `coe_smul` record that the coercion to $A$ preserves these operations. The main definition is the double-coset operator. Under the hypothesis `h` that the image of the set $U \cdot \{g\} = Ug$ under the projection $G \to G/V$ is finite — equivalently, that $UgV$ is a finite union of left cosets $g_i V$ — `HeckeOperator_toFun` sends $a \in A^V$ to $\sum_i g_i \cdot a$, where the $g_i$ are the canonical `Quotient.out` representatives of the cosets in the image of $Ug$ in $G/V$ and the sum is an unconditional `finsum` over that set. Two points are worth noting: the representatives are not a chosen decomposition but the canonical section of the quotient, and the proof that the value lies in $A^U$ proceeds by the auxiliary results [`Set.bijOn_smul`](../def/AbstractHeckeOperator.html#L70) (left translation by $u \in U$ is a bijection of $U \cdot X$ onto itself) and `eq_finsum_quotient_out_of_bijOn'` (for $a$ fixed by $V$, the sum of $g \cdot a$ over any set of representatives bijecting onto a subset of $G/V$ agrees with the sum over the canonical representatives). The operator is then packaged as an additive homomorphism `HeckeOperator_addMonoidHom` and, for $R$ a ring acting commutingly, as an $R$-linear map `HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A`; `HeckeOperator_apply` states its defining formula on underlying elements.
--
--   **Relation to Mathlib.** Mathlib supplies the fixed-point set `MulAction.fixedPoints` and its additive submonoid; the additive monoid, scalar, `MulAction` and `Module` instances on it are added here. Mathlib has no general double-coset Hecke operator, so `HeckeOperator` is the project's own.
--
--   **Where it is used.** This is the general double-coset formalism $[UgV] \colon A^V \to A^U$ from which the Hecke action on spaces of automorphic forms is obtained: taking $G$ to be the adelic points of a totally definite quaternion algebra and $U, V$ open compact subgroups gives the Brandt-matrix action on weight-two quaternionic automorphic forms, and in the $\mathrm{GL}_2$ setting the classical operators $T_p$ and $U_p$.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AbstractHeckeOperator.lean

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.GroupAction.Quotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace FixedPoints

open MulAction

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G}

instance : AddCommMonoid (fixedPoints G A) :=
  AddSubmonoid.toAddCommMonoid (FixedPoints.addSubmonoid G A)

@[simp, norm_cast]
lemma coe_zero : ((0 : fixedPoints G A) : A) = 0 := rfl

@[simp, norm_cast]
lemma coe_add (a b : fixedPoints G A) :
    ((a + b : fixedPoints G A) : A) = a + b := rfl

variable {R : Type*}

instance [SMul R A] [SMulCommClass G R A] :
    SMul R (fixedPoints G A) where
  smul r a := ⟨r • a.1, fun g ↦ by rw [smul_comm, a.2]⟩

@[simp, norm_cast]
lemma coe_smul [SMul R A] [SMulCommClass G R A] (r : R) (a : fixedPoints G A) :
    ((r • a : fixedPoints G A) : A) = r • a := rfl

instance [Monoid R] [MulAction R A] [SMulCommClass G R A] :
    MulAction R (fixedPoints G A) where
  one_smul a := by
    ext
    push_cast
    simp
  mul_smul r s a := by
    ext
    push_cast
    simp [mul_smul]

instance module [Ring R] [Module R A] [SMulCommClass G R A] : Module R (fixedPoints G A) where
  one_smul a := one_smul _ _
  mul_smul r s a := mul_smul _ _ _
  smul_zero a := by
    ext
    exact smul_zero _
  smul_add r s a := by
    ext
    exact smul_add _ _ _
  add_smul r s a := by
    ext
    exact add_smul _ _ _
  zero_smul a := by
    ext
    exact zero_smul _ _

end FixedPoints

open scoped Pointwise

variable (G : Type*) [Group G] (U : Subgroup G) (X : Set G) {u : G} in
lemma Set.bijOn_smul (hu : u ∈ U) : Set.BijOn (fun x ↦ u • x) ((U : Set G) * X) (U * X) := by
  refine ⟨?_, Set.injOn_of_injective (MulAction.injective u), ?_⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨u * u', mul_mem hu hu', x, hx, by simp [mul_assoc]⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨(u⁻¹ * u') * x, ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', x, hx, rfl⟩, by simp [mul_assoc]⟩

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G} {U V : Subgroup G}

open MulAction

variable (h : (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite)

open ConjAct

namespace AbstractHeckeOperator

lemma eq_finsum_quotient_out_of_bijOn' (a : fixedPoints V A)
    {X : Set (G ⧸ V)}
    {s : Set G} (hs : s.BijOn (QuotientGroup.mk : G → G ⧸ V) X) :
    ∑ᶠ g ∈ s, g • (a : A) = ∑ᶠ g ∈ Quotient.out '' X, g • (a : A) := by
  let e (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ V)
  have he₀ : Set.BijOn e s (Quotient.out '' X) := by
    refine Set.BijOn.comp ?_ hs
    exact Set.InjOn.bijOn_image <| Set.injOn_of_injective Quotient.out_injective
  have he₁ : ∀ g ∈ s, g • (a : A) = (Quotient.out (QuotientGroup.mk g : G ⧸ V)) • a := by
    intro g hgs
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    rw [hv, mul_smul, (show (v : G) • (a : A) = a from a.2 v)]
  exact finsum_mem_eq_of_bijOn e he₀ he₁

noncomputable def HeckeOperator_toFun (a : fixedPoints V A) : fixedPoints U A :=
  ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)), gᵢ • a.1, by
  rintro ⟨u, huU⟩
  rw [smul_finsum_mem (h.image Quotient.out), ← eq_finsum_quotient_out_of_bijOn' a]
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · apply (Set.bijOn_comp_iff (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      apply Set.bijOn_smul _ _ _ huU
    · refine Set.InjOn.image_of_comp ?_
      simp only [Function.comp_def, Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

noncomputable def HeckeOperator_addMonoidHom : fixedPoints V A →+ fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_zero' := by
    ext
    simp [HeckeOperator_toFun]
  map_add' a b := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_add, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]

variable {R : Type*} [Ring R] [Module R A] [SMulCommClass G R A]

variable (g U V) in

noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_add' a b := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_add, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]
  map_smul' r a := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_smul, smul_comm,
      smul_finsum_mem (h.image Quotient.out), RingHom.id_apply]

lemma HeckeOperator_apply (a : fixedPoints V A) :
    (HeckeOperator (R := R) g U V h a : A) =
    ∑ᶠ (gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V))), gᵢ • (a : A) :=
  rfl

end AbstractHeckeOperator


