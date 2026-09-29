-- Prove2me | Definitions.Def_LocalRing_PrincipalUnits
-- name    : LocalRing_PrincipalUnits
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/da8c2ac8-f710-5304-bdae-a04bd2751011
-- title:
--   The principal units filtration of a local ring
-- statement:
--   For a commutative local ring $R$ with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R` and a natural number $k$, [`IsLocalRing.principalUnits R k`](../def/LocalRing_PrincipalUnits.html#L7) is the subgroup of the unit group $R^\times$ consisting of those $u$ with $u - 1 \in \mathfrak m^{k}$, i.e. the units congruent to $1$ modulo $\mathfrak m^{k}$. The carrier is exactly that set, and the subgroup axioms are the usual identities: $uv - 1 = (u-1)v + (v-1)$ shows closure under multiplication, and $u^{-1} - 1 = -u^{-1}(u-1)$ closure under inversion, both using that $\mathfrak m^{k}$ is an ideal.
--
--   Three small companions record the basic properties. [`IsLocalRing.mem_principalUnits_iff`](../def/LocalRing_PrincipalUnits.html#L25) states the membership criterion $u \in \mathrm{principalUnits}\,R\,k \iff (u : R) - 1 \in \mathfrak m^{k}$, which holds by definition and is the form in which membership is normally used. [`IsLocalRing.principalUnits_zero`](../def/LocalRing_PrincipalUnits.html#L28) says that at level $k = 0$ one gets the whole unit group, since $\mathfrak m^{0}$ is the unit ideal. [`IsLocalRing.principalUnits_antitone`](../def/LocalRing_PrincipalUnits.html#L31) says that $k \mapsto \mathrm{principalUnits}\,R\,k$ is antitone: for $k \le l$ the inclusion $\mathfrak m^{l} \subseteq \mathfrak m^{k}$ gives $\mathrm{principalUnits}\,R\,l \le \mathrm{principalUnits}\,R\,k$. Together these present the descending filtration
--   $$R^\times = U^{(0)} \supseteq U^{(1)} \supseteq U^{(2)} \supseteq \cdots$$
--   of the unit group by principal units. The definition is made for an arbitrary commutative local ring, with no completeness, noetherian or discrete-valuation hypothesis, and carries no structure theorem: it is purely the filtered family of subgroups.
--
--   **Relation to Mathlib.** Mathlib's `ValuationSubring.principalUnitGroup` is a different notion (a subgroup of $K^\times$ attached to a valuation subring of a field, at level one only); the filtration by congruence modulo powers of the maximal ideal of a commutative local ring is defined here, in the `IsLocalRing` namespace, using Mathlib's `IsLocalRing.maximalIdeal`.
--
--   **Where it is used.** The filtration is the common language for the local unit groups occurring throughout the argument — over $\mathbb{Z}_p$, over valuation rings of finite extensions of $\mathbb{Q}_p$, and over completions of rings of integers of number fields — where congruence conditions on units modulo powers of the maximal ideal govern local deformation and level structure data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalRing_PrincipalUnits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsLocalRing

def principalUnits (R : Type*) [CommRing R] [IsLocalRing R] (k : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ maximalIdeal R ^ k}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have h : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      push_cast; ring
    rw [Set.mem_setOf_eq, h]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hu) hv
  inv_mem' := by
    intro u hu
    have h : ((u⁻¹ : Rˣ) : R) - 1 = -(((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [Set.mem_setOf_eq, h]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hu)

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem mem_principalUnits_iff {k : ℕ} {u : Rˣ} :
    u ∈ principalUnits R k ↔ (u : R) - 1 ∈ maximalIdeal R ^ k := Iff.rfl

@[simp] theorem principalUnits_zero : principalUnits R 0 = ⊤ := by
  ext u; simp [mem_principalUnits_iff]

theorem principalUnits_antitone : Antitone (principalUnits R) :=
  fun _ _ hkl _ hu => Ideal.pow_le_pow_right hkl hu

end IsLocalRing


