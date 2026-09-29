-- Prove2me | Definitions.Def_SchurMultiplierTrivial
-- name    : SchurMultiplierTrivial
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/4289ab82-59c3-5382-915c-eeae5a6e74b6
-- title:
--   Trivial Schur multiplier via stem extensions
-- statement:
--   The module introduces, in the `Ihara` namespace, a predicate expressing that a group has no non-trivial central stem extension. For a type $G$ with a group structure, [`Ihara.HasTrivialSchurMultiplier G`](../def/SchurMultiplierTrivial.html#L11) asserts: for every group $E$ in the same universe as $G$ and every homomorphism $\pi \colon E \to G$ that is surjective and whose kernel is contained both in the centre of $E$ and in the commutator subgroup $[E,E]$, the kernel of $\pi$ is trivial. Thus the predicate is a statement about all surjections onto $G$ in one fixed universe, quantified over group structures on types of that universe, and it encodes the vanishing of the Schur multiplier in the form "every stem extension of $G$ splits as the identity", rather than through any homological object; no second homology group is constructed here.
--
--   Three lemmas accompany the definition. [`Ihara.HasTrivialSchurMultiplier.of_mulEquiv`](../def/SchurMultiplierTrivial.html#L16) transports the predicate backwards along a group isomorphism: if $H$ satisfies it and $e \colon G \simeq^* H$ is an isomorphism, then $G$ satisfies it; the point is that composing a surjection onto $G$ with $e$ leaves the kernel, and the surjectivity, unchanged. [`Ihara.hasTrivialSchurMultiplier_of_isCyclic`](../def/SchurMultiplierTrivial.html#L29) proves the predicate for every cyclic group $G$: given $\pi$ as above with $\ker \pi$ central, the quotient $E/\ker\pi \cong G$ being cyclic forces $E$ to be abelian (Mathlib's `commutative_of_cyclic_center_quotient`), so $[E,E]$ is trivial and the hypothesis $\ker \pi \le [E,E]$ gives $\ker \pi = 1$. [`Ihara.hasTrivialSchurMultiplier_of_subsingleton`](../def/SchurMultiplierTrivial.html#L41) records the case of a group with at most one element, as an instance of the cyclic case.
--
--   **Relation to Mathlib.** Mathlib supplies the group-theoretic ingredients used (the `commutator` subgroup, `Subgroup.center`, and `commutative_of_cyclic_center_quotient`), but the predicate itself is the project's own: it is a stem-extension formulation, not a Mathlib notion of Schur multiplier or of second group homology.
--
--   **Where it is used.** The predicate is the interface in which the Schur-multiplier input about the groups $\mathrm{SL}_2(\mathbb{Z}/q^n)$ is stated and consumed elsewhere in the development; the cyclic and trivial cases proved here serve as base cases and as reductions along isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_SchurMultiplierTrivial.lean

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped commutatorElement

namespace Ihara

universe u

def HasTrivialSchurMultiplier (G : Type u) [Group G] : Prop :=
  ∀ (E : Type u) [Group E] (π : E →* G), Function.Surjective π →
    MonoidHom.ker π ≤ Subgroup.center E → MonoidHom.ker π ≤ commutator E →
      MonoidHom.ker π = ⊥

theorem HasTrivialSchurMultiplier.of_mulEquiv {G H : Type u} [Group G] [Group H]
    (hH : HasTrivialSchurMultiplier H) (e : G ≃* H) : HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hker : MonoidHom.ker (e.toMonoidHom.comp π) = MonoidHom.ker π := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hsurj' : Function.Surjective (e.toMonoidHom.comp π) := by
    rw [MonoidHom.coe_comp]; exact e.surjective.comp hsurj
  have h := hH E (e.toMonoidHom.comp π) hsurj'
    (by rw [hker]; exact hcent) (by rw [hker]; exact hcomm)
  rw [← hker]; exact h

theorem hasTrivialSchurMultiplier_of_isCyclic {G : Type u} [Group G] [IsCyclic G] :
    HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hcommutative : ∀ a b : E, a * b = b * a :=
    commutative_of_cyclic_center_quotient π hcent
  have hbot : commutator E = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcommutative g₁ g₂
  rw [eq_bot_iff]; exact hcomm.trans hbot.le

theorem hasTrivialSchurMultiplier_of_subsingleton {G : Type u} [Group G] [Subsingleton G] :
    HasTrivialSchurMultiplier G :=
  hasTrivialSchurMultiplier_of_isCyclic

end Ihara


