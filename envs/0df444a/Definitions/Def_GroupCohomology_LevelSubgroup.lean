-- Prove2me | Definitions.Def_GroupCohomology_LevelSubgroup
-- name    : GroupCohomology_LevelSubgroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/bc7b1b23-b575-5f26-8795-242f08b5ef49
-- title:
--   Level subgroups as preimages of Galois fixing subgroups
-- statement:
--   Fix a group $G$ together with a homomorphism $r \colon G \to (\overline{\mathbb Q} \simeq_{\mathrm{alg}[\mathbb Q]} \overline{\mathbb Q})$ into the group of $\mathbb Q$-algebra automorphisms of a chosen algebraic closure of $\mathbb Q$, and let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$. The object studied throughout is the subgroup $r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F)) \le G$, written in Lean as the `Subgroup.comap` of Mathlib's `IntermediateField.fixingSubgroup` of $F$ along $r$; it is the set of $g \in G$ whose image $r(g)$ fixes $F$ pointwise.
--
--   Four facts about this subgroup are recorded. First, `comap_fixingSubgroup_eq_ker`: if $F$ is normal over $\mathbb Q$, then $r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F))$ is exactly the kernel of the composite of $r$ with the restriction homomorphism $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) \to \mathrm{Aut}_{\mathbb Q}(F)$ given by `AlgEquiv.restrictNormalHom`, i.e. the kernel of $G \to \mathrm{Gal}(F/\mathbb Q)$. Second and third, two consequences of this identification are registered as typeclass instances, so that they are available automatically wherever the subgroup occurs: for $F$ normal over $\mathbb Q$ the subgroup is normal in $G$ (`normal_comap_fixingSubgroup`), and for $F$ in addition finite-dimensional over $\mathbb Q$ it has finite index (`finiteIndex_comap_fixingSubgroup`), the quotient embedding into the finite group $\mathrm{Gal}(F/\mathbb Q)$. Fourth, `comap_fixingSubgroup_antitone` records the order reversal in $F$: if $F \le F'$ then $r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F')) \le r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F))$, so the subgroups shrink as the field grows. No topology on $G$ or on the Galois group enters; the fixing subgroups are taken as abstract subgroups and $r$ as an abstract homomorphism.
--
--   **Relation to Mathlib.** All the ingredients — `IntermediateField.fixingSubgroup`, `Subgroup.comap`, `AlgEquiv.restrictNormalHom` and the description of its kernel — are Mathlib's; what is added here is the identification of the pullback with a kernel for an arbitrary homomorphism $r$ into $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, and the registration of normality and finiteness of index as instances so that they are found by typeclass inference.
--
--   **Where it is used.** These subgroups are the level subgroups $U_F \le G$ attached to a Galois representation or Galois action $r$ of $G$; the instances make statements about the finite quotients $G/U_F$, about invariants $M^{U_F}$ and about inflation maps into continuous cohomology elaborate without extra hypotheses, for any level map $r$ (the absolute Galois group itself, its subgroups, or decomposition groups at primes). They are used pervasively in the group-cohomological part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_LevelSubgroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace groupCohomology

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

theorem comap_fixingSubgroup_eq_ker (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    F.fixingSubgroup.comap r
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›,
    MonoidHom.comap_ker]
  rfl

instance normal_comap_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup.comap r).Normal := by
  rw [comap_fixingSubgroup_eq_ker]; exact MonoidHom.normal_ker _

instance finiteIndex_comap_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ F] [Normal ℚ F] : (F.fixingSubgroup.comap r).FiniteIndex := by
  rw [comap_fixingSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

theorem comap_fixingSubgroup_antitone {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') :
    F'.fixingSubgroup.comap r ≤ F.fixingSubgroup.comap r :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

end groupCohomology


