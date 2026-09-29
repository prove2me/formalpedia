-- Prove2me | Definitions.Def_GroupCohomology_LevelQuotient
-- name    : GroupCohomology_LevelQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/99ccc2af-742d-5277-8e32-b4f23288a950
-- title:
--   Level restriction to finite Galois layers of Q​
-- statement:
--   Throughout, $G$ is a group, $r \colon G \to \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ is a homomorphism into the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, and $F$ is an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ that is normal over $\mathbb Q$. The level subgroup attached to $F$ is the preimage $r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F))$, written as the comap along $r$ of `F.fixingSubgroup`.
--
--   The first definition, `levelRestrict r F`, is the homomorphism $G \to \mathrm{Aut}_{\mathbb Q}(F)$ obtained by composing $r$ with Mathlib's restriction map $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) \to \mathrm{Aut}_{\mathbb Q}(F)$ for the normal subextension $F$; the accompanying lemma records that, for $g \in G$ and $x \in F$, the value $\mathrm{levelRestrict}(g)(x)$ has the same image in $\overline{\mathbb Q}$ as $r(g)(x)$, and a second lemma identifies its kernel with the level subgroup $r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F))$. Consequently `levelQuotientHom r F` is defined as the induced homomorphism $G/r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F)) \to \mathrm{Aut}_{\mathbb Q}(F)$ on the quotient group, sending the class of $g$ to $r(g)|_F$, and it is shown to be injective.
--
--   For $G = \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ and $r$ the identity, `levelQuotientEquiv F` is the resulting group isomorphism
--   $$\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})\big/\mathrm{Gal}(\overline{\mathbb Q}/F) \;\xrightarrow{\sim}\; \mathrm{Aut}_{\mathbb Q}(F),$$
--   bijectivity coming from the injectivity above together with surjectivity of restriction, i.e. extension of automorphisms of $F$ to $\overline{\mathbb Q}$; two simp lemmas describe it on classes $\sigma \bmod \mathrm{Gal}(\overline{\mathbb Q}/F)$ and on elements $x \in F$. Finally, for a commutative ring $k$ and a representation $A$ of $\mathrm{Aut}_{\mathbb Q}(F)$ over $k$, [`Rep.ofLevel F A`](../def/GroupCohomology_LevelQuotient.html#L59) is the representation of the quotient group obtained by restricting $A$ along this isomorphism. A scoped instance provides `IsAlgClosure ℚ (AlgebraicClosure ℚ)` for the rational algebra structure used here.
--
--   **Relation to Mathlib.** The constructions are assembled from Mathlib: `AlgEquiv.restrictNormalHom` and its surjectivity, `IntermediateField.fixingSubgroup`, `QuotientGroup.lift`, and `Rep.res`. `levelQuotientEquiv` is the instance, for $\overline{\mathbb Q}/\mathbb Q$ and a normal subextension $F$, of the standard identification of $\mathrm{Gal}(F/\mathbb Q)$ with a quotient of the absolute Galois group, packaged as a `MulEquiv` for use with representations.
--
--   **Where it is used.** These definitions let a Galois representation of a group $G$ (in particular of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ itself) be pushed down to the finite Galois layer $\mathrm{Gal}(F/\mathbb Q)$, and conversely let a representation of $\mathrm{Gal}(F/\mathbb Q)$ be read as a representation of the quotient $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)/\mathrm{Gal}(\overline{\mathbb Q}/F)$, which is the shape required by the group-cohomology machinery used elsewhere in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_LevelQuotient.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_FieldTheory_RatAlgClosureGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace groupCohomology

scoped instance isAlgClosure_rat_algebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

abbrev levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] : G →* (F ≃ₐ[ℚ] F) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r

lemma levelRestrict_apply_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (g : G) (x : F) :
    (levelRestrict r F g x : AlgebraicClosure ℚ) = r g x :=
  AlgEquiv.restrictNormal_commutes (r g) F x

lemma ker_levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (levelRestrict r F).ker = F.fixingSubgroup.comap r :=
  (comap_fixingSubgroup_eq_ker r F).symm

def levelQuotientHom (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    G ⧸ F.fixingSubgroup.comap r →* (F ≃ₐ[ℚ] F) :=
  QuotientGroup.lift _ (levelRestrict r F) (by rw [← ker_levelRestrict])

@[simp] lemma levelQuotientHom_mk (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (g : G) :
    levelQuotientHom r F (QuotientGroup.mk g) = levelRestrict r F g := rfl

lemma levelQuotientHom_injective (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    Function.Injective (levelQuotientHom r F) := by
  rw [← MonoidHom.ker_eq_bot_iff, levelQuotientHom, QuotientGroup.ker_lift, ker_levelRestrict, QuotientGroup.map_mk'_self]

def levelQuotientEquiv (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup.comap (MonoidHom.id _) ≃* (F ≃ₐ[ℚ] F) :=
  MulEquiv.ofBijective (levelQuotientHom (MonoidHom.id _) F)
    ⟨levelQuotientHom_injective (MonoidHom.id _) F, fun σ => by
      obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) (AlgebraicClosure ℚ) σ
      exact ⟨QuotientGroup.mk g, rfl⟩⟩

@[simp] lemma levelQuotientEquiv_mk (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    levelQuotientEquiv F (QuotientGroup.mk g) = AlgEquiv.restrictNormalHom F g := rfl

lemma levelQuotientEquiv_apply_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F) :
    (levelQuotientEquiv F (QuotientGroup.mk g) x : AlgebraicClosure ℚ) = g x :=
  AlgEquiv.restrictNormal_commutes g F x

end groupCohomology

namespace Rep

open scoped groupCohomology

abbrev ofLevel {k : Type} [CommRing k] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (A : Rep k (F ≃ₐ[ℚ] F)) :
    Rep k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup.comap (MonoidHom.id _)) :=
  Rep.res (groupCohomology.levelQuotientEquiv F).toMonoidHom A

end Rep

end


