-- Prove2me | Definitions.Def_ModularCurve_LevelOneComp
-- name    : ModularCurve_LevelOneComp
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/b8aaad1d-5e55-5198-87f6-b626d7d4bf16
-- title:
--   Level-one component map of the modular Jacobian
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbf Q}$ and a natural number $q$. The ambient group is $H =$ `inertiaInvariants A (1 * q)`, the subgroup of those classes in `JZero (1 * q)` (the degree-zero Picard group of the base change to $\overline{\mathbf Q}$ of the modular function field of level $1\cdot q$) which are fixed by every element of the inertia subgroup of $A$ over $\mathbf Q$; the level is written in the form $1 \cdot q$ so as to match the shape of the level-$N$ semistable specialisation datum at $N = 1$.
--
--   The first definition, `levelOneIdentityComponent A q`, is the subgroup $nH \subseteq H$, the image of multiplication by the natural number $n =$ `eisensteinNumerator q` $= (q-1)/\gcd(q-1,12)$ (natural-number division); `mem_levelOneIdentityComponent` records that membership means being of the form $n\cdot y$ with $y \in H$. The type `LevelOnePhi A q` is the quotient $H/nH$, equipped with its additive commutative group structure, and `LevelOnePhi.mk` is the projection $H \to H/nH$, which is surjective and whose kernel is described by `LevelOnePhi.mk_eq_zero_iff`: $\mathrm{mk}(x) = 0$ iff $x = n\cdot y$ for some $y \in H$.
--
--   Finally, for a finite index type $\iota$, a width function `width : ι → ℕ` and an additive isomorphism $\varphi \colon H/nH \xrightarrow{\sim}$ `componentGroup width` (the quotient of $\operatorname{Hom}_{\mathbf Z}(X,\mathbf Z)$ by the image of the Gram map of the width pairing on the degree-zero character lattice $X$), `levelOneComp A q φ` is the additive homomorphism $H \to$ `componentGroup width` given by $\varphi$ after the projection. The accompanying lemmas state its value on elements, that it vanishes exactly on $nH$, and that it is surjective. Thus the identification $\varphi$ enters as a parameter: no canonical component map is constructed, only the family of maps attached to each such $\varphi$.
--
--   **Relation to Mathlib.** The quotient group, its projection and the kernel criterion are Mathlib's `QuotientAddGroup` machinery; the objects quotiented — the inertia invariants of the modular Jacobian and the combinatorial component group of a width function — are the project's own, Mathlib having no notion of Néron model component groups.
--
--   **Where it is used.** At prime level $q$ the component group of the Néron model of $J_0(q)$ is killed by the Eisenstein numerator $n$, so that the subgroup of $n$-divisible elements is the identity component and the component map is the quotient by $nH$ followed by an isomorphism. These definitions package that description so that the level-one case of the semistable specialisation data can be fed into the level-lowering argument for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneComp.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring

section LevelOneComp

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ)

def levelOneIdentityComponent : AddSubgroup ↥(inertiaInvariants A (1 * q)) :=
  (nsmulAddMonoidHom (eisensteinNumerator q) :
    ↥(inertiaInvariants A (1 * q)) →+ ↥(inertiaInvariants A (1 * q))).range

theorem mem_levelOneIdentityComponent (x : ↥(inertiaInvariants A (1 * q))) :
    x ∈ levelOneIdentityComponent A q ↔
      ∃ y : ↥(inertiaInvariants A (1 * q)), eisensteinNumerator q • y = x := by
  simp [levelOneIdentityComponent, AddMonoidHom.mem_range]

def LevelOnePhi : Type := ↥(inertiaInvariants A (1 * q)) ⧸ levelOneIdentityComponent A q

set_option synthInstance.maxHeartbeats 400000 in
instance LevelOnePhi.instAddCommGroup : AddCommGroup (LevelOnePhi A q) :=
  QuotientAddGroup.Quotient.addCommGroup (levelOneIdentityComponent A q)

set_option synthInstance.maxHeartbeats 400000 in

def LevelOnePhi.mk : ↥(inertiaInvariants A (1 * q)) →+ LevelOnePhi A q :=
  QuotientAddGroup.mk' (levelOneIdentityComponent A q)

set_option synthInstance.maxHeartbeats 400000 in
theorem LevelOnePhi.mk_eq_zero_iff (x : ↥(inertiaInvariants A (1 * q))) :
    LevelOnePhi.mk A q x = 0 ↔ ∃ y : ↥(inertiaInvariants A (1 * q)), eisensteinNumerator q • y = x := by
  rw [← mem_levelOneIdentityComponent]
  exact QuotientAddGroup.eq_zero_iff x

theorem LevelOnePhi.mk_surjective : Function.Surjective (LevelOnePhi.mk A q) :=
  QuotientAddGroup.mk'_surjective _

def levelOneComp {ι : Type*} [Fintype ι] {width : ι → ℕ} (φ : LevelOnePhi A q ≃+ componentGroup width) :
    ↥(inertiaInvariants A (1 * q)) →+ componentGroup width :=
  φ.toAddMonoidHom.comp (LevelOnePhi.mk A q)

theorem levelOneComp_apply {ι : Type*} [Fintype ι] {width : ι → ℕ} (φ : LevelOnePhi A q ≃+ componentGroup width)
    (x : ↥(inertiaInvariants A (1 * q))) :
    levelOneComp A q φ x = φ (LevelOnePhi.mk A q x) := rfl

theorem levelOneComp_eq_zero_iff {ι : Type*} [Fintype ι] {width : ι → ℕ}
    (φ : LevelOnePhi A q ≃+ componentGroup width) (x : ↥(inertiaInvariants A (1 * q))) :
    levelOneComp A q φ x = 0 ↔ ∃ y : ↥(inertiaInvariants A (1 * q)), eisensteinNumerator q • y = x := by
  rw [levelOneComp_apply, AddEquiv.map_eq_zero_iff, LevelOnePhi.mk_eq_zero_iff]

theorem levelOneComp_surjective {ι : Type*} [Fintype ι] {width : ι → ℕ}
    (φ : LevelOnePhi A q ≃+ componentGroup width) : Function.Surjective (levelOneComp A q φ) :=
  φ.surjective.comp (LevelOnePhi.mk_surjective A q)

end LevelOneComp

end ModularCurve

end


