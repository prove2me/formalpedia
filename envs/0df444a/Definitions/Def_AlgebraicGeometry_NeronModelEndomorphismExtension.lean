-- Prove2me | Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
-- name    : AlgebraicGeometry_NeronModelEndomorphismExtension
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/d84b8504-cd83-5f1f-92ac-5b37c106a0b8
-- title:
--   Endomorphism extension under the Néron mapping property
-- statement:
--   Over a base $\operatorname{Spec} R$ with $R$ a commutative ring and $K$ an $R$-algebra which is a field, the project records for morphisms $g : Y \to \operatorname{Spec} R$, $f : X \to \operatorname{Spec} R$ the type `SchemeHomOver g f` of pairs consisting of $\varphi : Y \to X$ together with a proof that $\varphi$ followed by $f$ equals $g$, and the map `genericFibreRestrict` sending such a $\varphi$ to the induced morphism of the base changes along `specGenericFibreInclusion`, the map $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by $R \to K$. This module first equips these hom-types with an identity `schemeHomOverId` (the identity of $X$) and a composition `schemeHomOverComp` (the pair $(\varphi,\psi) \mapsto \psi \circ \varphi$ in diagrammatic order), proves associativity and the two unit laws, and shows that `genericFibreRestrict` carries identity to identity and composition to composition.
--
--   It then exploits the predicate `NeronUniqueExtension R K f` — bijectivity of `genericFibreRestrict` for every smooth test morphism $t : T \to \operatorname{Spec} R$ — and the structure `NeronModelPropertyBundle R K f`, whose fields assert that $f$ is smooth, separated, locally of finite type, quasi-compact and satisfies `NeronUniqueExtension`. From such a bundle one obtains: bijectivity of restriction on endomorphisms over the base, the corresponding unique-existence statement, its unpacked form for bare morphisms $v : X \to X$ with $v$ followed by $f$ equal to $f$, the bijection `integralPoints_bijective` for the test object $\operatorname{Spec} R$ itself, and the resulting equivalence `endExtensionEquiv` between endomorphisms of $f$ and endomorphisms of its generic fibre. Its inverse is shown to preserve the identity and composition, hence to transport commuting pairs and involutions, and (in the family layer) to extend an arbitrary indexed family of generic-fibre endomorphisms uniquely, compatibly with any composition relation among them. The closing lemmas instantiate all of this at the identity of $\operatorname{Spec} \mathbb{Z}_p$, where the bundle holds because the structure morphism is an isomorphism.
--
--   **Relation to Mathlib.** Mathlib has no notion of Néron model or Néron mapping property; `SchemeHomOver`, `genericFibreRestrict`, `NeronUniqueExtension` and `NeronModelPropertyBundle` are the project's own, built on Mathlib's scheme pullbacks and on its predicates `Smooth`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.
--
--   **Where it is used.** This layer supplies the formal mechanism by which endomorphisms defined on a generic fibre — in the intended application, Hecke correspondences on a modular curve or its Jacobian over $\mathbb{Q}$ — are extended uniquely to the integral model, together with the fact that such extensions respect identities, composition and the relations satisfied by a family of operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_NeronModelEndomorphismExtension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section HomOverBookkeeping

variable {B Y X W : Scheme.{u}}

def schemeHomOverId (f : X ⟶ B) : SchemeHomOver f f :=
  ⟨𝟙 X, Category.id_comp f⟩

@[simp]
theorem schemeHomOverId_coe (f : X ⟶ B) : (schemeHomOverId f).1 = 𝟙 X :=
  rfl

def schemeHomOverComp {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) : SchemeHomOver g e :=
  ⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩

@[simp]
theorem schemeHomOverComp_coe {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) :
    (schemeHomOverComp φ ψ).1 = φ.1 ≫ ψ.1 :=
  rfl

theorem schemeHomOverComp_assoc {V : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    {d : V ⟶ B} (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver e d) :
    schemeHomOverComp (schemeHomOverComp φ ψ) χ =
      schemeHomOverComp φ (schemeHomOverComp ψ χ) := by
  apply Subtype.ext
  simp

@[simp]
theorem schemeHomOverComp_id_left {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    schemeHomOverComp (schemeHomOverId g) φ = φ := by
  apply Subtype.ext
  simp

@[simp]
theorem schemeHomOverComp_id_right {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    schemeHomOverComp φ (schemeHomOverId f) = φ := by
  apply Subtype.ext
  simp

end HomOverBookkeeping

section RestrictFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem genericFibreRestrict_schemeHomOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K f f (schemeHomOverId f) =
      schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K)) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [genericFibreRestrict]
  · simp [genericFibreRestrict]

theorem genericFibreRestrict_schemeHomOverComp
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (e : Z ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) :
    genericFibreRestrict R K e g (schemeHomOverComp φ ψ) =
      schemeHomOverComp (genericFibreRestrict R K f g φ) (genericFibreRestrict R K e f ψ) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [genericFibreRestrict, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp [genericFibreRestrict, pullback.lift_snd]

theorem genericFibreRestrict_endComp (f : X ⟶ Spec (CommRingCat.of R))
    (φ ψ : SchemeHomOver f f) :
    genericFibreRestrict R K f f (schemeHomOverComp φ ψ) =
      schemeHomOverComp (genericFibreRestrict R K f f φ) (genericFibreRestrict R K f f ψ) :=
  genericFibreRestrict_schemeHomOverComp R K f f f φ ψ

end RestrictFunctoriality

section ExtensionEngines

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X Y : Scheme.{u}}

theorem neronHomRestrict_bijective_of_smooth {f : X ⟶ Spec (CommRingCat.of R)}
    (hf : NeronUniqueExtension R K f) {g : Y ⟶ Spec (CommRingCat.of R)} (hg : Smooth g) :
    Function.Bijective (genericFibreRestrict R K f g) :=
  hf Y g hg

theorem neronEndRestrict_bijective_of_smooth {f : X ⟶ Spec (CommRingCat.of R)}
    (hf : NeronUniqueExtension R K f) (hsm : Smooth f) :
    Function.Bijective (genericFibreRestrict R K f f) :=
  hf X f hsm

variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.homRestrict_bijective (h : NeronModelPropertyBundle R K f)
    {g : Y ⟶ Spec (CommRingCat.of R)} (hg : Smooth g) :
    Function.Bijective (genericFibreRestrict R K f g) :=
  h.neronMapping Y g hg

theorem NeronModelPropertyBundle.endRestrict_bijective (h : NeronModelPropertyBundle R K f) :
    Function.Bijective (genericFibreRestrict R K f f) :=
  h.neronMapping X f h.smooth

theorem NeronModelPropertyBundle.existsUnique_endExtension (h : NeronModelPropertyBundle R K f)
    (ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! φ : SchemeHomOver f f, genericFibreRestrict R K f f φ = ψ :=
  h.endRestrict_bijective.existsUnique ψ

theorem NeronModelPropertyBundle.exists_endExtension_hom (h : NeronModelPropertyBundle R K f)
    (u : pullback f (specGenericFibreInclusion R K) ⟶
      pullback f (specGenericFibreInclusion R K))
    (hu : u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f (specGenericFibreInclusion R K)) :
    ∃ (v : X ⟶ X) (hv : v ≫ f = f), (genericFibreRestrict R K f f ⟨v, hv⟩).1 = u := by
  obtain ⟨⟨v, hv⟩, hφ⟩ := h.endRestrict_bijective.surjective ⟨u, hu⟩
  exact ⟨v, hv, congrArg Subtype.val hφ⟩

theorem NeronModelPropertyBundle.endExtension_unique_hom (h : NeronModelPropertyBundle R K f)
    {v₁ v₂ : X ⟶ X} (hv₁ : v₁ ≫ f = f) (hv₂ : v₂ ≫ f = f)
    (huv : (genericFibreRestrict R K f f ⟨v₁, hv₁⟩).1 =
      (genericFibreRestrict R K f f ⟨v₂, hv₂⟩).1) :
    v₁ = v₂ :=
  congrArg Subtype.val (h.endRestrict_bijective.injective (Subtype.ext huv))

theorem NeronModelPropertyBundle.integralPoints_bijective (h : NeronModelPropertyBundle R K f) :
    Function.Bijective
      (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R)))) :=
  h.neronMapping (Spec (CommRingCat.of R)) (𝟙 (Spec (CommRingCat.of R))) inferInstance

end ExtensionEngines

section ExtensionEquiv

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

noncomputable def NeronModelPropertyBundle.endExtensionEquiv
    (h : NeronModelPropertyBundle R K f) :
    SchemeHomOver f f ≃
      SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
        (pullback.snd f (specGenericFibreInclusion R K)) :=
  Equiv.ofBijective (genericFibreRestrict R K f f) h.endRestrict_bijective

@[simp]
theorem NeronModelPropertyBundle.endExtensionEquiv_apply (h : NeronModelPropertyBundle R K f)
    (φ : SchemeHomOver f f) :
    h.endExtensionEquiv φ = genericFibreRestrict R K f f φ :=
  rfl

@[simp]
theorem NeronModelPropertyBundle.endExtensionEquiv_symm_restrict
    (h : NeronModelPropertyBundle R K f) (φ : SchemeHomOver f f) :
    h.endExtensionEquiv.symm (genericFibreRestrict R K f f φ) = φ := by
  rw [← h.endExtensionEquiv_apply φ]
  exact h.endExtensionEquiv.symm_apply_apply φ

@[simp]
theorem NeronModelPropertyBundle.restrict_endExtensionEquiv_symm
    (h : NeronModelPropertyBundle R K f)
    (ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    genericFibreRestrict R K f f (h.endExtensionEquiv.symm ψ) = ψ := by
  rw [← h.endExtensionEquiv_apply]
  exact h.endExtensionEquiv.apply_symm_apply ψ

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_id
    (h : NeronModelPropertyBundle R K f) :
    h.endExtensionEquiv.symm
        (schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      schemeHomOverId f := by
  apply h.endRestrict_bijective.injective
  rw [h.restrict_endExtensionEquiv_symm]
  exact (genericFibreRestrict_schemeHomOverId R K f).symm

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_comp
    (h : NeronModelPropertyBundle R K f)
    (ψ₁ ψ₂ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    h.endExtensionEquiv.symm (schemeHomOverComp ψ₁ ψ₂) =
      schemeHomOverComp (h.endExtensionEquiv.symm ψ₁) (h.endExtensionEquiv.symm ψ₂) := by
  apply h.endRestrict_bijective.injective
  rw [h.restrict_endExtensionEquiv_symm, genericFibreRestrict_endComp,
    h.restrict_endExtensionEquiv_symm, h.restrict_endExtensionEquiv_symm]

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_commute
    (h : NeronModelPropertyBundle R K f)
    {ψ₁ ψ₂ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hcomm : schemeHomOverComp ψ₁ ψ₂ = schemeHomOverComp ψ₂ ψ₁) :
    schemeHomOverComp (h.endExtensionEquiv.symm ψ₁) (h.endExtensionEquiv.symm ψ₂) =
      schemeHomOverComp (h.endExtensionEquiv.symm ψ₂) (h.endExtensionEquiv.symm ψ₁) := by
  rw [← h.endExtensionEquiv_symm_comp, ← h.endExtensionEquiv_symm_comp, hcomm]

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_involution
    (h : NeronModelPropertyBundle R K f)
    {ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hinv : schemeHomOverComp ψ ψ =
      schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K))) :
    schemeHomOverComp (h.endExtensionEquiv.symm ψ) (h.endExtensionEquiv.symm ψ) =
      schemeHomOverId f := by
  rw [← h.endExtensionEquiv_symm_comp, hinv, h.endExtensionEquiv_symm_id]

end ExtensionEquiv

section FamilyLayer

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.existsUnique_familyExtension
    (h : NeronModelPropertyBundle R K f) {J : Type*}
    (T : J → SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! S : J → SchemeHomOver f f, ∀ j, genericFibreRestrict R K f f (S j) = T j := by
  refine ⟨fun j => h.endExtensionEquiv.symm (T j),
    fun j => h.restrict_endExtensionEquiv_symm (T j), ?_⟩
  intro S' hS'
  funext j
  rw [← hS' j]
  exact (h.endExtensionEquiv_symm_restrict (S' j)).symm

theorem NeronModelPropertyBundle.familyExtension_relation
    (h : NeronModelPropertyBundle R K f) {J : Type*}
    (T : J → SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    {i j k : J} (hrel : schemeHomOverComp (T i) (T j) = T k) :
    schemeHomOverComp (h.endExtensionEquiv.symm (T i)) (h.endExtensionEquiv.symm (T j)) =
      h.endExtensionEquiv.symm (T k) := by
  rw [← hrel]
  exact (h.endExtensionEquiv_symm_comp (T i) (T j)).symm

end FamilyLayer

section SatGates

theorem gate_endRestrict_bijective_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (𝟙 (Spec (CommRingCat.of ℤ_[p])))) :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).endRestrict_bijective

theorem gate_endExtensionEquiv_symm_id_trivialGroupScheme_z3 :
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).endExtensionEquiv.symm
        (schemeHomOverId (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3])))
          (specGenericFibreInclusion ℤ_[3] ℚ_[3]))) =
      schemeHomOverId (𝟙 (Spec (CommRingCat.of ℤ_[3]))) :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_z3).endExtensionEquiv_symm_id

theorem gate_existsUnique_familyExtension_trivialGroupScheme_z3
    (T : ℕ → SchemeHomOver
      (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (specGenericFibreInclusion ℤ_[3] ℚ_[3]))
      (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (specGenericFibreInclusion ℤ_[3] ℚ_[3]))) :
    ∃! S : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
      ∀ j, genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (S j) = T j :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_z3).existsUnique_familyExtension T

end SatGates

end NeronModelInfra

/--
info: 'NeronModelInfra.genericFibreRestrict_schemeHomOverComp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_schemeHomOverComp

/--
info: 'NeronModelInfra.neronEndRestrict_bijective_of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronEndRestrict_bijective_of_smooth

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.endRestrict_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.endRestrict_bijective

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.existsUnique_endExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.existsUnique_endExtension

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_comp

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.existsUnique_familyExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.existsUnique_familyExtension

/--
info: 'NeronModelInfra.gate_endRestrict_bijective_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_endRestrict_bijective_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_endExtensionEquiv_symm_id_trivialGroupScheme_z3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_endExtensionEquiv_symm_id_trivialGroupScheme_z3


