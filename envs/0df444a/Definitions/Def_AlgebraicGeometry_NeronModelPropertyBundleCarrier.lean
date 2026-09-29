-- Prove2me | Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
-- name    : AlgebraicGeometry_NeronModelPropertyBundleCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2f929eb3-2e0e-59d5-99d9-007387469f41
-- title:
--   Néron model property bundle over a Dedekind base
-- statement:
--   Over a commutative ring $R$ with a field $K$ and an $R$-algebra structure $R \to K$, `specGenericFibreInclusion` is the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the structure map. For schemes over a base, `SchemeHomOver g f` is the subtype of morphisms $\varphi : Y \to X$ with $\varphi$ followed by $f$ equal to $g$, i.e. the relative Hom-set of $B$-morphisms. For two morphisms $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$, `genericFibreRestrict` is the base-change map
--   $$\operatorname{Hom}_{\operatorname{Spec} R}(Y, X) \longrightarrow \operatorname{Hom}_{\operatorname{Spec} K}(Y \times_{\operatorname{Spec} R} \operatorname{Spec} K,\; X \times_{\operatorname{Spec} R} \operatorname{Spec} K),$$
--   the fibre products being Mathlib pullbacks along `specGenericFibreInclusion` and the structure morphisms to $\operatorname{Spec} K$ being the second projections; two simp lemmas record its compositions with the two projections, and a further lemma identifies it with `pullback.map` applied to $\varphi$ and identities. The predicate `NeronUniqueExtension R K f` asserts that for every scheme $T$ and every smooth $t : T \to \operatorname{Spec} R$ this restriction map is bijective — every $K$-morphism on generic fibres extends uniquely over $R$.
--
--   For $R$ a Dedekind domain with fraction field $K$, the `Prop`-valued structure `NeronModelPropertyBundle R K f` has five fields: $f$ is smooth, separated, locally of finite type, quasi-compact, and satisfies `NeronUniqueExtension`. It is thus a predicate on a morphism to $\operatorname{Spec} R$ and carries no group-scheme structure and no identification of the generic fibre with a prescribed $K$-scheme. Accessors restate the four Mathlib properties, an iff-lemma converts the bundle to the corresponding conjunction, and bijectivity is repackaged as unique existence of an extension. Further lemmas show that for $f$ an isomorphism the relative Hom-sets are subsingletons and nonempty, whence `genericFibreRestrict` is bijective and the bundle holds for $\mathbb{1}_{\operatorname{Spec} R}$, specialised to $R = \mathbb{Z}_p$, $K = \mathbb{Q}_p$ and to $p = 3$. In the opposite direction, $\operatorname{Spec}\mathbb{Q}_p \to \operatorname{Spec}\mathbb{Z}_p$ admits no section (a ring map $\mathbb{Q}_p \to \mathbb{Z}_p$ over $\mathbb{Z}_p$ would make $p$ a unit), so it satisfies neither `NeronUniqueExtension` nor the bundle.
--
--   **Relation to Mathlib.** `Smooth`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` for morphisms of schemes, and the pullbacks used, are Mathlib's; Mathlib has no Néron model notion, so `NeronUniqueExtension`, `SchemeHomOver`, `genericFibreRestrict` and `NeronModelPropertyBundle` are the project's own.
--
--   **Where it is used.** The module is an infrastructure leaf supplying the vocabulary in which the defining properties of a Néron model over a Dedekind base (in particular over $\mathbb{Z}_p$ with generic fibre over $\mathbb{Q}_p$) are stated in the rest of the development; the mathematics proved here consists of the two extreme cases, the identity on $\operatorname{Spec} R$ and the generic-fibre inclusion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

def specGenericFibreInclusion : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

@[simp]
theorem specGenericFibreInclusion_eq :
    specGenericFibreInclusion R K = Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  rfl

abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  {φ : Y ⟶ X // φ ≫ f = g}

variable {X Y : Scheme.{u}}

def genericFibreRestrict (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift (pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1)
      (pullback.snd g (specGenericFibreInclusion R K))
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩

def NeronUniqueExtension (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
    Function.Bijective (genericFibreRestrict R K f t)

theorem neronUniqueExtension_iff_bijective (f : X ⟶ Spec (CommRingCat.of R)) :
    NeronUniqueExtension R K f ↔
      ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
        Function.Bijective (genericFibreRestrict R K f t) :=
  Iff.rfl

structure NeronModelPropertyBundle [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop where

  smooth : Smooth f

  separated : IsSeparated f

  locallyOfFiniteType : LocallyOfFiniteType f

  quasiCompact : QuasiCompact f

  neronMapping : NeronUniqueExtension R K f

section ComparisonHooks

variable {R K}
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.smooth_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.Smooth f :=
  h.smooth

theorem NeronModelPropertyBundle.isSeparated_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.IsSeparated f :=
  h.separated

theorem NeronModelPropertyBundle.locallyOfFiniteType_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.LocallyOfFiniteType f :=
  h.locallyOfFiniteType

theorem NeronModelPropertyBundle.quasiCompact_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.QuasiCompact f :=
  h.quasiCompact

theorem NeronModelPropertyBundle.neronMapping_bijective
    (h : NeronModelPropertyBundle R K f) (T : Scheme.{u})
    (t : T ⟶ Spec (CommRingCat.of R)) (ht : Smooth t) :
    Function.Bijective (genericFibreRestrict R K f t) :=
  h.neronMapping T t ht

theorem neronModelPropertyBundle_iff_propertyList (f : X ⟶ Spec (CommRingCat.of R)) :
    NeronModelPropertyBundle R K f ↔
      (Smooth f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
        NeronUniqueExtension R K f) :=
  ⟨fun h => ⟨h.smooth, h.separated, h.locallyOfFiniteType, h.quasiCompact, h.neronMapping⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

theorem NeronModelPropertyBundle.existsUnique_extension
    (h : NeronModelPropertyBundle R K f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (ht : Smooth t)
    (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! φ : SchemeHomOver t f, genericFibreRestrict R K f t φ = v :=
  (h.neronMapping T t ht).existsUnique v

end ComparisonHooks

section RestrictHooks

variable {R K}
variable (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))

@[simp]
theorem genericFibreRestrict_coe_comp_snd (φ : SchemeHomOver g f) :
    (genericFibreRestrict R K f g φ).1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd g (specGenericFibreInclusion R K) :=
  (genericFibreRestrict R K f g φ).2

@[simp]
theorem genericFibreRestrict_coe_comp_fst (φ : SchemeHomOver g f) :
    (genericFibreRestrict R K f g φ).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1 :=
  pullback.lift_fst _ _ _

theorem genericFibreRestrict_coe_eq_pullbackMap (φ : SchemeHomOver g f)
    (eq₁ : g ≫ 𝟙 (Spec (CommRingCat.of R)) = φ.1 ≫ f)
    (eq₂ : specGenericFibreInclusion R K ≫ 𝟙 (Spec (CommRingCat.of R)) =
      𝟙 (Spec (CommRingCat.of K)) ≫ specGenericFibreInclusion R K) :
    (genericFibreRestrict R K f g φ).1 =
      pullback.map g (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
        φ.1 (𝟙 (Spec (CommRingCat.of K))) (𝟙 (Spec (CommRingCat.of R))) eq₁ eq₂ := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, pullback.map]
  · simp [genericFibreRestrict, pullback.map]

end RestrictHooks

section IsoEngines

theorem subsingleton_schemeHomOver_of_isIso {B Y' X' : Scheme.{u}} (g : Y' ⟶ B) (f : X' ⟶ B)
    [IsIso f] : Subsingleton (SchemeHomOver g f) := by
  constructor
  intro a b
  apply Subtype.ext
  have ha : a.1 = g ≫ inv f := by
    have h0 : a.1 = (a.1 ≫ f) ≫ inv f := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [a.2] at h0
    exact h0
  have hb : b.1 = g ≫ inv f := by
    have h0 : b.1 = (b.1 ≫ f) ≫ inv f := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [b.2] at h0
    exact h0
  rw [ha, hb]

theorem nonempty_schemeHomOver_of_isIso {B Y' X' : Scheme.{u}} (g : Y' ⟶ B) (f : X' ⟶ B)
    [IsIso f] : Nonempty (SchemeHomOver g f) :=
  ⟨⟨g ≫ inv f, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩

theorem genericFibreRestrict_bijective_of_isIso (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f]
    (g : Y ⟶ Spec (CommRingCat.of R)) :
    Function.Bijective (genericFibreRestrict R K f g) := by
  constructor
  · intro a b _
    exact (subsingleton_schemeHomOver_of_isIso g f).allEq a b
  · intro v
    obtain ⟨φ⟩ := nonempty_schemeHomOver_of_isIso g f
    exact ⟨φ, (subsingleton_schemeHomOver_of_isIso
      (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))).allEq _ v⟩

theorem neronUniqueExtension_of_isIso (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] :
    NeronUniqueExtension R K f :=
  fun _ t _ => genericFibreRestrict_bijective_of_isIso R K f t

theorem neronModelPropertyBundle_id [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K] :
    NeronModelPropertyBundle R K (𝟙 (Spec (CommRingCat.of R))) :=
  { smooth := inferInstance
    separated := inferInstance
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    neronMapping := neronUniqueExtension_of_isIso R K (𝟙 (Spec (CommRingCat.of R))) }

end IsoEngines

section SatGates

theorem gate_neronModelPropertyBundle_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime] :
    NeronModelPropertyBundle ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p]))) :=
  neronModelPropertyBundle_id ℤ_[p] ℚ_[p]

theorem gate_neronModelPropertyBundle_trivialGroupScheme_z3 :
    NeronModelPropertyBundle ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3]))) :=
  gate_neronModelPropertyBundle_trivialGroupScheme_zp 3

end SatGates

section TeethGate

theorem isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsEmpty (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[p])))
      (specGenericFibreInclusion ℤ_[p] ℚ_[p])) := by
  constructor
  rintro ⟨s, hs⟩
  obtain ⟨σ, rfl⟩ := Spec.map_surjective s
  rw [specGenericFibreInclusion_eq, ← Spec.map_comp, Spec.map_eq_id] at hs
  have h2 : σ.hom.comp (algebraMap ℤ_[p] ℚ_[p]) = RingHom.id ℤ_[p] := by
    have h3 := congrArg CommRingCat.Hom.hom hs
    simpa [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id] using h3
  have happ : σ.hom (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) = (p : ℤ_[p]) := by
    have h4 := RingHom.congr_fun h2 (p : ℤ_[p])
    rw [RingHom.comp_apply, RingHom.id_apply] at h4
    exact h4
  have hunitK : IsUnit (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) := by
    refine isUnit_iff_ne_zero.mpr ?_
    rw [PadicInt.algebraMap_apply, PadicInt.coe_ne_zero]
    exact PadicInt.prime_p.ne_zero
  have hunit : IsUnit ((p : ℤ_[p])) := happ ▸ hunitK.map σ.hom
  exact (mem_nonunits_iff.mp (PadicInt.p_nonunit (p := p))) hunit

theorem gate_neronUniqueExtension_fails_genericFibreOnly (p : ℕ) [Fact p.Prime] :
    ¬ NeronUniqueExtension ℤ_[p] ℚ_[p] (specGenericFibreInclusion ℤ_[p] ℚ_[p]) := by
  intro h
  obtain ⟨φ, -⟩ := (h (Spec (CommRingCat.of ℤ_[p])) (𝟙 (Spec (CommRingCat.of ℤ_[p])))
    inferInstance).2
    ⟨pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[p]))) (specGenericFibreInclusion ℤ_[p] ℚ_[p]) ≫
        pullback.lift (𝟙 (Spec (CommRingCat.of ℚ_[p]))) (𝟙 (Spec (CommRingCat.of ℚ_[p]))) rfl,
      by simp [pullback.lift_snd]⟩
  exact (isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp p).false φ

theorem gate_neronModelPropertyBundle_not_genericFibreOnly (p : ℕ) [Fact p.Prime] :
    ¬ NeronModelPropertyBundle ℤ_[p] ℚ_[p] (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  fun h => gate_neronUniqueExtension_fails_genericFibreOnly p h.neronMapping

theorem gate_neronUniqueExtension_fails_genericFibreOnly_three :
    ¬ NeronUniqueExtension ℤ_[3] ℚ_[3] (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_neronUniqueExtension_fails_genericFibreOnly 3

end TeethGate

end NeronModelInfra

/--
info: 'NeronModelInfra.genericFibreRestrict_coe_eq_pullbackMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_coe_eq_pullbackMap

/--
info: 'NeronModelInfra.neronModelPropertyBundle_iff_propertyList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronModelPropertyBundle_iff_propertyList

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.existsUnique_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.existsUnique_extension

/--
info: 'NeronModelInfra.genericFibreRestrict_bijective_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_bijective_of_isIso

/--
info: 'NeronModelInfra.neronUniqueExtension_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronUniqueExtension_of_isIso

/--
info: 'NeronModelInfra.neronModelPropertyBundle_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronModelPropertyBundle_id

/--
info: 'NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_z3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_z3

/--
info: 'NeronModelInfra.isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly

/--
info: 'NeronModelInfra.gate_neronModelPropertyBundle_not_genericFibreOnly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModelPropertyBundle_not_genericFibreOnly

/--
info: 'NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly_three


