-- Prove2me | Definitions.Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism
-- name    : AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/ca3c9b46-7436-562b-9057-e035692afaee
-- title:
--   Uniqueness of Néron models up to unique isomorphism
-- statement:
--   Throughout, $R$ is a commutative ring with a field $K$ and an $R$-algebra structure on $K$ (in the final sections $R$ is moreover a Dedekind domain with $K$ its fraction field), and morphisms of schemes over $\operatorname{Spec} R$ are compared through the generic-fibre functor: for $f : X \to \operatorname{Spec} R$, the object $X_K$ is the pullback of $f$ along `specGenericFibreInclusion`, the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by $R \to K$, and `genericFibreRestrict` sends a morphism $\varphi : Y \to X$ with $\varphi \circ f = g$ to the induced morphism $Y_K \to X_K$ over $\operatorname{Spec} K$. The first two results record that this operation is functorial on underlying morphisms: it carries the identity to the identity and a composite to the corresponding composite (in diagrammatic order). Here `NeronUniqueExtension R K f` is the predicate that for every smooth $t : T \to \operatorname{Spec} R$ the restriction map on $\operatorname{Spec} R$-morphisms $T \to X$ is a bijection onto $\operatorname{Spec} K$-morphisms $T_K \to X_K$, and `NeronModelPropertyBundle` bundles this with smoothness, separatedness, local finite type and quasi-compactness of $f$.
--
--   The comparison results follow. If $f$ has the unique-extension property and is smooth, an endomorphism of $X$ over $\operatorname{Spec} R$ restricting to the identity on $X_K$ is the identity. Given two such $f, f'$, extensions of a fixed generic-fibre morphism are unique, every generic-fibre morphism extends uniquely, and mutually inverse $u_K, v_K$ lift to mutually inverse $u, v$ over $\operatorname{Spec} R$; this is packaged as existence, unique existence, and the statement that any extension of an invertible $u_K$ is an isomorphism, both for the bare hypotheses and for `NeronModelPropertyBundle`. A further variant takes $u_K$ invertible and produces the extension whose partner restricts to $u_K^{-1}$. Finally, three instances specialise these statements to $R = \mathbb{Z}_p$, $K = \mathbb{Q}_p$ (and $p = 3$) with $f$ the identity of $\operatorname{Spec} \mathbb{Z}_p$, for which the bundle holds because the structure morphism is an isomorphism.
--
--   **Relation to Mathlib.** Mathlib has no notion of Néron model; `NeronUniqueExtension`, `NeronModelPropertyBundle`, `SchemeHomOver` and `genericFibreRestrict` are the project's own, phrased with Mathlib's scheme pullbacks and its morphism properties `Smooth`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.
--
--   **Where it is used.** The Néron-model infrastructure supports the study of the Galois representations attached to elliptic curves over local and global fields, where a model over $\operatorname{Spec} R$ is pinned down by its generic fibre; these uniqueness statements are the form in which such a model may be treated as canonical.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism.lean

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

section ValueFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem genericFibreRestrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (χ : SchemeHomOver f f) (hχ : χ.1 = 𝟙 X) :
    (genericFibreRestrict R K f f χ).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, hχ]
  · simp [genericFibreRestrict, pullback.lift_snd]

theorem genericFibreRestrict_val_eq_comp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver g e)
    (hχ : χ.1 = φ.1 ≫ ψ.1) :
    (genericFibreRestrict R K e g χ).1 =
      (genericFibreRestrict R K f g φ).1 ≫ (genericFibreRestrict R K e f ψ).1 := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, hχ, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp [genericFibreRestrict, pullback.lift_snd]

end ValueFunctoriality

section MinimalModelLemma

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X : Scheme.{u}}

theorem neronModel_end_eq_id_of_restrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (hN : NeronUniqueExtension R K f) (hsf : Smooth f) (w : SchemeHomOver f f)
    (hw : (genericFibreRestrict R K f f w).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K))) :
    w.1 = 𝟙 X := by
  have hres : genericFibreRestrict R K f f w =
      genericFibreRestrict R K f f ⟨𝟙 X, Category.id_comp f⟩ := by
    apply Subtype.ext
    rw [hw, genericFibreRestrict_val_eq_id R K f ⟨𝟙 X, Category.id_comp f⟩ rfl]
  have hwid : w = (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) :=
    (hN X f hsf).1 hres
  exact congrArg Subtype.val hwid

end MinimalModelLemma

section TwoModels

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X X' : Scheme.{u}}

theorem neronTwoModels_extension_unique
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    {u₁ u₂ : SchemeHomOver f f'}
    (h : genericFibreRestrict R K f' f u₁ = genericFibreRestrict R K f' f u₂) :
    u₁ = u₂ :=
  (hNf' X f hsf).1 h

theorem neronTwoModels_existsUnique_homExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f', genericFibreRestrict R K f' f u = uK :=
  (hNf' X f hsf).existsUnique uK

theorem neronTwoModels_comp_eq_id
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hsf : Smooth f)
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    {vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} {v : SchemeHomOver f' f}
    (hu : genericFibreRestrict R K f' f u = uK)
    (hv : genericFibreRestrict R K f f' v = vK) :
    u.1 ≫ v.1 = 𝟙 X := by
  have hcomp : (u.1 ≫ v.1) ≫ f = f := by rw [Category.assoc, v.2, u.2]
  have hval : (genericFibreRestrict R K f f ⟨u.1 ≫ v.1, hcomp⟩).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
    rw [genericFibreRestrict_val_eq_comp R K f' f f u v ⟨u.1 ≫ v.1, hcomp⟩ rfl, hu, hv]
    exact huv
  exact neronModel_end_eq_id_of_restrict_val_eq_id R K f hNf hsf ⟨u.1 ≫ v.1, hcomp⟩ hval

theorem neronTwoModels_exists_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, hu⟩ := (hNf' X f hsf).2 uK
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨u, v, hu, hv, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩

theorem neronTwoModels_existsUnique_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, v, hu, hv, huvId, hvuId⟩ :=
    neronTwoModels_exists_isoExtension hNf hNf' hsf hsf' uK vK huv hvu
  refine ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

theorem neronTwoModels_isoExtension_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 := by
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨⟨v.1, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩⟩

theorem neronTwoModels_existsUnique_isoExtension_of_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) [IsIso uK.1] :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        (genericFibreRestrict R K f f' v).1 = inv uK.1 ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  have hvKmem : inv uK.1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f' (specGenericFibreInclusion R K) :=
    (IsIso.inv_comp_eq uK.1).mpr uK.2.symm
  obtain ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, -⟩ :=
    neronTwoModels_existsUnique_isoExtension hNf hNf' hsf hsf' uK ⟨inv uK.1, hvKmem⟩
      (IsIso.hom_inv_id uK.1) (IsIso.inv_hom_id uK.1)
  refine ⟨u, ⟨hu, v, congrArg Subtype.val hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

end TwoModels

section BundleForm

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X X' : Scheme.{u}}
variable {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.exists_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_exists_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.existsUnique_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_existsUnique_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.isoExtension_isIso
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 :=
  neronTwoModels_isoExtension_isIso h.neronMapping h'.neronMapping h.smooth h'.smooth
    vK huv hvu hu

end BundleForm

section SatGates

theorem gate_neronModel_end_eq_id_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime]
    (w : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[p]))) (𝟙 (Spec (CommRingCat.of ℤ_[p]))))
    (hw : (genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (𝟙 (Spec (CommRingCat.of ℤ_[p]))) w).1 =
      𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (specGenericFibreInclusion ℤ_[p] ℚ_[p]))) :
    w.1 = 𝟙 (Spec (CommRingCat.of ℤ_[p])) :=
  neronModel_end_eq_id_of_restrict_val_eq_id ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).smooth w hw

theorem gate_neronTwoModels_exists_isoExtension_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime] :
    ∃ (u v : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (𝟙 (Spec (CommRingCat.of ℤ_[p])))),
      genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
          (𝟙 (Spec (CommRingCat.of ℤ_[p]))) u =
        ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
            (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩ ∧
      genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
          (𝟙 (Spec (CommRingCat.of ℤ_[p]))) v =
        ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
            (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩ ∧
      u.1 ≫ v.1 = 𝟙 (Spec (CommRingCat.of ℤ_[p])) ∧
      v.1 ≫ u.1 = 𝟙 (Spec (CommRingCat.of ℤ_[p])) :=
  neronTwoModels_exists_isoExtension
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).smooth
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).smooth
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩
    (Category.id_comp _) (Category.id_comp _)

theorem gate_neronTwoModels_existsUnique_isoExtension_trivialGroupScheme_z3 :
    ∃! u : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
      genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
          (𝟙 (Spec (CommRingCat.of ℤ_[3]))) u =
        ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
            (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩ ∧
      ∃ v : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
        genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
            (𝟙 (Spec (CommRingCat.of ℤ_[3]))) v =
          ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
              (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩ ∧
        u.1 ≫ v.1 = 𝟙 (Spec (CommRingCat.of ℤ_[3])) ∧
        v.1 ≫ u.1 = 𝟙 (Spec (CommRingCat.of ℤ_[3])) :=
  neronTwoModels_existsUnique_isoExtension
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).smooth
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).smooth
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩
    (Category.id_comp _) (Category.id_comp _)

end SatGates

end NeronModelInfra

/--
info: 'NeronModelInfra.genericFibreRestrict_val_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_val_eq_id

/--
info: 'NeronModelInfra.genericFibreRestrict_val_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_val_eq_comp

/--
info: 'NeronModelInfra.neronModel_end_eq_id_of_restrict_val_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronModel_end_eq_id_of_restrict_val_eq_id

/--
info: 'NeronModelInfra.neronTwoModels_extension_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_extension_unique

/--
info: 'NeronModelInfra.neronTwoModels_existsUnique_homExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_existsUnique_homExtension

/--
info: 'NeronModelInfra.neronTwoModels_comp_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_comp_eq_id

/--
info: 'NeronModelInfra.neronTwoModels_exists_isoExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_exists_isoExtension

/--
info: 'NeronModelInfra.neronTwoModels_existsUnique_isoExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_existsUnique_isoExtension

/--
info: 'NeronModelInfra.neronTwoModels_isoExtension_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_isoExtension_isIso

/--
info: 'NeronModelInfra.neronTwoModels_existsUnique_isoExtension_of_isIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_existsUnique_isoExtension_of_isIso

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.exists_isoExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.exists_isoExtension

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.existsUnique_isoExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.existsUnique_isoExtension

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.isoExtension_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.isoExtension_isIso

/--
info: 'NeronModelInfra.gate_neronModel_end_eq_id_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModel_end_eq_id_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_neronTwoModels_exists_isoExtension_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronTwoModels_exists_isoExtension_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_neronTwoModels_existsUnique_isoExtension_trivialGroupScheme_z3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronTwoModels_existsUnique_isoExtension_trivialGroupScheme_z3


