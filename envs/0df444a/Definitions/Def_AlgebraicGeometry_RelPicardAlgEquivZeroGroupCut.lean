-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
-- name    : AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/0b5a8a61-d835-562f-b96b-28b2691cc46e
-- title:
--   Pic⁰ cut as a group condition on rigidified line bundles
-- statement:
--   Over a field $k$, a module $L$ on a $k$-scheme $a \colon A \to \operatorname{Spec} k$ satisfies `IsAlgEquivZero a L` when there are a morphism $h \colon T' \to \operatorname{Spec} k$ that is locally of finite type and satisfies `GeometricallyIntegral`, an invertible module $N$ on $A \times_{\operatorname{Spec} k} T'$, and two $k$-points $t_0, t_1$ of $T'$ (morphisms $\operatorname{Spec} k \to T'$ over $\operatorname{Spec} k$), such that the pullback of $N$ along the base-change morphism attached to $t_0$ is isomorphic to the unit module on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$, while the pullback along $t_1$ is isomorphic to the pullback of $L$ along the first projection. Three results establish the group-theoretic stability of this notion. `GeometricallyIntegral.fst_comp_of_field` states that for $h_1, h_2$ to $\operatorname{Spec} k$, both locally of finite type and `GeometricallyIntegral` (a class whose content, as used, yields integrality of base changes along morphisms from spectra of fields), the composite of the first projection of $T_1 \times_k T_2$ with $h_1$ is again `GeometricallyIntegral`. `IsAlgEquivZero.tensor` closes the predicate under the tensor product of the symmetric monoidal structure on modules, the witness being the product of the two parameter schemes carrying the external tensor product of the two families; `IsAlgEquivZero.of_tensor_iso_unit` shows that if $L$ is algebraically equivalent to zero and $L \otimes M$ is isomorphic to the unit, then so is $M$.
--
--   These are transported to rigidified line bundles over $c \colon C \to \operatorname{Spec} R$ with rigidifying section $\varepsilon$: `FibrewiseAlgEquivZero.tensor` and `FibrewiseAlgEquivZero.of_tensor_iso_unit` give the same two closure properties for the fibrewise condition (algebraic equivalence to zero of the restriction to every fibre over an algebraically closed-field point of the base), the second hypothesis being only an isomorphism of underlying modules, not of rigidifications. `algEquivZeroGroupCut c ε` packages this as a `SubPicGroupCondition` whose underlying `SubPicCondition` is `algEquivZeroCut c ε`, as recorded by the final lemma.
--
--   **Relation to Mathlib.** The relative Picard formalism used here — `SchemeHomOver`, `RigidifiedLineBundle`, `SubPicCondition`, `SubPicGroupCondition`, `GeometricallyIntegral` and the predicate `IsAlgEquivZero` — is the project's own; the symmetric monoidal closed structure on a scheme's sheaves of modules and the monoidality of pullback are also constructed within the project, on top of Mathlib's sheaves of modules and fibre products of schemes.
--
--   **Where it is used.** The group condition furnished here is what makes the rigidified relative Picard functor cut out by fibrewise algebraic equivalence to zero a presheaf of commutative groups, so that a scheme representing it carries a commutative relative group law with the designated zero section as unit. This is the route by which $\operatorname{Pic}^0$ of a relative curve is given its group structure, as needed for Jacobians of modular curves and their Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

theorem GeometricallyIntegral.fst_comp_of_field {k : Type u} [Field k] {T₁ T₂ : Scheme.{u}}
    (h₁ : T₁ ⟶ Spec (CommRingCat.of k)) (h₂ : T₂ ⟶ Spec (CommRingCat.of k))
    [GeometricallyIntegral h₁] [LocallyOfFiniteType h₁] [GeometricallyIntegral h₂] [LocallyOfFiniteType h₂] :
    GeometricallyIntegral (pullback.fst h₁ h₂ ≫ h₁) := by
  constructor
  intro K _ y Z fst' snd' hP

  haveI : AlgebraicGeometry.IsIntegral (Limits.pullback h₁ y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := h₁) y (pullback.fst h₁ y) (pullback.snd h₁ y)
      (IsPullback.of_hasPullback h₁ y)

  haveI : AlgebraicGeometry.IsIntegral (Limits.pullback (pullback.fst h₁ h₂) (pullback.fst h₁ y)) := inferInstance

  exact AlgebraicGeometry.IsIntegral.of_isIso
    (pullbackRightPullbackFstIso h₁ y (pullback.fst h₁ h₂) ≪≫ hP.isoPullback.symm).hom

end AlgebraicGeometry

namespace AlgebraicGeometry.RelPicard

theorem IsAlgEquivZero.tensor {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L M : A.Modules} (hL : IsAlgEquivZero a L) (hM : IsAlgEquivZero a M) : IsAlgEquivZero a (L ⊗ M) := by
  obtain ⟨T₁, h₁, hft₁, hgi₁, N₁, hN₁, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL
  obtain ⟨T₂, h₂, hft₂, hgi₂, N₂, hN₂, s₀, s₁, ⟨f₀⟩, ⟨f₁⟩⟩ := hM

  let T := Limits.pullback h₁ h₂
  let h : T ⟶ Spec (CommRingCat.of k) := pullback.fst h₁ h₂ ≫ h₁
  haveI : LocallyOfFiniteType h := inferInstance
  haveI : GeometricallyIntegral h := GeometricallyIntegral.fst_comp_of_field h₁ h₂

  let p₁ : Limits.pullback a h ⟶ Limits.pullback a h₁ :=
    pullback.map a h a h₁ (𝟙 A) (pullback.fst h₁ h₂) (𝟙 _) (by simp) (by simp [h])
  let p₂ : Limits.pullback a h ⟶ Limits.pullback a h₂ :=
    pullback.map a h a h₂ (𝟙 A) (pullback.snd h₁ h₂) (𝟙 _) (by simp) (by simp [h, pullback.condition])

  have hts : ∀ (tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₁)
      (ss : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₂), tt.1 ≫ h₁ = ss.1 ≫ h₂ := fun tt ss => by
    rw [tt.2, ss.2]
  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₁ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₂ →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h := fun tt ss =>
    ⟨pullback.lift tt.1 ss.1 (hts tt ss), by simp only [h, pullback.lift_fst_assoc]; exact tt.2⟩

  have hsq₁ : ∀ tt ss, baseChangeSnd a (u tt ss) ≫ p₁ = baseChangeSnd a tt := by
    intro tt ss
    apply pullback.hom_ext <;>
      simp only [p₁, u, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id]
  have hsq₂ : ∀ tt ss, baseChangeSnd a (u tt ss) ≫ p₂ = baseChangeSnd a ss := by
    intro tt ss
    apply pullback.hom_ext <;>
      simp only [p₂, u, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id]

  refine ⟨T, h, inferInstance, inferInstance,
    (Scheme.Modules.pullback p₁).obj N₁ ⊗ (Scheme.Modules.pullback p₂).obj N₂,
    (hN₁.pullback p₁).tensor (hN₂.pullback p₂), u t₀ s₀, u t₁ s₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      ((((Scheme.Modules.pullbackComp _ _).app N₁ ≪≫ (Scheme.Modules.pullbackCongr (hsq₁ t₀ s₀)).app N₁ ≪≫ e₀) ⊗ᵢ
        ((Scheme.Modules.pullbackComp _ _).app N₂ ≪≫ (Scheme.Modules.pullbackCongr (hsq₂ t₀ s₀)).app N₂ ≪≫ f₀))) ≪≫
      λ_ _
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      ((((Scheme.Modules.pullbackComp _ _).app N₁ ≪≫ (Scheme.Modules.pullbackCongr (hsq₁ t₁ s₁)).app N₁ ≪≫ e₁) ⊗ᵢ
        ((Scheme.Modules.pullbackComp _ _).app N₂ ≪≫ (Scheme.Modules.pullbackCongr (hsq₂ t₁ s₁)).app N₂ ≪≫ f₁))) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

theorem IsAlgEquivZero.of_tensor_iso_unit {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L M : A.Modules} (hL : IsAlgEquivZero a L) (e : L ⊗ M ≅ 𝟙_ A.Modules) : IsAlgEquivZero a M := by
  obtain ⟨T', h, hft, hgi, N, hN, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  obtain ⟨N', hN', ⟨eN⟩⟩ := hN.exists_tensor_inverse

  have uniq : ∀ {V : Scheme.{u}} (X Y Y' : V.Modules), (X ⊗ Y ≅ 𝟙_ _) → (X ⊗ Y' ≅ 𝟙_ _) → (Y ≅ Y') :=
    fun X Y Y' i i' =>
      (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫
        (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'
  refine ⟨T', h, hft, hgi, N', hN', t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  ·
    have i : (Scheme.Modules.pullback (baseChangeSnd a t₀)).obj N ⊗
        (Scheme.Modules.pullback (baseChangeSnd a t₀)).obj N' ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso eN ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
    exact uniq _ _ _ i ((e₀ ⊗ᵢ Iso.refl _) ≪≫ λ_ _)
  ·
    have i : (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N ⊗
        (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N' ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso eN ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
    have i' : (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N ⊗
        (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj M ≅ 𝟙_ _ :=
      (e₁ ⊗ᵢ Iso.refl _) ≪≫ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _
    exact uniq _ _ _ i i'

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem FibrewiseAlgEquivZero.tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L M : RigidifiedLineBundle c ε t} (hL : FibrewiseAlgEquivZero L) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (L.tensor M) := by
  intro k _ _ s
  exact IsAlgEquivZero.of_iso (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ((hL k s).tensor (hM k s))

theorem FibrewiseAlgEquivZero.of_tensor_iso_unit {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L M : RigidifiedLineBundle c ε t}
    (e : Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L))
    (hL : FibrewiseAlgEquivZero L) : FibrewiseAlgEquivZero M := by
  intro k _ _ s

  refine (hL k s).of_tensor_iso_unit ?_
  exact (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e.some ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso _

def algEquivZeroGroupCut (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicGroupCondition c ε where
  toSubPicCondition := algEquivZeroCut c ε
  tensor_mem := fun _ _ _ hL hM => FibrewiseAlgEquivZero.tensor hL hM
  inv_mem := fun _ _ _ e hL => FibrewiseAlgEquivZero.of_tensor_iso_unit e hL

@[simp] theorem algEquivZeroGroupCut_toSubPicCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (algEquivZeroGroupCut c ε).toSubPicCondition = algEquivZeroCut c ε := rfl

end AlgebraicGeometry.RelPicard

end


