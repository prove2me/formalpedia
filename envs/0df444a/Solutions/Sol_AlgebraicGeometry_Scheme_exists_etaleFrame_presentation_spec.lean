-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_spec
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T18:10:49.133965+00:00
-- url     : https://prove2.me/submissions/a0a47feb-922b-4a5a-abc3-fbc12a2012ad

import Definitions.Def_AlgebraicGeometry_EtaleFrameTorsorCompletion
import Mathlib.Algebra.Category.ModuleCat.Descent

section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers PhilipponTorsorInvariantDescent

namespace PhilipponAffineEtaleTorsorCover
universe u

/-- Over an affine scheme, a units torsor has sections on a finite
jointly surjective family of affine étale objects. -/
theorem exists_affine_family (X : Scheme.{u}) [IsAffine X]
    (A : Torsor (PhilipponKummerSequence.units X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Etale),
      (∀ i, IsAffine (V i).left) ∧ (∀ i, Nonempty (A.D.P.obj (op (V i)))) ∧
      ∀ x : X, ∃ (i : ι) (y : (V i).left), (V i).hom y = x := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let R := presence A.D.P T
  have hR : R ∈ X.smallEtaleTopology T := A.locally_nonempty T
  obtain ⟨U, hOver, hU, h⟩ := (Scheme.mem_smallGrothendieckTopology T R).mp hR
  let : U.Over X := hOver
  let : QuasiCompactCover U.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i => (U.f i).isOpenMap)
  let : CompactSpace T.left := inferInstanceAs (CompactSpace X)
  obtain ⟨W, r, hfin, _⟩ := QuasiCompactCover.exists_hom.{u} U
  let : ∀ i, Etale (W.f i) := fun i => W.cover.map_prop i
  let V (i : W.I₀) : X.Etale := Scheme.Etale.mk (W.f i)
  refine ⟨W.I₀, hfin, V, fun i => inferInstanceAs (IsAffine (Spec (W.X i))), ?_, ?_⟩
  · intro i
    let j := r.s₀ i
    let Uj := (U.X j).asOverProp X (hU j)
    let u : Uj ⟶ T := (U.f j).asOverProp X
    have hu : U.toPresieveOverProp hU u := ⟨j⟩
    obtain ⟨s⟩ : Nonempty (A.D.P.obj (op Uj)) := h _ _ hu
    have huj : (U.f j) = Uj.hom := by
      change U.f j = U.X j ↘ X
      exact (Category.comp_id (U.f j)).symm.trans (comp_over (U.f j) X)
    let v : V i ⟶ Uj := MorphismProperty.Over.homMk (r.h₀ i)
      ((congrArg (r.h₀ i ≫ ·) huj.symm).trans (r.w₀ i)) trivial
    exact ⟨A.D.P.map v.op s⟩
  · intro x
    obtain ⟨y, hy⟩ := W.covers x
    exact ⟨W.idx x, y, hy⟩

private theorem sections_subsingleton_of_empty {X : Scheme.{u}}
    (A : Torsor (PhilipponKummerSequence.units X)) {W : X.Etale}
    (hW : IsEmpty W.left) : Subsingleton (A.D.P.obj (op W)) := by
  let V : Empty → X.Etale := Empty.elim
  let p (i : Empty) : V i ⟶ W := Empty.elim i
  have hCover : Sieve.ofArrows V p ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr
    exact Set.ext fun x => (hW.false x).elim
  have hBot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Empty.elim i
  refine ⟨fun x y => ?_⟩
  apply (A.isSheaf.isSheafFor _ hBot).isSeparatedFor.ext
  intro _ _ h
  exact h.elim

/-- A units torsor over an affine scheme has a section on one affine
surjective étale scheme. -/
theorem exists_affine_object (X : Scheme.{u}) [IsAffine X]
    (A : Torsor (PhilipponKummerSequence.units X)) :
    ∃ E : X.Etale, IsAffine E.left ∧ Function.Surjective E.hom ∧
      Nonempty (A.D.P.obj (op E)) := by
  obtain ⟨ι, hfin, V, ha, hs, hsur⟩ := exists_affine_family X A
  let : Finite ι := hfin
  let Y := fun i : ι => (V i).left
  let : ∀ i, IsAffine (Y i) := ha
  let q : (∐ Y) ⟶ X := Sigma.desc (fun i => (V i).hom)
  let : Etale q := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover Y)).mpr
    intro i
    change Etale (Sigma.ι Y i ≫ q)
    rw [Sigma.ι_desc]
    exact (V i).prop
  let E : X.Etale := Scheme.Etale.mk q
  let j (i : ι) : V i ⟶ E :=
    MorphismProperty.Over.homMk (Sigma.ι Y i) (Sigma.ι_desc _ _) trivial
  refine ⟨E, inferInstanceAs (IsAffine (∐ Y)), ?_, ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := hsur x
    refine ⟨Sigma.ι Y i y, ?_⟩
    change (Sigma.ι Y i ≫ q) y = x
    rw [Sigma.ι_desc]
    exact hy
  · have hCover : Sieve.ofArrows V j ∈ X.smallEtaleTopology E := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      let oc := sigmaOpenCover Y
      obtain ⟨y, hy⟩ := oc.covers x
      exact ⟨oc.idx x, y, hy⟩
    have hSheaf : Presieve.IsSheafFor A.D.P (.ofArrows V j) :=
      (Presieve.isSheafFor_iff_generate (.ofArrows V j)).mpr (A.isSheaf.isSheafFor _ hCover)
    let s (i : ι) : A.D.P.obj (op (V i)) := (hs i).some
    have hCompat : Presieve.Arrows.Compatible A.D.P j s := by
      intro i k W a b h
      have hh : a.left ≫ Sigma.ι Y i = b.left ≫ Sigma.ι Y k :=
        congrArg (fun t : W ⟶ E => t.left) h
      by_cases hEq : i = k
      · subst k
        have hSame : a = b := MorphismProperty.Over.Hom.ext ((cancel_mono (Sigma.ι Y i)).mp hh)
        rw [hSame]
      · exact (sections_subsingleton_of_empty A (isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ hEq)).elim _ _
    obtain ⟨s', _, _⟩ := (Presieve.isSheafFor_arrows_iff (π := j) (P := A.D.P)).mp hSheaf s hCompat
    exact ⟨s'⟩

/-- The affine covering object can be presented as the spectrum of
a faithfully flat étale ring extension. -/
theorem exists_spec_cover (R : CommRingCat.{u})
    (A : Torsor (PhilipponKummerSequence.units (Spec R))) :
    ∃ (S : CommRingCat.{u}) (f : R ⟶ S) (_ : Etale (Spec.map f)),
      f.hom.FaithfullyFlat ∧ Nonempty (A.D.P.obj (op (Scheme.Etale.mk (Spec.map f)))) := by
  obtain ⟨E, ha, hsur, ⟨s⟩⟩ := exists_affine_object (Spec R) A
  let : IsAffine E.left := ha
  let : Etale E.hom := E.prop
  let : Surjective E.hom := ⟨hsur⟩
  let g := E.left.isoSpec.inv ≫ E.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective g
  let : Etale (Spec.map f) := by
    rw [hf]
    exact inferInstanceAs (Etale (E.left.isoSpec.inv ≫ E.hom))
  have hs : Surjective (Spec.map f) := by
    rw [hf]
    exact inferInstanceAs (Surjective (E.left.isoSpec.inv ≫ E.hom))
  have hff := (flat_and_surjective_SpecMap_iff f).mp ⟨inferInstance, hs⟩
  let e : Scheme.Etale.mk (Spec.map f) ⟶ E :=
    MorphismProperty.Over.homMk E.left.isoSpec.inv hf.symm trivial
  exact ⟨_, f, inferInstance, hff, ⟨A.D.P.map e.op s⟩⟩

end PhilipponAffineEtaleTorsorCover
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers

namespace PhilipponEtaleTorsorTransitions
universe u
variable {X : Scheme.{u}} (A : Torsor (PhilipponKummerSequence.units X))
variable {U V W T : X.Etale} (s : A.D.P.obj (op U))

/-- The transition unit between two restrictions of the same frame. -/
def transition (a b : V ⟶ U) : (Γ(V.left, ⊤))ˣ :=
  Additive.toMul (A.D.diff (op V) (A.D.P.map a.op s) (A.D.P.map b.op s))

theorem transition_self (a : V ⟶ U) : transition A s a a = 1 := by
  let p := A.D.P.map a.op s
  have h := A.D.diff_add_diff (op V) p p p
  let d := A.D.diff (op V) p p
  change d + d = d at h
  exact congrArg Additive.toMul (add_left_cancel (h.trans (add_zero d).symm))

theorem transition_mul (a b c : V ⟶ U) :
    transition A s a b * transition A s b c = transition A s a c :=
  congrArg Additive.toMul (A.D.diff_add_diff (op V) (A.D.P.map a.op s)
    (A.D.P.map b.op s) (A.D.P.map c.op s))

theorem transition_restrict (a b : V ⟶ U) (g : W ⟶ V) :
    Units.map g.left.appTop.hom.toMonoidHom (transition A s a b) =
      transition A s (g ≫ a) (g ≫ b) := by
  change Additive.toMul ((PhilipponKummerSequence.units X).obj.map g.op
    (A.D.diff (op V) (A.D.P.map a.op s) (A.D.P.map b.op s))) =
      Additive.toMul (A.D.diff (op W) (A.D.P.map (g ≫ a).op s) (A.D.P.map (g ≫ b).op s))
  rw [A.D.map_diff, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]

/-- The transition unit on an actual pairwise fiber product. -/
def overlap (f : U ⟶ T) : (Γ((pullback f f).left, ⊤))ˣ :=
  transition A s (pullback.fst f f) (pullback.snd f f)

theorem overlap_pullback (f : U ⟶ T) (a b : V ⟶ U) (h : a ≫ f = b ≫ f) :
    Units.map (pullback.lift a b h).left.appTop.hom.toMonoidHom (overlap A s f) =
      transition A s a b := by
  rw [overlap, transition_restrict, pullback.lift_fst, pullback.lift_snd]

/-- The overlap unit is normalized along the diagonal. -/
theorem overlap_diagonal (f : U ⟶ T) :
    Units.map (pullback.lift (𝟙 U) (𝟙 U) rfl).left.appTop.hom.toMonoidHom (overlap A s f) = 1 :=
  (overlap_pullback A s f _ _ rfl).trans (transition_self A s (𝟙 U))

/-- The cocycle identity on any triple of overlap projections, including
the canonical projections from the triple fiber product. -/
theorem overlap_cocycle (f : U ⟶ T) (a b c : V ⟶ U)
    (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f) :
    Units.map (pullback.lift a b hab).left.appTop.hom.toMonoidHom (overlap A s f) *
        Units.map (pullback.lift b c hbc).left.appTop.hom.toMonoidHom (overlap A s f) =
      Units.map (pullback.lift a c (hab.trans hbc)).left.appTop.hom.toMonoidHom (overlap A s f) := by
  rw [overlap_pullback, overlap_pullback, overlap_pullback, transition_mul]

end PhilipponEtaleTorsorTransitions
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory ModuleCat

namespace PhilipponRankOneCoalgebra
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

abbrev freeOne (S : Type u) [CommRing S] : ModuleCat.{u} S := ModuleCat.of S S
abbrev comonad := (ModuleCat.extendRestrictScalarsAdj f).toComonad
abbrev comparison := Comonad.comparison (ModuleCat.extendRestrictScalarsAdj f)

/-- A linear coaction on the free module is specified by the image of one. -/
def coaction (t : ((comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S))) :
    freeOne S ⟶ (comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S) :=
  ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf S ℤ _).symm t)

theorem coaction_one (t : ((comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S))) :
    coaction f t (1 : S) = t := by
  change (LinearMap.ringLmapEquivSelf S ℤ _).symm t (1 : S) = t
  simp

theorem coaction_apply (t : ((comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S))) (s : S) :
    coaction f t s = s • t := by
  calc
    coaction f t s = coaction f t (s • (1 : S)) := by rw [smul_eq_mul, mul_one]
    _ = s • coaction f t (1 : S) := (coaction f t).hom.map_smul s (1 : S)
    _ = s • t := congrArg (s • ·) (coaction_one f t)

/-- The counit and cocycle equations on the image of the free generator. -/
structure IsDescentElement (t : ((comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S))) : Prop where
  counit : (comonad f).ε.app (freeOne S) t = (1 : S)
  cocycle : (comonad f).δ.app (freeOne S) t = (comonad f).map (coaction f t) t

private theorem hom_ext_one {N : ModuleCat.{u} S} (a b : freeOne S ⟶ N) (h : a (1 : S) = b (1 : S)) :
    a = b := by
  apply ModuleCat.hom_ext
  apply (LinearMap.ringLmapEquivSelf S ℤ N).injective
  exact h

def coalgebra {t : ((comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S))}
    (h : IsDescentElement f t) : (comonad f).Coalgebra where
  A := freeOne S
  a := coaction f t
  counit := by
    apply hom_ext_one _ _
    change (comonad f).ε.app (freeOne S) (coaction f t (1 : S)) = (1 : S)
    rw [coaction_one]
    exact h.counit
  coassoc := by
    apply hom_ext_one _ _
    change (comonad f).δ.app (freeOne S) (coaction f t (1 : S)) =
      (comonad f).map (coaction f t) (coaction f t (1 : S))
    rw [coaction_one]
    exact h.cocycle

/-- A compatible rank-one coaction is induced by a module over the
base ring, with the full coaction retained in the comparison isomorphism. -/
theorem exists_model (hf : f.FaithfullyFlat)
    {t : ((comonad f : ModuleCat S ⥤ ModuleCat S).obj (freeOne S))} (h : IsDescentElement f t) :
    ∃ M : ModuleCat.{u} R, Nonempty ((comparison f).obj M ≅ coalgebra f h) := by
  let hC := comonadicExtendScalars hf
  let : (comparison f).IsEquivalence := hC.eqv
  exact ⟨(comparison f).objPreimage (coalgebra f h),
    ⟨(comparison f).objObjPreimageIso (coalgebra f h)⟩⟩

end PhilipponRankOneCoalgebra
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory ModuleCat TensorProduct
open PhilipponRankOneCoalgebra

namespace PhilipponRankOneTensorCocycle
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

section AlgebraMaps
variable (R S) [Algebra R S]

abbrev diagonal : (S ⊗[R] S) →ₐ[R] S :=
  Algebra.TensorProduct.productMap (AlgHom.id R S) (AlgHom.id R S)

abbrev face₁₂ : (S ⊗[R] S) →ₐ[R] (S ⊗[R] (S ⊗[R] S)) :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft

abbrev face₁₃ : (S ⊗[R] S) →ₐ[R] (S ⊗[R] (S ⊗[R] S)) :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight

abbrev face₂₃ : (S ⊗[R] S) →ₐ[R] (S ⊗[R] (S ⊗[R] S)) := Algebra.TensorProduct.includeRight

end AlgebraMaps

/-- The ordinary tensor-product cocycle gives a normalized coaction on
the free rank-one module. The order of its three faces is fixed by the
choice of left scalar multiplication in extension of scalars. -/
theorem isDescentElement (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    ∀ t : S ⊗[R] S, diagonal R S t = 1 →
      face₁₃ R S t = face₁₂ R S t * face₂₃ R S t → IsDescentElement f t := by
  let : Algebra R S := f.toAlgebra
  intro t h₁ h₂
  have hε (z : S ⊗[R] S) : (comonad f).ε.app (freeOne S) z = diagonal R S z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s a => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hδ (z : S ⊗[R] S) : (comonad f).δ.app (freeOne S) z = face₁₃ R S z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s a => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hmap (z : S ⊗[R] S) : (comonad f).map (coaction f t) z = face₁₂ R S z * face₂₃ R S t := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul]
    | tmul s a =>
      let x : S ⊗[R] S := coaction f t a
      have hx : x = a • t := coaction_apply f t a
      change TensorProduct.tmul R (M := S) (N := S ⊗[R] S) s x = _
      rw [hx, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self]
      rfl
    | add a b ha hb => rw [map_add, map_add, add_mul, ha, hb]
  exact ⟨(hε t).trans h₁, (hδ t).trans (h₂.trans (hmap t).symm)⟩

end PhilipponRankOneTensorCocycle
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open PhilipponTorsorSectionFibers PhilipponEtaleTorsorTransitions
open PhilipponRankOneTensorCocycle

namespace PhilipponAffineEtaleTorsorCocycle
universe u
variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

abbrev baseMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

abbrev specMap (k : A →ₐ[R] B) := Spec.map (CommRingCat.ofHom k.toRingHom)

theorem specMap_over (k : A →ₐ[R] B) : specMap k ≫ baseMap R A = baseMap R B := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact k.commutes x

instance tensor_etale [Etale (baseMap R A)] [Etale (baseMap R B)] :
    Etale (baseMap R (A ⊗[R] B)) := by
  let i : A →ₐ[R] A ⊗[R] B := Algebra.TensorProduct.includeLeft
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R A B)
  let : Etale (specMap i) := MorphismProperty.of_isPullback (P := @Etale) hp.flip (by infer_instance)
  rw [← specMap_over (R := R) i]
  infer_instance

abbrev obj (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Etale (baseMap R A)] :=
  Scheme.Etale.mk (baseMap R A)

variable [Etale (baseMap R A)] [Etale (baseMap R B)] [Etale (baseMap R C)]

def arrow (k : A →ₐ[R] B) : obj R B ⟶ obj R A :=
  MorphismProperty.Over.homMk (specMap k) (specMap_over k) trivial

theorem arrow_comp (i : A →ₐ[R] B) (j : B →ₐ[R] C) : arrow j ≫ arrow i = arrow (j.comp i) := by
  apply MorphismProperty.Over.Hom.ext
  change specMap j ≫ specMap i = specMap (j.comp i)
  rw [← Spec.map_comp]
  rfl

abbrev scalarUnits (B : Type u) [CommRing B] (t : (Γ(Spec (CommRingCat.of B), ⊤))ˣ) : Bˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom t

theorem scalarUnits_map (k : A →ₐ[R] B) (t : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) :
    scalarUnits B (Units.map (specMap k).appTop.hom.toMonoidHom t) =
      Units.map k.toMonoidHom (scalarUnits A t) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom k.toRingHom)) t.val

variable (P : Torsor (PhilipponKummerSequence.units (Spec (CommRingCat.of R))))
variable (s : P.D.P.obj (op (obj R A)))

def scalarTransition (i j : A →ₐ[R] B) : Bˣ :=
  scalarUnits B (transition P s (arrow i) (arrow j))

theorem scalarTransition_self (i : A →ₐ[R] B) : scalarTransition P s i i = 1 := by
  rw [scalarTransition, transition_self]
  exact (Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom).map_one

theorem scalarTransition_mul (i j k : A →ₐ[R] B) :
    scalarTransition P s i j * scalarTransition P s j k = scalarTransition P s i k := by
  rw [scalarTransition, scalarTransition, scalarTransition, ← map_mul, transition_mul]

theorem scalarTransition_map (i j : A →ₐ[R] B) (k : B →ₐ[R] C) :
    Units.map k.toMonoidHom (scalarTransition P s i j) = scalarTransition P s (k.comp i) (k.comp j) := by
  unfold scalarTransition
  rw [← scalarUnits_map, ← arrow_comp i k, ← arrow_comp j k]
  exact congrArg (scalarUnits C) (transition_restrict P s (arrow i) (arrow j) (arrow k))

local notation "Q₂" => A ⊗[R] A
local notation "Q₃" => A ⊗[R] (A ⊗[R] A)

abbrev leftFace : A →ₐ[R] Q₂ := Algebra.TensorProduct.includeLeft
abbrev rightFace : A →ₐ[R] Q₂ := Algebra.TensorProduct.includeRight

def overlapUnit : Q₂ˣ := scalarTransition P s leftFace rightFace

/-- On affine spectra, an actual torsor section yields a normalized
unit in the tensor square satisfying the usual tensor-cube cocycle. -/
theorem overlapUnit_cocycle :
    diagonal R A (overlapUnit P s : Q₂) = 1 ∧
      face₁₃ R A (overlapUnit P s : Q₂) = face₁₂ R A (overlapUnit P s : Q₂) *
        face₂₃ R A (overlapUnit P s : Q₂) := by
  constructor
  · have h : (diagonal R A).comp (leftFace : A →ₐ[R] Q₂) =
        (diagonal R A).comp (rightFace : A →ₐ[R] Q₂) := by
      ext a
      simp [diagonal, Algebra.TensorProduct.productMap]
    have hh : Units.map (diagonal R A).toMonoidHom (overlapUnit P s) = 1 := by
      rw [overlapUnit, scalarTransition_map, h, scalarTransition_self]
    exact congrArg Units.val hh
  · let a : A →ₐ[R] Q₃ := Algebra.TensorProduct.includeLeft
    let b : A →ₐ[R] Q₃ := Algebra.TensorProduct.includeRight.comp (leftFace : A →ₐ[R] Q₂)
    let c : A →ₐ[R] Q₃ := Algebra.TensorProduct.includeRight.comp (rightFace : A →ₐ[R] Q₂)
    have h₁ : (face₁₂ R A).comp (leftFace : A →ₐ[R] Q₂) = a := by
      ext t
      simp [face₁₂, a]
    have h₂ : (face₁₂ R A).comp (rightFace : A →ₐ[R] Q₂) = b := by
      ext t
      simp [face₁₂, b]
    have h₃ : (face₁₃ R A).comp (leftFace : A →ₐ[R] Q₂) = a := by
      ext t
      simp [face₁₃, a]
    have h₄ : (face₁₃ R A).comp (rightFace : A →ₐ[R] Q₂) = c := by
      ext t
      simp [face₁₃, c]
    have hh : Units.map (face₁₃ R A).toMonoidHom (overlapUnit P s) =
        Units.map (face₁₂ R A).toMonoidHom (overlapUnit P s) *
          Units.map (face₂₃ R A).toMonoidHom (overlapUnit P s) := by
      simp only [overlapUnit, scalarTransition_map, h₁, h₂, h₃, h₄]
      exact (scalarTransition_mul P s a b c).symm
    exact congrArg Units.val hh

end PhilipponAffineEtaleTorsorCocycle
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponTildeBaseChange
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

private abbrev σ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom f)

/-- The global sections of the pushforward along a map of affine schemes
are the global sections of the original module with scalars restricted. -/
def pushforwardΓ : Scheme.Modules.pushforward (σ f) ⋙ moduleSpecΓFunctor (R := CommRingCat.of R) ≅
    moduleSpecΓFunctor (R := CommRingCat.of S) ⋙ ModuleCat.restrictScalars f := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let P : ModuleCat R := (Scheme.Modules.pushforward (σ f) ⋙
      moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
    let Q : ModuleCat R := (moduleSpecΓFunctor (R := CommRingCat.of S) ⋙
      ModuleCat.restrictScalars f).obj M
    change P ≅ Q
    let e : P ≃ₗ[R] Q :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change ↥Γ(M, ⊤) at x
          change ((σ f).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) • x =
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv (f r)) • x
          exact congrArg (· • x) (ConcreteCategory.congr_hom
            (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r).symm }
    exact e.toModuleIso
  · intro M N a
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Pulling back the quasi-coherent sheaf of a module along a map of
affine schemes agrees with extension of scalars on that module. -/
def tildePullback : tilde.functor (CommRingCat.of R) ⋙ Scheme.Modules.pullback (σ f) ≅
    ModuleCat.extendScalars f ⋙ tilde.functor (CommRingCat.of S) :=
  (((tilde.adjunction (R := CommRingCat.of R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (σ f))).ofNatIsoRight (pushforwardΓ f)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj f).comp (tilde.adjunction (R := CommRingCat.of S)))

end PhilipponTildeBaseChange
end
end

section
set_option autoImplicit false
noncomputable section

open TensorProduct

namespace PhilipponFaithfullyFlatRankOne
universe u v w
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S] {M : Type w} [AddCommGroup M] [Module R M]

/-- If base change to a faithfully flat algebra is free of rank one,
the original module is free of rank one on a principal neighborhood of
each prime. -/
theorem exists_away_equiv (e : S ⊗[R] M ≃ₗ[S] S) (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Nonempty (LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) := by
  let : Module.Finite S (S ⊗[R] M) := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let : Module.Flat S (S ⊗[R] M) := Module.Flat.of_linearEquiv e
  let : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  let : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  have hrank (q : PrimeSpectrum R) : Module.rankAtStalk M q = 1 := by
    obtain ⟨q', rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) q
    let : Nontrivial S := ⟨⟨1, 0, fun h => q'.isPrime.one_notMem (h ▸ q'.asIdeal.zero_mem)⟩⟩
    exact (Module.rankAtStalk_baseChange (M := M) q').symm.trans
      ((congrFun (Module.rankAtStalk_eq_of_equiv e) q').trans (congrFun Module.rankAtStalk_self q'))
  obtain ⟨r, hr, hf⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p.asIdeal
    (fun m _ => (hrank ⟨m, inferInstance⟩).trans (hrank p).symm)
  let : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hf
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ r]
    exact hr
  obtain ⟨q, hq⟩ := hp
  let : Nontrivial (Localization.Away r) := ⟨⟨1, 0, fun h => q.isPrime.one_notMem (h ▸ q.asIdeal.zero_mem)⟩⟩
  have h := Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers r) M) q
  rw [Module.rankAtStalk_eq_finrank_of_free, hq, hrank] at h
  refine ⟨r, hr, ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩⟩
  exact h.trans (Module.finrank_self (R := Localization.Away r)).symm

end PhilipponFaithfullyFlatRankOne
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct
open PhilipponTildeBaseChange

namespace PhilipponTildeRankOne
universe u
variable {R : Type u} [CommRing R]

private def pullback_trivialization {X Y Z : Scheme.{u}} {f : Z ⟶ X} {g : Y ⟶ X}
    (c : Y ≅ Z) (hc : c.hom ≫ f = g) (M : X.Modules)
    (k : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr hc.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp c.hom f).app M).symm ≪≫
    (Scheme.Modules.pullback c.hom).mapIso k ≪≫ Scheme.Modules.pullbackUnitIso c.hom

private def away_extends (M : ModuleCat.{u} R) (r : R)
    (e : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away r))).obj M ≅
      ModuleCat.of (Localization.Away r) (Localization.Away r) := by
  let D := Localization.Away r
  let f : R →+* D := algebraMap R D
  have e' : D ⊗[R] M ≃ₗ[D] D :=
    (LocalizedModule.isBaseChange (Submonoid.powers r) M).equiv.trans e
  let I : Module R D := Module.compHom D f
  let J : Module R D :=
    OreLocalization.instModuleOfIsScalarTower (R₀ := R) (R := R) (X := R)
      (S := Submonoid.powers r)
  have h : I = J := Module.ext' I J fun a x => by
    change f a * x = (a • x : Localization.Away r)
    exact (Algebra.smul_def a (x : Localization.Away r)).symm
  let tensorModule (E : Type u) [CommRing E] [Module R E] [SMulCommClass R E E] :
      ModuleCat.{u} E :=
    ModuleCat.of E (E ⊗[R] M)
  have hI : @SMulCommClass R D D I.toSMul inferInstance := ModuleCat.sMulCommClass_mk f D
  have hJ : @SMulCommClass R D D J.toSMul inferInstance := inferInstance
  have ht : ∀ (P Q : Module R D) (hc : @SMulCommClass R D D P.toSMul inferInstance)
      (hd : @SMulCommClass R D D Q.toSMul inferInstance), P = Q →
      @tensorModule D _ P hc = @tensorModule D _ Q hd := by
    intro P Q hc hd heq
    subst Q
    rfl
  have h' : (ModuleCat.extendScalars f).obj M = ModuleCat.of D (D ⊗[R] M) :=
    ht I J hI hJ h
  exact eqToIso h' ≪≫ (e'.toModuleIso : ModuleCat.of D (D ⊗[R] M) ≅ ModuleCat.of D D)

private def specAway_trivialization (M : ModuleCat.{u} R) (r : R)
    (e : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
        (tilde (R := CommRingCat.of R) M) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf := by
  let D := Localization.Away r
  let f : R →+* D := algebraMap R D
  exact (tildePullback f).app M ≪≫ (tilde.functor (CommRingCat.of D)).mapIso
    (away_extends M r e) ≪≫ tildeSelf

/-- A module free of rank one on principal neighborhoods gives an
invertible module on the actual affine scheme. -/
theorem invertible_tilde (M : ModuleCat.{u} R)
    (h : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧
      Nonempty (LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r)) :
    Scheme.Modules.IsInvertible (tilde (R := CommRingCat.of R) M) := by
  constructor
  intro x
  obtain ⟨r, hr, ⟨e⟩⟩ := h x
  let V : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r
  refine ⟨V, hr, ⟨?_⟩⟩
  exact pullback_trivialization (basicOpenIsoSpecAway (R := CommRingCat.of R) r)
    (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) r)
    (tilde (R := CommRingCat.of R) M) (specAway_trivialization M r e)

end PhilipponTildeRankOne
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory ModuleCat Opposite TensorProduct
open PhilipponTorsorSectionFibers PhilipponRankOneCoalgebra
open PhilipponAffineEtaleTorsorCocycle PhilipponTildeBaseChange

namespace PhilipponAffineEtaleTorsorModel
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The overlap cocycle of a torsor section over a faithfully flat affine
étale object has an effective rank-one module model. Its coaction is
retained, and its associated invertible module trivializes on that object. -/
theorem exists_model (f : R →+* S) [Etale (Spec.map (CommRingCat.ofHom f))]
    (hf : f.FaithfullyFlat) (A : Torsor (PhilipponKummerSequence.units (Spec (CommRingCat.of R))))
    (s : A.D.P.obj (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom f))))) :
    letI : Algebra R S := f.toAlgebra
    ∃ (h : IsDescentElement f (overlapUnit A s : S ⊗[R] S)) (M : ModuleCat.{u} R),
      Scheme.Modules.IsInvertible (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ∧
      Nonempty ((comparison f).obj M ≅ coalgebra f h) ∧
      Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f))).obj
        (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ≅
          SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf) := by
  let : Algebra R S := f.toAlgebra
  let : Module.FaithfullyFlat R S := hf
  have ht := overlapUnit_cocycle A s
  let h := PhilipponRankOneTensorCocycle.isDescentElement f (overlapUnit A s) ht.1 ht.2
  obtain ⟨M, ⟨e⟩⟩ := PhilipponRankOneCoalgebra.exists_model f hf h
  let d : (ModuleCat.extendScalars f).obj M ≅ freeOne S := (comonad f).forget.mapIso e
  have lin : S ⊗[R] M ≃ₗ[S] S := d.toLinearEquiv
  refine ⟨h, M, ?_, ⟨e⟩, ?_⟩
  · exact PhilipponTildeRankOne.invertible_tilde M (PhilipponFaithfullyFlatRankOne.exists_away_equiv lin)
  · exact ⟨(tildePullback f).app M ≪≫ (tilde.functor (CommRingCat.of S)).mapIso d ≪≫ tildeSelf⟩

end PhilipponAffineEtaleTorsorModel
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory ModuleCat TensorProduct
open PhilipponRankOneCoalgebra
open scoped ChangeOfRings

namespace PhilipponRankOneDescentCoordinates
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- A comparison isomorphism of coalgebras realizes its cocycle as the
change of the two coordinates of every base module section. -/
theorem coordinates_eq (f : R →+* S) (M : ModuleCat.{u} R) :
    letI : Algebra R S := f.toAlgebra
    ∀ {t : S ⊗[R] S} (h : IsDescentElement f t)
      (e : (comparison f).obj M ≅ coalgebra f h) (x : M),
      let d : (ModuleCat.extendScalars f).obj M ⟶ freeOne S := e.hom.f
      let y : S := d ((1 : S) ⊗ₜ[R,f] x)
      (1 : S) ⊗ₜ[R] y = (y ⊗ₜ[R] (1 : S)) * t := by
  let : Algebra R S := f.toAlgebra
  intro t h e x
  let m : (ModuleCat.extendScalars f).obj M := (1 : S) ⊗ₜ[R,f] x
  let d : (ModuleCat.extendScalars f).obj M ⟶ freeOne S := e.hom.f
  let y : S := d m
  have he := ConcreteCategory.congr_hom e.hom.h m
  change (TensorProduct.tmul R (M := S) (N := S) 1 y) = coaction f t y at he
  change (1 : S) ⊗ₜ[R] y = (y ⊗ₜ[R] (1 : S)) * t
  refine he.trans ((coaction_apply f t y).trans ?_)
  change (y • t : S ⊗[R] S) = _
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

end PhilipponRankOneDescentCoordinates
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponPullbackSectionMaps
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The map on sections given by the unit of inverse and direct image. -/
abbrev onSections (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U

theorem onSections_smul (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (a : Γ(M, U)) :
    onSections f M U (r • a) = f.app U r • onSections f M U a :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) r a

/-- The section map of an open immersion is an isomorphism over an open
contained in its image. -/
theorem onSections_isIso [IsOpenImmersion f] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (onSections f M U) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have h' := congrArg (fun a => Scheme.Modules.Hom.app a U) h
  change ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ (e.hom.app M).app (f ⁻¹ᵁ U) =
    onSections f M U at h'
  have hEq : f ''ᵁ (f ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hU
  have heq : (homOfLE (f.image_preimage_le U)) = eqToHom hEq := Subsingleton.elim _ _
  have hi : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, heq]
    infer_instance
  rw [← h']
  infer_instance

theorem onSections_naturality {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) :
    a.app U ≫ onSections f N U =
      onSections f M U ≫ ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  exact congrArg (fun k => Scheme.Modules.Hom.app k U) h

theorem onSections_restrict (M : Y.Modules) {U V : Y.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op ≫ onSections f M V = onSections f M U ≫
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i).op :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality i.op

/-- The section maps for successive pullbacks agree with the composite
via the canonical comparison of pullback functors. -/
theorem onSections_comp {Z : Scheme.{u}} (g : Z ⟶ X) (M : Y.Modules) (U : Y.Opens) :
    onSections (g ≫ f) M U = onSections f M U ≫
      onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
      ((Scheme.Modules.pullbackComp g f).hom.app M).app ((g ≫ f) ⁻¹ᵁ U) := by
  let F := Scheme.Modules.pullback f
  let adjF := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjG := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjC := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  let P := Scheme.Modules.pushforward (g ≫ f)
  let e := (Scheme.Modules.pullbackComp g f).app M
  have h := unit_conjugateEquiv (adjF.comp adjG) adjC (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  change (adjF.comp adjG).unit.app M ≫ (Scheme.Modules.pushforwardComp g f).hom.app
      ((F ⋙ Scheme.Modules.pullback g).obj M) = adjC.unit.app M ≫ P.map e.inv at h
  have h' := congrArg (fun k => k ≫ P.map e.hom) h
  simp only [Category.assoc] at h'
  rw [← P.map_comp, Iso.inv_hom_id, P.map_id] at h'
  have hh := congrArg (fun k => Scheme.Modules.Hom.app k U)
    (h'.trans (Category.comp_id (adjC.unit.app M)))
  rw [Adjunction.comp_unit_app] at hh
  let c := (e.hom).app ((g ≫ f) ⁻¹ᵁ U)
  let a := onSections f M U
  let b := onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
  simp only [adjC, adjF, adjG, F, P, e, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_map_app,
    Category.assoc] at hh
  change a ≫ b ≫ 𝟙 _ ≫ c = onSections (g ≫ f) M U at hh
  exact hh.symm.trans (congrArg (fun k => a ≫ b ≫ k) (Category.id_comp c))

end PhilipponPullbackSectionMaps
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct ModuleCat
open PhilipponTildeBaseChange PhilipponPullbackSectionMaps
open scoped ChangeOfRings

namespace PhilipponTildeBaseChangeSections
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The affine pullback comparison sends the base-change section of an
element to the section of its elementary tensor with one. -/
theorem comparison_on_generator (f : R →+* S) (M : ModuleCat.{u} R) (x : M) :
    (moduleSpecΓFunctor (R := CommRingCat.of S)).map ((tildePullback f).hom.app M)
      (onSections (Spec.map (CommRingCat.ofHom f)) (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
        ((tilde.isoTop (R := CommRingCat.of R) M).hom x)) =
    (tilde.isoTop (R := CommRingCat.of S) ((ModuleCat.extendScalars f).obj M)).hom
      ((1 : S) ⊗ₜ[R,f] x) := by
  let σ := Spec.map (CommRingCat.ofHom f)
  let a := tilde.adjunction (R := CommRingCat.of R)
  let b := Scheme.Modules.pullbackPushforwardAdjunction σ
  let d := ModuleCat.extendRestrictScalarsAdj f
  let c := tilde.adjunction (R := CommRingCat.of S)
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((a.comp b).ofNatIsoRight (pushforwardΓ f)) (d.comp c) M
  change ((a.comp b).unit.app M ≫ (pushforwardΓ f).hom.app _) ≫
    (moduleSpecΓFunctor (R := CommRingCat.of S) ⋙ ModuleCat.restrictScalars f).map
      ((tildePullback f).hom.app M) = (d.comp c).unit.app M at h
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact ConcreteCategory.congr_hom h x

end PhilipponTildeBaseChangeSections
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponTildeBaseChange PhilipponPullbackSectionMaps
open scoped ChangeOfRings

namespace PhilipponAffineFrameCoordinates
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

abbrev specMap (f : R →+* S) := Spec.map (CommRingCat.ofHom f)

def trivialization (f : R →+* S) {M : ModuleCat.{u} R}
    (d : (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of S S) :
    (Scheme.Modules.pullback (specMap f)).obj
      (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ≅
      SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf :=
  (tildePullback f).app M ≪≫ (tilde.functor (CommRingCat.of S)).mapIso d ≪≫ tildeSelf

private theorem isoTop_ring (z : S) :
    (tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S S)).hom z =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv z := rfl

/-- The scalar coordinate of a pulled-back base section is the coordinate
of its elementary tensor in the affine module model. -/
theorem coordinate_on_generator (f : R →+* S) {M : ModuleCat.{u} R}
    (d : (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of S S) (x : M) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
      ((trivialization f d).hom.app ⊤
        (onSections (specMap f) (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
          ((tilde.isoTop (R := CommRingCat.of R) M).hom x))) =
    d.hom ((1 : S) ⊗ₜ[R,f] x) := by
  let ΓS := moduleSpecΓFunctor (R := CommRingCat.of S)
  let v := onSections (specMap f) (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
    ((tilde.isoTop (R := CommRingCat.of R) M).hom x)
  let x' : (ModuleCat.extendScalars f).obj M := (1 : S) ⊗ₜ[R,f] x
  have h := PhilipponTildeBaseChangeSections.comparison_on_generator f M x
  let i := tilde.toTildeΓNatIso (R := CommRingCat.of S)
  have hn := ConcreteCategory.congr_hom (i.hom.naturality d.hom) x'
  change (tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S S)).hom (d.hom x') =
    ΓS.map ((tilde.functor (CommRingCat.of S)).map d.hom)
      ((tilde.isoTop (R := CommRingCat.of S) ((ModuleCat.extendScalars f).obj M)).hom x') at hn
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    (ΓS.map ((tilde.functor (CommRingCat.of S)).map d.hom)
      (ΓS.map ((tildePullback f).hom.app M) v)) = d.hom x'
  change ΓS.map ((tildePullback f).hom.app M) v =
    (tilde.isoTop (R := CommRingCat.of S) ((ModuleCat.extendScalars f).obj M)).hom x' at h
  rw [h, ← hn, isoTop_ring]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of S)).inv_hom_id (d.hom x')

/-- A module map out of the pullback of an affine associated sheaf
is determined by its values on the base module sections. -/
theorem hom_ext_of_generators {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (M : ModuleCat.{u} R) {N : X.Modules}
    {a b : (Scheme.Modules.pullback f).obj
      (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⟶ N}
    (h : ∀ x : M,
      a.app (f ⁻¹ᵁ ⊤)
          (onSections f (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
            ((tilde.isoTop (R := CommRingCat.of R) M).hom x)) =
        b.app (f ⁻¹ᵁ ⊤)
          (onSections f (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
            ((tilde.isoTop (R := CommRingCat.of R) M).hom x))) :
    a = b := by
  let d := Scheme.Modules.pullbackPushforwardAdjunction f
  let c := tilde.adjunction (R := CommRingCat.of R)
  apply ((c.comp d).homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit]
  exact h x

end PhilipponAffineFrameCoordinates
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponPullbackSectionMaps PhilipponAffineFrameCoordinates PhilipponFrameUnits

namespace PhilipponAffineFrameChange
universe u
variable {R : Type u} [CommRing R]

private abbrev multiply (X : Scheme.{u}) (a b : Γ(X, ⊤)) : Γ(X, ⊤) := a * b

private theorem unit_map (X : Scheme.{u}) (a : Aut (trivial X)) (v : Γ(X, ⊤)) :
    a.hom.app ⊤ v = multiply X v (unitAut X a).val := by
  let k := a.hom.val.app (op (⊤ : X.Opens))
  have h := k.hom.map_smul v (1 : Γ(X, ⊤))
  change k (multiply X v 1) = multiply X v (k (1 : Γ(X, ⊤))) at h
  change k v = multiply X v (k (1 : Γ(X, ⊤)))
  simpa only [multiply, mul_one] using h

/-- Rank-one coordinates on the base module generators determine the
change of frame, as an actual unit of the global sections. -/
theorem change_of_generators {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {M : ModuleCat.{u} R}
    (a b : (Scheme.Modules.pullback f).obj (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ≅
      trivial X) (t : (Γ(X, ⊤))ˣ)
    (h : ∀ x : M,
      let v : Γ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.tilde (R := CommRingCat.of R) M), ⊤) :=
        onSections f (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
          ((tilde.isoTop (R := CommRingCat.of R) M).hom x)
      b.hom.app ⊤ v = multiply X (a.hom.app ⊤ v) t.val) :
    differenceEquiv X b.symm a.symm = t := by
  let c := (unitAut X).symm t
  have hc : unitAut X c = t := (unitAut X).apply_symm_apply t
  have he : b.hom = a.hom ≫ c.hom := by
    apply hom_ext_of_generators f M
    intro x
    let v := onSections f (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
      ((tilde.isoTop (R := CommRingCat.of R) M).hom x)
    change b.hom.app ⊤ v = (a.hom ≫ c.hom).app ⊤ v
    rw [Scheme.Modules.Hom.comp_app]
    exact (h x).trans ((unit_map X c (a.hom.app ⊤ v)).trans
      (congrArg (fun w => multiply X (a.hom.app ⊤ v) w.val) hc)).symm
  have hIso : a.symm ≪≫ b = c := by
    apply Iso.ext
    change a.inv ≫ b.hom = c.hom
    rw [he, Iso.inv_hom_id_assoc]
  change unitAut X (a.symm ≪≫ b) = t
  rw [hIso, hc]

/-- The overlap unit can be computed in any identified coordinate ring. -/
theorem scalar_change_of_generators {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {M : ModuleCat.{u} R} {D : Type u} [CommRing D] (e : Γ(X, ⊤) ≅ CommRingCat.of D)
    (p q : trivial X ≅ (Scheme.Modules.pullback f).obj
      (AlgebraicGeometry.tilde (R := CommRingCat.of R) M)) (t : Dˣ)
    (h : ∀ x : M,
      let v := onSections f (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
        ((tilde.isoTop (R := CommRingCat.of R) M).hom x)
      e.hom (q.inv.app ⊤ v) = (e.hom (p.inv.app ⊤ v) : D) * t.val) :
    Units.map e.hom.hom.toMonoidHom (differenceEquiv X q p) = t := by
  let u : (Γ(X, ⊤))ˣ := Units.map e.inv.hom.toMonoidHom t
  have hu : Units.map e.hom.hom.toMonoidHom u = t := by
    apply Units.ext
    exact ConcreteCategory.congr_hom e.inv_hom_id t.val
  have hval : e.hom u.val = t.val := congrArg Units.val hu
  have he : differenceEquiv X q.symm.symm p.symm.symm = u := by
    apply change_of_generators f p.symm q.symm u
    intro x
    let v := onSections f (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) ⊤
      ((tilde.isoTop (R := CommRingCat.of R) M).hom x)
    let a : Γ(X, ⊤) := p.inv.app ⊤ v
    change q.inv.app ⊤ v = multiply X a u.val
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    calc
      _ = (e.hom a : D) * t.val := h x
      _ = (e.hom a : D) * e.hom u.val := congrArg (fun b : D => (e.hom a : D) * b) hval.symm
      _ = _ := (e.hom.hom.map_mul a u.val).symm
  exact (congrArg (Units.map e.hom.hom.toMonoidHom) (by simpa only [Iso.symm_symm_eq] using he)).trans hu

end PhilipponAffineFrameChange
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponFrameUnits PhilipponFramePullback PhilipponPullbackSectionMaps

namespace PhilipponFrameCoordinateRestriction
universe u
variable {X Y Z : Scheme.{u}}

private theorem unit_map (g : Z ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    (unitIso g).hom.app (g ⁻¹ᵁ U) (onSections g (trivial Y) U s) = g.app U s := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction g
  have h : a.homEquiv (trivial Y) (trivial Z) (unitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [a.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom (congrArg (fun t => Scheme.Modules.Hom.app t U) h) s

def restrictCoordinate (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y) :
    (Scheme.Modules.pullback (g ≫ f)).obj M ⟶ trivial Z :=
  (Scheme.Modules.pullbackComp g f).inv.app M ≫
    (Scheme.Modules.pullback g).map v ≫ (unitIso g).hom

/-- Coordinates of a pulled-back section restrict by the map of
structure sheaves. -/
theorem coordinate_restrict_section (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y) (U : X.Opens) (s : Γ(M, U)) :
    (restrictCoordinate f g v).app ((g ≫ f) ⁻¹ᵁ U)
        (onSections (g ≫ f) M U s) =
      g.app (f ⁻¹ᵁ U) (v.app (f ⁻¹ᵁ U) (onSections f M U s)) := by
  let W := (g ≫ f) ⁻¹ᵁ U
  let c := (Scheme.Modules.pullbackComp g f).app M
  have hc : c.hom.app W ≫ c.inv.app W = 𝟙 _ :=
    congrArg (fun t => Scheme.Modules.Hom.app t W) c.hom_inv_id
  have hs := onSections_comp f g M U
  have h : onSections (g ≫ f) M U ≫ (restrictCoordinate f g v).app W =
      onSections f M U ≫ v.app (f ⁻¹ᵁ U) ≫
        onSections g (trivial Y) (f ⁻¹ᵁ U) ≫ (unitIso g).hom.app W := by
    change onSections (g ≫ f) M U ≫ (restrictCoordinate f g v).app W = _
    rw [hs]
    change (onSections f M U ≫ onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
        c.hom.app W) ≫ (restrictCoordinate f g v).app W = _
    simp only [restrictCoordinate, Scheme.Modules.Hom.comp_app, Category.assoc]
    change onSections f M U ≫ onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
        c.hom.app W ≫ c.inv.app W ≫ _ = _
    rw [← Category.assoc (c.hom.app W), hc, Category.id_comp]
    erw [← reassoc_of% (onSections_naturality g v (f ⁻¹ᵁ U))]
  have hh := ConcreteCategory.congr_hom h s
  exact hh.trans (unit_map g (f ⁻¹ᵁ U) (v.app (f ⁻¹ᵁ U) (onSections f M U s)))

/-- Coordinate restriction with the composite identified with the given map. -/
theorem coordinate_restrict_section_of_eq (f : Y ⟶ X) (g : Z ⟶ Y) {k : Z ⟶ X}
    (h : g ≫ f = k) {M : X.Modules} (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y)
    (U : X.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).inv.app M ≫ restrictCoordinate f g v).app (k ⁻¹ᵁ U)
        (onSections k M U s) =
      Z.presheaf.map (eqToHom (congrArg (fun a : Z ⟶ X => a ⁻¹ᵁ U) h.symm)).op
        (g.app (f ⁻¹ᵁ U) (v.app (f ⁻¹ᵁ U) (onSections f M U s))) := by
  subst k
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, eqToHom_refl, op_id]
  exact (coordinate_restrict_section f g v U s).trans
    (ConcreteCategory.congr_hom (Z.presheaf.map_id (Opposite.op ((g ≫ f) ⁻¹ᵁ U))) _).symm

theorem coordinate_restrict_top_of_eq (f : Y ⟶ X) (g : Z ⟶ Y) {k : Z ⟶ X}
    (h : g ≫ f = k) {M : X.Modules} (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y)
    (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).inv.app M ≫ restrictCoordinate f g v).app ⊤
        (onSections k M ⊤ s) =
      g.appTop (v.app ⊤ (onSections f M ⊤ s)) := by
  subst k
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp]
  with_unfolding_all
    exact coordinate_restrict_section f g v ⊤ s

end PhilipponFrameCoordinateRestriction
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleFrameSections PhilipponFramePullback PhilipponPullbackSectionMaps
open PhilipponFrameCoordinateRestriction

namespace PhilipponEtaleFrameCoordinateRestriction
universe u
variable {X : Scheme.{u}} {M : X.Modules} {U V : X.Etale}

theorem restrict_inv (f : V ⟶ U) (p : Frame M U) :
    (restrict M f p).inv =
      (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)).inv.app M ≫
        restrictCoordinate U.hom f.left p.inv := by
  simp only [restrict, pullFrame, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    Iso.app_inv, Category.assoc, restrictCoordinate]

theorem restrict_inv_section (f : V ⟶ U) (p : Frame M U) (s : Γ(M, ⊤)) :
    (restrict M f p).inv.app ⊤ (onSections V.hom M ⊤ s) =
      f.left.appTop (p.inv.app ⊤ (onSections U.hom M ⊤ s)) := by
  rw [restrict_inv f p]
  exact coordinate_restrict_top_of_eq U.hom f.left (MorphismProperty.Over.w f) p.inv s

/-- Express the restriction formula in arbitrary scalar coordinates on
the global functions of the two charts. -/
theorem scalar_restricted_coordinate {S D : Type u} (f : V ⟶ U) (p : Frame M U) (s : Γ(M, ⊤))
    (d : Γ(V.left, ⊤) → D) (c : Γ(U.left, ⊤) → S) (i : S → D)
    (h : ∀ w : Γ(U.left, ⊤), d (f.left.appTop w) = i (c w))
    (x : S) (hx : c (p.inv.app ⊤ (onSections U.hom M ⊤ s)) = x) :
    d ((restrict M f p).inv.app ⊤ (onSections V.hom M ⊤ s)) = i x :=
  (congrArg d (restrict_inv_section f p s)).trans ((h _).trans (congrArg i hx))

/-- The frame-coordinate formula over an arbitrary open of the base. -/
theorem restrict_inv_section_on (f : V ⟶ U) (p : Frame M U) (W : X.Opens) (s : Γ(M, W)) :
    (restrict M f p).inv.app (V.hom ⁻¹ᵁ W) (onSections V.hom M W s) =
      V.left.presheaf.map (eqToHom (congrArg (fun a : V.left ⟶ X => a ⁻¹ᵁ W)
        (MorphismProperty.Over.w f).symm)).op
        (f.left.app (U.hom ⁻¹ᵁ W) (p.inv.app (U.hom ⁻¹ᵁ W) (onSections U.hom M W s))) := by
  rw [restrict_inv f p]
  exact coordinate_restrict_section_of_eq U.hom f.left (MorphismProperty.Over.w f) p.inv W s

theorem restrict_inv_section_of_coordinate (f : V ⟶ U) (p : Frame M U) (W : X.Opens)
    (s : Γ(M, W)) (a : Γ(X, W))
    (h : p.inv.app (U.hom ⁻¹ᵁ W) (onSections U.hom M W s) = U.hom.app W a) :
    (restrict M f p).inv.app (V.hom ⁻¹ᵁ W) (onSections V.hom M W s) = V.hom.app W a := by
  rw [restrict_inv_section_on f p W s, h]
  exact (ConcreteCategory.congr_hom
    (Scheme.Hom.congr_app (MorphismProperty.Over.w f).symm W) a).symm

end PhilipponEtaleFrameCoordinateRestriction
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleFrameSections PhilipponFramePullback PhilipponPullbackSectionMaps
open PhilipponAffineEtaleTorsorCocycle
open scoped ChangeOfRings

namespace PhilipponEtaleAffineFrameCoordinates
universe u

/-- Compute the frame transition on an overlap using coordinates on the
chart and on the overlap. The étale objects remain abstract in this step. -/
theorem scalar_change_of_restrictions {R S D : Type u} [CommRing R] [CommRing D]
    {M : ModuleCat.{u} R} {U V : (Spec (CommRingCat.of R)).Etale}
    (p : Frame (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) U)
    (a b : V ⟶ U) (c : Γ(U.left, ⊤) → S) (e : Γ(V.left, ⊤) ≅ CommRingCat.of D)
    (i j : S → D) (t : Dˣ)
    (hi : ∀ s : Γ(U.left, ⊤), e.hom (a.left.appTop s) = i (c s))
    (hj : ∀ s : Γ(U.left, ⊤), e.hom (b.left.appTop s) = j (c s))
    (coord : M → S)
    (hc : ∀ x : M,
      let L := AlgebraicGeometry.tilde (R := CommRingCat.of R) M
      c (p.inv.app ⊤ (onSections U.hom L ⊤ ((tilde.isoTop (R := CommRingCat.of R) M).hom x))) =
        coord x)
    (h : ∀ x : M, j (coord x) = i (coord x) * t.val) :
    let L := AlgebraicGeometry.tilde (R := CommRingCat.of R) M
    Units.map e.hom.hom.toMonoidHom
      (PhilipponFrameUnits.differenceEquiv V.left (restrict L b p) (restrict L a p)) = t := by
  let L := AlgebraicGeometry.tilde (R := CommRingCat.of R) M
  refine PhilipponAffineFrameChange.scalar_change_of_generators V.hom e
    (restrict L a p) (restrict L b p) t ?_
  intro x
  let s : Γ(L, ⊤) := (tilde.isoTop (R := CommRingCat.of R) M).hom x
  let v := onSections V.hom L ⊤ s
  have ha := PhilipponEtaleFrameCoordinateRestriction.scalar_restricted_coordinate
    a p s (fun z => e.hom z) c i hi (coord x) (hc x)
  have hb := PhilipponEtaleFrameCoordinateRestriction.scalar_restricted_coordinate
    b p s (fun z => e.hom z) c j hj (coord x) (hc x)
  change (e.hom ((restrict L b p).inv.app ⊤ v) : D) =
    (e.hom ((restrict L a p).inv.app ⊤ v) : D) * t.val
  exact hb.trans ((h x).trans (congrArg (fun z : D => z * t.val) ha.symm))

variable {R S D : Type u} [CommRing R] [CommRing S] [CommRing D] [Algebra R S] [Algebra R D]
  [Etale (baseMap R S)] [Etale (baseMap R D)]

/-- The inverse of a frame obtained from a scalar-extension isomorphism. -/
def frame {M : ModuleCat.{u} R}
    (d : (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S S) :
    Frame (AlgebraicGeometry.tilde (R := CommRingCat.of R) M) (obj R S) :=
  (PhilipponAffineFrameCoordinates.trivialization (algebraMap R S) d).symm

private theorem naturality_of_scalars (i : S →ₐ[R] D) (s : Γ((obj R S).left, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of D)).hom ((arrow i).left.appTop s) =
      i ((Scheme.ΓSpecIso (CommRingCat.of S)).hom s) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom i.toRingHom)) s

private theorem frame_coordinate {M : ModuleCat.{u} R}
    (d : (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S S)
    (x : M) :
    let L := AlgebraicGeometry.tilde (R := CommRingCat.of R) M
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
      ((frame d).inv.app ⊤ (onSections (obj R S).hom L ⊤
        ((tilde.isoTop (R := CommRingCat.of R) M).hom x))) =
      d.hom ((1 : S) ⊗ₜ[R,algebraMap R S] x) :=
  PhilipponAffineFrameCoordinates.coordinate_on_generator (algebraMap R S) d x

/-- Multiplicative comparison of the two scalar coordinates gives the
actual frame transition unit on the affine overlap. -/
theorem frame_transition_eq {M : ModuleCat.{u} R}
    (d : (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S S)
    (i j : S →ₐ[R] D) (t : Dˣ)
    (h : ∀ x : M, j (d.hom ((1 : S) ⊗ₜ[R,algebraMap R S] x)) =
      i (d.hom ((1 : S) ⊗ₜ[R,algebraMap R S] x)) * t.val) :
    let L := AlgebraicGeometry.tilde (R := CommRingCat.of R) M
    scalarUnits D (PhilipponFrameUnits.differenceEquiv (Spec (CommRingCat.of D))
      (restrict L (arrow j) (frame d)) (restrict L (arrow i) (frame d))) = t :=
  scalar_change_of_restrictions (U := obj R S) (V := obj R D) (frame d) (arrow i) (arrow j)
    (fun z => (Scheme.ΓSpecIso (CommRingCat.of S)).hom z) (Scheme.ΓSpecIso (CommRingCat.of D))
    i j t (naturality_of_scalars i) (naturality_of_scalars j)
    (fun x => d.hom ((1 : S) ⊗ₜ[R,algebraMap R S] x)) (frame_coordinate d) h

end PhilipponEtaleAffineFrameCoordinates
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponPresheafTorsorCompletion

namespace PhilipponTorsorMorphismExtension
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

theorem isLocallyInjective {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (h : ∀ U, Nonempty (P.obj U) → Function.Bijective (f.app U)) :
    Presheaf.IsLocallyInjective J f := by
  apply Presheaf.isLocallyInjective_of_injective J f
  intro U p q he
  exact (h U ⟨p⟩).injective he

theorem isLocallySurjective {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (hlocal : ∀ U, presence P U ∈ J U)
    (h : ∀ U, Nonempty (P.obj U) → Function.Bijective (f.app U)) :
    Presheaf.IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (hlocal U)
    intro V g hv
    exact (h (op V) hv).surjective (Q.map g.op s)

theorem equivalent_of_map {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G}
    (f : A.D.P ⟶ B.D.P)
    (hf : ∀ (U : Cᵒᵖ) (p q : A.D.P.obj U), B.D.diff U (f.app U p) (f.app U q) = A.D.diff U p q) :
    Equivalent A B := by
  have hb (U : Cᵒᵖ) : Nonempty (A.D.P.obj U) → Function.Bijective (f.app U) := by
    rintro ⟨p⟩
    exact bijective_of_section (D := A.D) (E := B.D) f U p (A.diff_bijective U p)
      (B.diff_bijective U (f.app U p)) (fun q => hf U q p)
  let A' : Sheaf J (Type w) := ⟨A.D.P, A.isSheaf⟩
  let B' : Sheaf J (Type w) := ⟨B.D.P, B.isSheaf⟩
  let φ : A' ⟶ B' := ⟨f⟩
  let : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso (A := Type w) φ).mp
    ⟨isLocallyInjective f hb, isLocallySurjective f A.locally_nonempty hb⟩
  exact ⟨(sheafToPresheaf J (Type w)).mapIso (asIso φ), hf⟩

variable [J.WEqualsLocallyBijective (Type w)]

/-- A map preserving differences extends along a locally bijective
comparison of section presheaves. -/
theorem exists_extension {G : Sheaf J AddCommGrpCat.{w}} {D E : Difference G.obj}
    {B : Torsor G} (η : D.P ⟶ E.P)
    (hlocal : ∀ U, presence D.P U ∈ J U)
    (hb : ∀ U, Nonempty (D.P.obj U) → Function.Bijective (η.app U))
    (hη : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), E.diff U (η.app U p) (η.app U q) = D.diff U p q)
    (k : D.P ⟶ B.D.P)
    (hk : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), B.D.diff U (k.app U p) (k.app U q) = D.diff U p q) :
    ∃ f : E.P ⟶ B.D.P,
      ∀ (U : Cᵒᵖ) (p q : E.P.obj U), B.D.diff U (f.app U p) (f.app U q) = E.diff U p q := by
  have hw : J.W η := (J.W_iff_isLocallyBijective η).mpr
    ⟨isLocallyInjective η hb, isLocallySurjective η hlocal hb⟩
  obtain ⟨f, hf⟩ := (hw B.D.P B.isSheaf).surjective k
  refine ⟨f, fun U x y => ?_⟩
  let G' : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj G
  apply (G'.property.isSheafFor _ (hlocal U.unop)).isSeparatedFor.ext
  intro V g hv
  obtain ⟨p, hp⟩ := (hb (op V) hv).surjective (E.P.map g.op x)
  obtain ⟨q, hq⟩ := (hb (op V) hv).surjective (E.P.map g.op y)
  change G.obj.map g.op (B.D.diff U (f.app U x) (f.app U y)) =
    G.obj.map g.op (E.diff U x y)
  have he (t : D.P.obj (op V)) : f.app (op V) (η.app (op V) t) = k.app (op V) t :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf (op V)) t
  rw [B.D.map_diff, E.map_diff, ← NatTrans.naturality_apply f g.op x,
    ← NatTrans.naturality_apply f g.op y, ← hp, ← hq, he p, he q, hk, hη]

/-- An equivariant map on locally available sections extends to the
associated torsor and determines an equivariant isomorphism. -/
theorem equivalent_of_local_map {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G}
    {D : Difference G.obj} (η : D.P ⟶ A.D.P)
    (hlocal : ∀ U, presence D.P U ∈ J U)
    (hb : ∀ U, Nonempty (D.P.obj U) → Function.Bijective (η.app U))
    (hη : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), A.D.diff U (η.app U p) (η.app U q) = D.diff U p q)
    (k : D.P ⟶ B.D.P)
    (hk : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), B.D.diff U (k.app U p) (k.app U q) = D.diff U p q) :
    Equivalent A B := by
  obtain ⟨f, hf⟩ := exists_extension η hlocal hb hη k hk
  exact equivalent_of_map f hf

end PhilipponTorsorMorphismExtension
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison

namespace PhilipponTorsorOverlapComparison
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G} {E : C}

def hits (E U : C) : Sieve U where
  arrows V _ := Nonempty (V ⟶ E)
  downward_closed h f := h.map (f ≫ ·)

variable (s : A.D.P.obj (op E)) (t : B.D.P.obj (op E))

/-- The unique comparison using the chosen sections over a single arrow. -/
private def atArrow {U : C} (a : U ⟶ E) (x : A.D.P.obj (op U)) : B.D.P.obj (op U) :=
  (B.diff_bijective (op U) (B.D.P.map a.op t)).surjective
    (A.D.diff (op U) x (A.D.P.map a.op s)) |>.choose

private theorem atArrow_diff {U : C} (a : U ⟶ E) (x : A.D.P.obj (op U)) :
    B.D.diff (op U) (atArrow s t a x) (B.D.P.map a.op t) =
      A.D.diff (op U) x (A.D.P.map a.op s) :=
  (B.diff_bijective (op U) (B.D.P.map a.op t)).surjective
    (A.D.diff (op U) x (A.D.P.map a.op s)) |>.choose_spec

private theorem atArrow_preserves {U : C} (a : U ⟶ E) (x y : A.D.P.obj (op U)) :
    B.D.diff (op U) (atArrow s t a x) (atArrow s t a y) = A.D.diff (op U) x y := by
  apply add_right_cancel (b := B.D.diff (op U) (atArrow s t a y) (B.D.P.map a.op t))
  rw [B.D.diff_add_diff, atArrow_diff, atArrow_diff, A.D.diff_add_diff]

private theorem atArrow_restrict {U V : C} (a : U ⟶ E) (f : V ⟶ U) (x : A.D.P.obj (op U)) :
    atArrow s t (f ≫ a) (A.D.P.map f.op x) = B.D.P.map f.op (atArrow s t a x) := by
  apply (B.diff_bijective (op V) (B.D.P.map (f ≫ a).op t)).injective
  change B.D.diff (op V) (atArrow s t (f ≫ a) (A.D.P.map f.op x)) (B.D.P.map (f ≫ a).op t) =
    B.D.diff (op V) (B.D.P.map f.op (atArrow s t a x)) (B.D.P.map (f ≫ a).op t)
  rw [atArrow_diff]
  simp only [op_comp, Functor.map_comp_apply, ← A.D.map_diff, ← B.D.map_diff, atArrow_diff]

variable (htransition : ∀ (U : C) (a b : U ⟶ E),
  A.D.diff (op U) (A.D.P.map a.op s) (A.D.P.map b.op s) =
    B.D.diff (op U) (B.D.P.map a.op t) (B.D.P.map b.op t))

include htransition in
private theorem atArrow_independent {U : C} (a b : U ⟶ E) (x : A.D.P.obj (op U)) :
    atArrow s t a x = atArrow s t b x := by
  apply (B.diff_bijective (op U) (B.D.P.map b.op t)).injective
  change B.D.diff (op U) (atArrow s t a x) (B.D.P.map b.op t) =
    B.D.diff (op U) (atArrow s t b x) (B.D.P.map b.op t)
  rw [← B.D.diff_add_diff (op U) (atArrow s t a x) (B.D.P.map a.op t),
    atArrow_diff, atArrow_diff, ← htransition U a b, A.D.diff_add_diff]

private def restricted (A : Torsor G) (E : C) : Difference G.obj where
  P :=
    { obj U := {x : A.D.P.obj U // Nonempty (U.unop ⟶ E)}
      map f := ↾fun x => ⟨A.D.P.map f x.val, x.property.map (f.unop ≫ ·)⟩
      map_id U := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Subtype.ext (by simp)
      map_comp f g := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Subtype.ext (by simp) }
  diff U x y := A.D.diff U x.val y.val
  diff_add_diff U x y z := A.D.diff_add_diff U x.val y.val z.val
  map_diff f x y := A.D.map_diff f x.val y.val

private def forgetArrow : (restricted A E).P ⟶ A.D.P where
  app _ := ↾Subtype.val
  naturality _ _ _ := rfl

private def comparison : (restricted A E).P ⟶ B.D.P where
  app _ := ↾fun x => atArrow s t x.property.some x.val
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    let y := (restricted A E).P.map f x
    change atArrow s t y.property.some (A.D.P.map f x.val) =
      B.D.P.map f (atArrow s t x.property.some x.val)
    exact (atArrow_independent s t htransition y.property.some (f.unop ≫ x.property.some) _).trans
      (atArrow_restrict s t x.property.some f.unop x.val)

include htransition in
/-- Torsors with matching transitions on a cover of the terminal object
are equivariantly isomorphic. -/
theorem equivalent_of_overlap [J.WEqualsLocallyBijective (Type w)]
    {T : C} (hT : IsTerminal T) (hcover : hits E T ∈ J T) : Equivalent A B := by
  refine PhilipponTorsorMorphismExtension.equivalent_of_local_map
    (D := restricted A E) forgetArrow (fun U => ?_) (fun U h => ?_) (fun _ _ _ => rfl)
    (comparison s t htransition) (fun U x y => ?_)
  · have ht : hits E U ∈ J U := J.pullback_stable (hT.from U) hcover
    apply J.superset_covering _ (J.intersection_covering (A.locally_nonempty U) ht)
    rintro V _ ⟨⟨x⟩, ha⟩
    exact ⟨⟨x, ha⟩⟩
  · obtain ⟨x⟩ := h
    exact ⟨fun _ _ h => Subtype.ext h, fun y => ⟨⟨y, x.property⟩, rfl⟩⟩
  · change B.D.diff U (atArrow s t x.property.some x.val) (atArrow s t y.property.some y.val) =
      A.D.diff U x.val y.val
    rw [atArrow_independent s t htransition y.property.some x.property.some y.val]
    exact atArrow_preserves s t x.property.some x.val y.val

end PhilipponTorsorOverlapComparison
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison
open PhilipponEtaleTorsorTransitions PhilipponTorsorOverlapComparison

namespace PhilipponEtaleTorsorOverlapComparison
universe u
variable {X : Scheme.{u}}

private abbrev terminalObject (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def terminal (X : Scheme.{u}) : IsTerminal (terminalObject X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- A surjective étale object covers the terminal object. -/
private theorem hits_cover (E : X.Etale) (hE : Function.Surjective E.hom.base) :
    hits E (terminalObject X) ∈ X.smallEtaleTopology (terminalObject X) := by
  let V : Unit → X.Etale := fun _ => E
  let f (i : Unit) : V i ⟶ terminalObject X :=
    MorphismProperty.Over.homMk E.hom (Category.comp_id E.hom) trivial
  have h : Sieve.ofArrows V f ∈ X.smallEtaleTopology (terminalObject X) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨y, hy⟩ := hE x
    exact ⟨(), y, hy⟩
  apply X.smallEtaleTopology.superset_covering _ h
  apply (Sieve.generate_le_iff _ _).mpr
  rintro U _ ⟨i⟩
  exact ⟨𝟙 E⟩

/-- Matching overlap units on one surjective étale object gives an
equivariant isomorphism of units torsors on the base. -/
theorem equivalent_of_equal_transitions (E : X.Etale) (hE : Function.Surjective E.hom.base)
    (A B : Torsor (PhilipponKummerSequence.units X))
    (s : A.D.P.obj (op E)) (t : B.D.P.obj (op E))
    (h : ∀ (V : X.Etale) (a b : V ⟶ E), transition A s a b = transition B t a b) :
    Equivalent A B :=
  equivalent_of_overlap s t (fun V a b => congrArg Additive.ofMul (h V a b))
    (terminal X) (hits_cover E hE)

theorem equivalent_of_equal_overlap (E : X.Etale) (hE : Function.Surjective E.hom.base)
    (A B : Torsor (PhilipponKummerSequence.units X))
    (s : A.D.P.obj (op E)) (t : B.D.P.obj (op E))
    (h : overlap A s ((terminal X).from E) = overlap B t ((terminal X).from E)) :
    Equivalent A B := by
  refine equivalent_of_equal_transitions E hE A B s t (fun U a b => ?_)
  let f := (terminal X).from E
  have hab : a ≫ f = b ≫ f := (terminal X).hom_ext _ _
  exact (overlap_pullback A s f a b hab).symm.trans
    ((congrArg (Units.map (pullback.lift a b hab).left.appTop.hom.toMonoidHom) h).trans
      (overlap_pullback B t f a b hab))

end PhilipponEtaleTorsorOverlapComparison
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison
open PhilipponAffineEtaleTorsorCocycle PhilipponEtaleTorsorTransitions

namespace PhilipponAffineTorsorOverlapRecognition
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Etale (baseMap R S)]

local notation "Base" => Spec (CommRingCat.of R)
local notation "Cover" => obj R S
local notation "Overlap" => obj R (S ⊗[R] S)
local notation "leftProjection" => arrow (leftFace : S →ₐ[R] S ⊗[R] S)
local notation "rightProjection" => arrow (rightFace : S →ₐ[R] S ⊗[R] S)

/-- Every pair of arrows to the affine étale cover factors through the
actual tensor-product spectrum by the two standard projections. -/
theorem factors {V : Scheme.Etale Base} (a b : V ⟶ Cover) :
    ∃ l : V ⟶ Overlap, l ≫ leftProjection = a ∧ l ≫ rightProjection = b := by
  let left : S →ₐ[R] S ⊗[R] S := leftFace
  let right : S →ₐ[R] S ⊗[R] S := rightFace
  have hp : IsPullback (specMap left) (specMap right) (baseMap R S) (baseMap R S) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R S S)
  have ha : a.left ≫ baseMap R S = V.hom := MorphismProperty.Over.w a
  have hb : b.left ≫ baseMap R S = V.hom := MorphismProperty.Over.w b
  let l := hp.lift a.left b.left (ha.trans hb.symm)
  have hleft : l ≫ specMap left = a.left := hp.lift_fst _ _ _
  have hright : l ≫ specMap right = b.left := hp.lift_snd _ _ _
  have hbase : l ≫ baseMap R (S ⊗[R] S) = V.hom := by
    rw [← specMap_over (R := R) left, ← Category.assoc, hleft]
    exact ha
  exact ⟨MorphismProperty.Over.homMk l hbase trivial,
    MorphismProperty.Over.Hom.ext hleft, MorphismProperty.Over.Hom.ext hright⟩

/-- Equality of the algebraic overlap units implies equality up to
equivariant isomorphism of the two étale sheaf torsors. -/
theorem equivalent_of_overlapUnit_eq (hcover : Function.Surjective (baseMap R S).base)
    (A B : Torsor (PhilipponKummerSequence.units Base))
    (s : A.D.P.obj (op Cover)) (t : B.D.P.obj (op Cover))
    (h : overlapUnit A s = overlapUnit B t) : Equivalent A B := by
  refine PhilipponEtaleTorsorOverlapComparison.equivalent_of_equal_transitions
    Cover hcover A B s t (fun V a b => ?_)
  have h' : transition A s leftProjection rightProjection =
      transition B t leftProjection rightProjection := by
    apply Units.ext
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).hom).injective
    exact congrArg Units.val h
  obtain ⟨k, hk₁, hk₂⟩ := factors a b
  have hm := congrArg (Units.map k.left.appTop.hom.toMonoidHom) h'
  rw [transition_restrict, transition_restrict, hk₁, hk₂] at hm
  exact hm

end PhilipponAffineTorsorOverlapRecognition
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison
open PhilipponEtaleFrameTorsor PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections

namespace PhilipponFramePresentationTransport
universe u
variable {X : Scheme.{u}} {M : X.Modules}

/-- An equivariant identification transports a comparison from frames to
the specified target torsor. -/
theorem exists_presentation (P : Presentation M)
    (A : Torsor (PhilipponKummerSequence.units X)) (h : Equivalent P.torsor A) :
    ∃ Q : Presentation M, Q.torsor = A := by
  obtain ⟨e, he⟩ := h
  let η : presheaf M ⟶ A.D.P := P.frames ≫ e.hom
  have hd (U : X.Etaleᵒᵖ) (p q : Frame M U.unop) :
      A.D.diff U (η.app U p) (η.app U q) = diff M U.unop p q :=
    (he U _ _).trans (P.diff_eq U p q)
  have hb (U : X.Etaleᵒᵖ) (hU : Nonempty (Frame M U.unop)) :
      Function.Bijective (η.app U) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app U)).comp (P.bijective U hU)
  exact ⟨⟨A, η, hd, hb⟩, rfl⟩

end PhilipponFramePresentationTransport
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponEtaleFrameTorsor PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections
open PhilipponEtaleTorsorTransitions

namespace PhilipponFramePresentationTransition
universe u
variable {X : Scheme.{u}} {M : X.Modules} {U V : X.Etale}

/-- The torsor comparison sends changes of frames to the transition units
of the image section. -/
theorem transition_frame (P : Presentation M) (p : Frame M U) (a b : V ⟶ U) :
    transition P.torsor (P.frames.app (op U) p) a b =
      PhilipponFrameUnits.differenceEquiv V.left (restrict M b p) (restrict M a p) := by
  have ha : P.torsor.D.P.map a.op (P.frames.app (op U) p) =
      P.frames.app (op V) (restrict M a p) := (NatTrans.naturality_apply P.frames a.op p).symm
  have hb : P.torsor.D.P.map b.op (P.frames.app (op U) p) =
      P.frames.app (op V) (restrict M b p) := (NatTrans.naturality_apply P.frames b.op p).symm
  change Additive.toMul (P.torsor.D.diff (op V)
    (P.torsor.D.P.map a.op (P.frames.app (op U) p))
    (P.torsor.D.P.map b.op (P.frames.app (op U) p))) = _
  rw [ha, hb, P.diff_eq]
  rfl

end PhilipponFramePresentationTransition
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory ModuleCat Opposite TensorProduct
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison
open PhilipponEtaleFrameTorsor PhilipponAffineEtaleTorsorCocycle
open PhilipponRankOneCoalgebra
open scoped ChangeOfRings

namespace PhilipponAffineTorsorEffectivity
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- A section on a faithfully flat affine étale cover produces an invertible
module with a presentation into the original torsor. -/
theorem exists_presentation_of_section (f : R →+* S) [Etale (Spec.map (CommRingCat.ofHom f))]
    (hf : f.FaithfullyFlat)
    (A : Torsor (PhilipponKummerSequence.units (Spec (CommRingCat.of R))))
    (s : A.D.P.obj (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom f))))) :
    ∃ (M : (Spec (CommRingCat.of R)).Modules) (_ : Scheme.Modules.IsInvertible M)
      (P : Presentation M), P.torsor = A := by
  let : Algebra R S := f.toAlgebra
  obtain ⟨h, N, hN, ⟨e⟩, _⟩ := PhilipponAffineEtaleTorsorModel.exists_model f hf A s
  let M := AlgebraicGeometry.tilde (R := CommRingCat.of R) N
  obtain ⟨P⟩ := nonempty_presentation M hN
  let d : (ModuleCat.extendScalars f).obj N ≅ ModuleCat.of S S :=
    (comonad f).forget.mapIso e
  let p := PhilipponEtaleAffineFrameCoordinates.frame (R := R) d
  let t := P.frames.app (op (obj R S)) p
  let i : S →ₐ[R] S ⊗[R] S := leftFace
  let j : S →ₐ[R] S ⊗[R] S := rightFace
  have he (x : N) :
      j (d.hom ((1 : S) ⊗ₜ[R,f] x)) =
        i (d.hom ((1 : S) ⊗ₜ[R,f] x)) * (overlapUnit A s : S ⊗[R] S) :=
    PhilipponRankOneDescentCoordinates.coordinates_eq f N h e x
  have hunit : overlapUnit P.torsor t = overlapUnit A s := by
    have H := PhilipponFramePresentationTransition.transition_frame P p (arrow i) (arrow j)
    exact (congrArg (scalarUnits (S ⊗[R] S)) H).trans
      (PhilipponEtaleAffineFrameCoordinates.frame_transition_eq d i j (overlapUnit A s) he)
  have hsur : Function.Surjective (baseMap R S).base :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hf).2.surj
  have hA : Equivalent P.torsor A :=
    PhilipponAffineTorsorOverlapRecognition.equivalent_of_overlapUnit_eq hsur P.torsor A t s hunit
  obtain ⟨P', hP'⟩ := PhilipponFramePresentationTransport.exists_presentation P A hA
  exact ⟨M, hN, P', hP'⟩

/-- Effective descent of the specified frame presentation over an affine spectrum. -/
theorem exists_presentation_spec (R : CommRingCat.{u})
    (A : Torsor (PhilipponKummerSequence.units (Spec R))) :
    ∃ (M : (Spec R).Modules) (_ : Scheme.Modules.IsInvertible M)
      (P : Presentation M), P.torsor = A := by
  obtain ⟨S, f, hEtale, hflat, ⟨s⟩⟩ := PhilipponAffineEtaleTorsorCover.exists_spec_cover R A
  exact exists_presentation_of_section f.hom hflat A s

end PhilipponAffineTorsorEffectivity
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u
open Opposite

theorem solution (R : CommRingCat.{u}) (A : Torsor (PhilipponKummerSequence.units (Spec R))) :
    ∃ (M : (Spec R).Modules) (_ : Scheme.Modules.IsInvertible M)
      (P : Presentation M), P.torsor = A := by
  exact PhilipponAffineTorsorEffectivity.exists_presentation_spec R A

#print axioms solution
