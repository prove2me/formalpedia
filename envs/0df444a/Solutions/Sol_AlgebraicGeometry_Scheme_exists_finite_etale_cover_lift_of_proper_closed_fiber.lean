-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_etale_cover_lift_of_proper_closed_fiber
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T17:44:43.402069+00:00
-- url     : https://prove2.me/submissions/03e34cd0-04c3-447f-8a3f-4126541cc71b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_approximable_henselian_stage_for_finite_etale_closed_fiber
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_etale_parameter_model_over_completion
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete

noncomputable section

section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericDimensionFormula
universe u

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h

end PhilipponGenericDimensionFormula

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponClosedFiberThickenings

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

private abbrev q (I : Ideal R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The base change of a scheme to a quotient of its affine base. -/
abbrev Fiber (I : Ideal R) := pullback (q I) f

private abbrev factorMap {I J : Ideal R} (h : I ≤ J) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))

private theorem factorMap_comp {I J : Ideal R} (h : I ≤ J) : factorMap h ≫ q I = q J := by
  rw [← Spec.map_comp]
  congr 1

/-- Transition from the base change along a larger ideal to that along a smaller one. -/
def transition {I J : Ideal R} (h : I ≤ J) : Fiber f J ⟶ Fiber f I :=
  pullback.lift (pullback.fst (q J) f ≫ factorMap h) (pullback.snd (q J) f) (by
    rw [Category.assoc, factorMap_comp, pullback.condition])

@[reassoc (attr := simp)]
theorem transition_fst {I J : Ideal R} (h : I ≤ J) :
    transition f h ≫ pullback.fst (q I) f = pullback.fst (q J) f ≫ factorMap h := by
  simp only [transition, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem transition_snd {I J : Ideal R} (h : I ≤ J) :
    transition f h ≫ pullback.snd (q I) f = pullback.snd (q J) f := by
  simp only [transition, pullback.lift_snd]

theorem transition_id (I : Ideal R) : transition f (le_refl I) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [transition_fst, Category.id_comp]
    have h : factorMap (le_refl I) = 𝟙 _ := by
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_refl I))) = _
      rw [Ideal.Quotient.factor_eq]
      exact Scheme.Spec.map_id _
    rw [h, Category.comp_id]
  · rw [transition_snd, Category.id_comp]

theorem transition_comp {I J K : Ideal R} (h : I ≤ J) (k : J ≤ K) :
    transition f k ≫ transition f h = transition f (h.trans k) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, transition_fst, transition_fst_assoc]
    rw [← Category.assoc, Category.assoc (pullback.fst (q K) f)]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (Ideal.Quotient.factor_comp h k)
  · simp only [Category.assoc, transition_snd]

private theorem transition_isPullback {I J : Ideal R} (h : I ≤ J) :
    IsPullback (pullback.fst (q J) f) (transition f h) (factorMap h) (pullback.fst (q I) f) := by
  have hOuter : IsPullback (pullback.fst (q J) f) (transition f h ≫ pullback.snd (q I) f)
      (factorMap h ≫ q I) f := by
    rw [transition_snd, factorMap_comp]
    exact IsPullback.of_hasPullback (q J) f
  exact IsPullback.of_bot hOuter (transition_fst f h).symm (IsPullback.of_hasPullback (q I) f)

instance {I J : Ideal R} (h : I ≤ J) : IsClosedImmersion (transition f h) := by
  apply MorphismProperty.of_isPullback (transition_isPullback f h)
  exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)

private theorem surjective_factorMap (I : Ideal R) (n : ℕ) :
    Surjective (factorMap (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))) := by
  let h : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
  constructor
  change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor h))
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _
    (Ideal.Quotient.factor_surjective h), PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.factor h (Ideal.Quotient.mk _ a) = 0 at hx
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact mem_nilradical.mpr ⟨n + 1, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hx _⟩

private theorem surjective_thickening (I : Ideal R) (n : ℕ) :
    Surjective (transition f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))) :=
  MorphismProperty.of_isPullback (transition_isPullback f _) (surjective_factorMap I n)

theorem surjective_transition_pow (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    Surjective (transition f (Ideal.pow_le_self (I := I) hn)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact surjective_thickening f I k

end PhilipponClosedFiberThickenings

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleThickeningModels

open PhilipponEtaleThickeningLifts

universe u v

private theorem isPullback_of_iSup_eq_top {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
    IsPullback fst snd f g := by
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U hU
  refine Scheme.isPullback_of_openCover fst snd f g 𝒰 fun i => ?_

  refine (h i).of_iso' (pullbackRestrictIsoRestrict fst (U i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    exact pullbackRestrictIsoRestrict_hom_morphismRestrict fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact pullbackRestrictIsoRestrict_hom_ι fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/- Adapted from the Prove2Me Fermat's Last Theorem gluing proof over an
affine nilpotent base. Here the thickening is a surjective closed immersion
of schemes with locally Noetherian target. -/

variable {X X₀ Y₀ : Scheme.{u}} (ι₀ : X₀ ⟶ X)
  [IsClosedImmersion ι₀] [Surjective ι₀] [IsLocallyNoetherian X]
  (q₀ : Y₀ ⟶ X₀)

structure Piece (V : Y₀.Opens) where
  Y : Scheme.{u}
  q : Y ⟶ X
  etale : Etale q
  j : (V : Scheme.{u}) ⟶ Y
  isPullback : IsPullback j (V.ι ≫ q₀) q (ι₀)

def Liftable (V : Y₀.Opens) : Prop := Nonempty (Piece ι₀ q₀ V)

omit [Surjective ι₀] [IsLocallyNoetherian X] in
theorem loc_exists [Etale q₀] (y : Y₀) : ∃ V : Y₀.Opens, y ∈ V ∧ Liftable ι₀ q₀ V := by
  obtain ⟨V₀, hy, V, qV, hV, jV, hpb⟩ := exists_local_model ι₀ q₀ y
  exact ⟨V₀, hy, ⟨⟨V, qV, hV, jV, hpb⟩⟩⟩

namespace Piece

variable {ι₀ q₀} {V : Y₀.Opens} (P : Piece ι₀ q₀ V)

instance isClosedImmersion_j : IsClosedImmersion P.j :=
  MorphismProperty.of_isPullback P.isPullback.flip inferInstance

instance surjective_j : Surjective P.j :=
  MorphismProperty.of_isPullback P.isPullback.flip inferInstance

instance locallyNoetherian_model : IsLocallyNoetherian P.Y :=
  have : Etale P.q := P.etale
  LocallyOfFiniteType.isLocallyNoetherian P.q

omit [IsLocallyNoetherian X] in
theorem isHomeomorph_j : IsHomeomorph P.j.base := by
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨P.j.isClosedEmbedding.isEmbedding, P.j.surjective⟩

def resOpens (V' : Y₀.Opens) : P.Y.Opens :=
  ⟨P.j.base '' ((V.ι ⁻¹ᵁ V' : (V : Scheme.{u}).Opens) : Set (V : Scheme.{u})),
    (P.isHomeomorph_j).isOpenMap _ (V.ι ⁻¹ᵁ V').2⟩

theorem preimage_resOpens (V' : Y₀.Opens) : P.j ⁻¹ᵁ (P.resOpens V') = V.ι ⁻¹ᵁ V' := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← P.j.isClosedEmbedding.injective hyx]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem range_preimage_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    Set.range ((P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι) = Set.range V'.ι := by
  rw [P.preimage_resOpens V', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy
    exact ⟨⟨y, h hy⟩, hy, rfl⟩

noncomputable def resIso {V' : Y₀.Opens} (h : V' ≤ V) :
    ((P.j ⁻¹ᵁ (P.resOpens V') : (V : Scheme.{u}).Opens) : Scheme.{u}) ≅ (V' : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq ((P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι) V'.ι (P.range_preimage_ι h)

theorem resIso_hom_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.resIso h).hom ≫ V'.ι = (P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem resIso_inv_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.resIso h).inv ≫ (P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι = V'.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

noncomputable def restrict {V' : Y₀.Opens} (h : V' ≤ V) : Piece ι₀ q₀ V' where
  Y := (P.resOpens V' : Scheme.{u})
  q := (P.resOpens V').ι ≫ P.q
  etale := by haveI := P.etale; infer_instance
  j := (P.resIso h).inv ≫ (P.j ∣_ P.resOpens V')
  isPullback := by
    have big := (isPullback_morphismRestrict P.j (P.resOpens V')).paste_vert P.isPullback
    refine big.of_iso (P.resIso h) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, ← Category.assoc, ← P.resIso_hom_ι h, Category.assoc]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

@[scoped simp] theorem restrict_Y {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict h).Y = (P.resOpens V' : Scheme.{u}) := rfl
@[scoped simp] theorem restrict_q {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict h).q = (P.resOpens V').ι ≫ P.q := rfl

theorem restrict_j_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict h).j ≫ (P.resOpens V').ι = Y₀.homOfLE h ≫ P.j := by
  show ((P.resIso h).inv ≫ (P.j ∣_ P.resOpens V')) ≫ (P.resOpens V').ι = Y₀.homOfLE h ≫ P.j
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι]
  exact P.resIso_inv_ι h

end Piece

theorem liftable_of_le {V V' : Y₀.Opens} (h : V' ≤ V) (hV : Liftable ι₀ q₀ V) :
    Liftable ι₀ q₀ V' :=
  ⟨(Classical.choice hV).restrict h⟩

abbrev Idx : Type u := {V : Y₀.Opens // Liftable ι₀ q₀ V}

scoped instance : Preorder (Idx ι₀ q₀) := Preorder.lift (fun V => V.1)

noncomputable def piece (V : Idx ι₀ q₀) : Piece ι₀ q₀ V.1 := Classical.choice V.2

theorem existsUnique_transition {V' V : Idx ι₀ q₀} (h : V' ≤ V) :
    ∃! φ : (piece ι₀ q₀ V').Y ⟶ (piece ι₀ q₀ V).Y,
      φ ≫ (piece ι₀ q₀ V).q = (piece ι₀ q₀ V').q ∧
      (piece ι₀ q₀ V').j ≫ φ = Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j := by
  haveI := (piece ι₀ q₀ V).etale
  refine existsUnique_lift (piece ι₀ q₀ V).q (piece ι₀ q₀ V').j (piece ι₀ q₀ V').q
    (Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j) ?_
  rw [Category.assoc, (piece ι₀ q₀ V).isPullback.w, (piece ι₀ q₀ V').isPullback.w,
    ← Scheme.homOfLE_ι Y₀ h]
  simp only [Category.assoc]

theorem transition_spec {V' V : Idx ι₀ q₀} (h : V' ≤ V) :
    (existsUnique_transition ι₀ q₀ h).choose ≫ (piece ι₀ q₀ V).q = (piece ι₀ q₀ V').q ∧
      (piece ι₀ q₀ V').j ≫ (existsUnique_transition ι₀ q₀ h).choose = Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j :=
  (existsUnique_transition ι₀ q₀ h).choose_spec.1

theorem transition_unique {V' V : Idx ι₀ q₀} (h : V' ≤ V)
    (φ : (piece ι₀ q₀ V').Y ⟶ (piece ι₀ q₀ V).Y)
    (h1 : φ ≫ (piece ι₀ q₀ V).q = (piece ι₀ q₀ V').q)
    (h2 : (piece ι₀ q₀ V').j ≫ φ = Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j) :
    φ = (existsUnique_transition ι₀ q₀ h).choose :=
  (existsUnique_transition ι₀ q₀ h).unique ⟨h1, h2⟩ (transition_spec ι₀ q₀ h)

noncomputable abbrev F : Idx ι₀ q₀ ⥤ Scheme.{u} where
  obj V := (piece ι₀ q₀ V).Y
  map h := (existsUnique_transition ι₀ q₀ h.le).choose
  map_id V := by
    symm
    refine transition_unique ι₀ q₀ le_rfl (𝟙 _) (Category.id_comp _) ?_
    rw [Category.comp_id]
    have : Y₀.homOfLE (le_refl V.1) = 𝟙 _ := by
      rw [← cancel_mono V.1.ι, Scheme.homOfLE_ι, Category.id_comp]
    rw [this, Category.id_comp]
  map_comp {V₁ V₂ V₃} h₁ h₂ := by
    symm
    obtain ⟨a1, a2⟩ := transition_spec ι₀ q₀ h₁.le
    obtain ⟨b1, b2⟩ := transition_spec ι₀ q₀ h₂.le
    refine transition_unique ι₀ q₀ (h₁ ≫ h₂).le _ ?_ ?_
    · rw [Category.assoc, b1, a1]
    · rw [← Category.assoc, a2, Category.assoc, b2, ← Category.assoc]
      congr 1
      rw [← cancel_mono V₃.1.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

namespace Piece

variable {ι₀ q₀}

theorem exists_iso {V : Y₀.Opens} (P Q : Piece ι₀ q₀ V) :
    ∃ e : P.Y ≅ Q.Y, e.hom ≫ Q.q = P.q ∧ P.j ≫ e.hom = Q.j := by
  haveI := P.etale
  haveI := Q.etale
  have wP := P.isPullback.w
  have wQ := Q.isPullback.w
  obtain ⟨α, ⟨hα1, hα2⟩, -⟩ := existsUnique_lift Q.q P.j P.q Q.j (by rw [wP, wQ])
  obtain ⟨β, ⟨hβ1, hβ2⟩, -⟩ := existsUnique_lift P.q Q.j Q.q P.j (by rw [wP, wQ])
  have hαβ : α ≫ β = 𝟙 _ :=
    (existsUnique_lift P.q P.j P.q P.j rfl).unique
      ⟨by rw [Category.assoc, hβ1, hα1], by rw [← Category.assoc, hα2, hβ2]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  have hβα : β ≫ α = 𝟙 _ :=
    (existsUnique_lift Q.q Q.j Q.q Q.j rfl).unique
      ⟨by rw [Category.assoc, hα1, hβ1], by rw [← Category.assoc, hβ2, hα2]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  exact ⟨⟨α, β, hαβ, hβα⟩, hα1, hα2⟩

end Piece

theorem F_map_isOpenImmersion {V' V : Idx ι₀ q₀} (h : V' ⟶ V) :
    IsOpenImmersion ((F ι₀ q₀).map h) := by
  obtain ⟨e, he1, he2⟩ :=
    Piece.exists_iso (piece ι₀ q₀ V') ((piece ι₀ q₀ V).restrict h.le)
  have key : (F ι₀ q₀).map h = e.hom ≫ ((piece ι₀ q₀ V).resOpens V'.1).ι := by
    symm
    refine transition_unique ι₀ q₀ h.le _ ?_ ?_
    · rw [Category.assoc]
      exact he1
    · rw [← Category.assoc, he2]
      exact (piece ι₀ q₀ V).restrict_j_ι h.le
  haveI h1 : IsOpenImmersion e.hom := inferInstance
  haveI h2 : IsOpenImmersion ((piece ι₀ q₀ V).resOpens V'.1).ι := inferInstance
  rw [key]
  exact MorphismProperty.comp_mem @IsOpenImmersion _ _ h1 h2

scoped instance {V' V : Idx ι₀ q₀} (h : V' ⟶ V) : IsOpenImmersion ((F ι₀ q₀).map h) :=
  F_map_isOpenImmersion ι₀ q₀ h

scoped instance : ((F ι₀ q₀) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj heq

  simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at xi xj heq ⊢
  change ((F ι₀ q₀).map fi).base xi = ((F ι₀ q₀).map fj).base xj at heq
  obtain ⟨yi, rfl⟩ := (piece ι₀ q₀ i).j.surjective xi
  obtain ⟨yj, rfl⟩ := (piece ι₀ q₀ j).j.surjective xj

  have sq : ∀ {V' V : Idx ι₀ q₀} (h : V' ⟶ V) (y : ↥(V'.1 : Scheme.{u})),
      ((F ι₀ q₀).map h).base ((piece ι₀ q₀ V').j.base y) =
        (piece ι₀ q₀ V).j.base ((Y₀.homOfLE h.le).base y) := by
    intro V' V h y
    have := (transition_spec ι₀ q₀ h.le).2
    have := congrArg (fun φ => φ.base y) this
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this
  rw [sq fi yi, sq fj yj] at heq
  have hy : ((Y₀.homOfLE fi.le).base yi) = ((Y₀.homOfLE fj.le).base yj) :=
    (piece ι₀ q₀ k).j.isClosedEmbedding.injective heq
  have hy1 : yi.1 = yj.1 := by
    have hι := congrArg (fun z : (k.1 : Scheme.{u}) => k.1.ι z) hy
    simpa only [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply] using hι

  let l : Idx ι₀ q₀ := ⟨i.1 ⊓ j.1, liftable_of_le ι₀ q₀ inf_le_left i.2⟩
  have hli : l ≤ i := show i.1 ⊓ j.1 ≤ i.1 from inf_le_left
  have hlj : l ≤ j := show i.1 ⊓ j.1 ≤ j.1 from inf_le_right
  let y : ↥(l.1 : Scheme.{u}) := ⟨yi.1, ⟨yi.2, hy1 ▸ yj.2⟩⟩
  refine ⟨l, homOfLE hli, homOfLE hlj, (piece ι₀ q₀ l).j.base y, ?_, ?_⟩
  · change ((F ι₀ q₀).map (homOfLE hli)).base ((piece ι₀ q₀ l).j.base y) = (piece ι₀ q₀ i).j.base yi
    rw [sq]
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ _)
  · change ((F ι₀ q₀).map (homOfLE hlj)).base ((piece ι₀ q₀ l).j.base y) = (piece ι₀ q₀ j).j.base yj
    rw [sq]
    congr 1
    exact Subtype.ext ((Scheme.homOfLE_apply _ _).trans hy1)

noncomputable abbrev Yg : Scheme.{u} := colimit (F ι₀ q₀)

noncomputable def qCocone : Cocone (F ι₀ q₀) where
  pt := X
  ι := { app := fun V => (piece ι₀ q₀ V).q
         naturality := fun {V' V} h => by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
           exact (transition_spec ι₀ q₀ h.le).1 }

noncomputable abbrev qg : Yg ι₀ q₀ ⟶ X := colimit.desc _ (qCocone ι₀ q₀)

@[scoped simp] theorem ι_qg (V : Idx ι₀ q₀) : colimit.ι (F ι₀ q₀) V ≫ qg ι₀ q₀ = (piece ι₀ q₀ V).q :=
  colimit.ι_desc _ _

private theorem iSup_opensRange : ⨆ V : Idx ι₀ q₀, (colimit.ι (F ι₀ q₀) V).opensRange = ⊤ :=
  (Scheme.IsLocallyDirected.openCover (F ι₀ q₀)).iSup_opensRange

theorem opensRange_ι (V : Idx ι₀ q₀) :
    (colimit.ι (F ι₀ q₀) V).opensRange.ι =
      (colimit.ι (F ι₀ q₀) V).isoOpensRange.inv ≫ colimit.ι (F ι₀ q₀) V :=
  ((Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι _).symm).symm

theorem etale_qg : Etale (qg ι₀ q₀) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale.{u}) _
    (iSup_opensRange ι₀ q₀) fun V => ?_
  rw [opensRange_ι, Category.assoc, ι_qg]
  have h1 : IsOpenImmersion (colimit.ι (F ι₀ q₀) V).isoOpensRange.inv := inferInstance
  have h1' : Etale (colimit.ι (F ι₀ q₀) V).isoOpensRange.inv := inferInstance
  exact MorphismProperty.comp_mem @Etale _ _ h1' (piece ι₀ q₀ V).etale

variable [Etale q₀]

noncomputable def coverY₀ : Y₀.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx ι₀ q₀) (fun V => (V.1 : Scheme.{u})) (fun V => V.1.ι) fun y => by
    obtain ⟨V, hy, hV⟩ := loc_exists ι₀ q₀ y
    exact ⟨⟨V, hV⟩, ⟨y, hy⟩, rfl⟩

omit [Etale q₀] in
theorem homOfLE_j_ι {u V : Idx ι₀ q₀} (h : u ≤ V) :
    Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V =
      (piece ι₀ q₀ u).j ≫ colimit.ι (F ι₀ q₀) u := by
  rw [← Category.assoc, ← (transition_spec ι₀ q₀ h).2, Category.assoc]
  congr 1
  exact colimit.w (F ι₀ q₀) (homOfLE h)

theorem j_compat (V W : Idx ι₀ q₀) :
    pullback.fst (V.1.ι) (W.1.ι) ≫ ((piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V) =
      pullback.snd (V.1.ι) (W.1.ι) ≫ ((piece ι₀ q₀ W).j ≫ colimit.ι (F ι₀ q₀) W) := by
  let u : Idx ι₀ q₀ := ⟨V.1 ⊓ W.1, liftable_of_le ι₀ q₀ inf_le_left V.2⟩
  have hP := isPullback_opens_inf V.1 W.1
  rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  have hl : u ≤ V := (inf_le_left : V.1 ⊓ W.1 ≤ V.1)
  have hr : u ≤ W := (inf_le_right : V.1 ⊓ W.1 ≤ W.1)
  exact (homOfLE_j_ι ι₀ q₀ hl).trans (homOfLE_j_ι ι₀ q₀ hr).symm

noncomputable abbrev jg : Y₀ ⟶ Yg ι₀ q₀ :=
  (coverY₀ ι₀ q₀).glueMorphisms (fun V => (piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V)
    (j_compat ι₀ q₀)

@[scoped simp] theorem ι_jg (V : Idx ι₀ q₀) :
    V.1.ι ≫ jg ι₀ q₀ = (piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V :=
  (coverY₀ ι₀ q₀).ι_glueMorphisms _ _ V

theorem ι_jg_qg (V : Idx ι₀ q₀) :
    V.1.ι ≫ (jg ι₀ q₀ ≫ qg ι₀ q₀) = V.1.ι ≫ (q₀ ≫ ι₀) := by
  have h1 := ι_jg ι₀ q₀ V
  have h2 := ι_qg ι₀ q₀ V
  have h3 := (piece ι₀ q₀ V).isPullback.w
  rw [← Category.assoc, h1, Category.assoc, h2, h3, Category.assoc]

theorem jg_w : jg ι₀ q₀ ≫ qg ι₀ q₀ = q₀ ≫ ι₀ :=
  Scheme.Cover.hom_ext (coverY₀ ι₀ q₀) _ _ fun V => ι_jg_qg ι₀ q₀ V

omit [Etale q₀] in
theorem F_map_j_apply {V' V : Idx ι₀ q₀} (h : V' ⟶ V) (y : (V'.1 : Scheme.{u})) :
    (F ι₀ q₀).map h ((piece ι₀ q₀ V').j y) = (piece ι₀ q₀ V).j (Y₀.homOfLE h.le y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ : (V'.1 : Scheme.{u}) ⟶ (piece ι₀ q₀ V).Y => φ y) (transition_spec ι₀ q₀ h.le).2

theorem jg_apply (V : Idx ι₀ q₀) (y : Y₀) (hy : y ∈ V.1) :
    jg ι₀ q₀ y = colimit.ι (F ι₀ q₀) V ((piece ι₀ q₀ V).j ⟨y, hy⟩) := by
  have h := congrArg (fun φ : (V.1 : Scheme.{u}) ⟶ Yg ι₀ q₀ => φ ⟨y, hy⟩) (ι_jg ι₀ q₀ V)
  exact h

theorem preimage_jg_opensRange (V : Idx ι₀ q₀) :
    jg ι₀ q₀ ⁻¹ᵁ (colimit.ι (F ι₀ q₀) V).opensRange = V.1 := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ : ∃ z, colimit.ι (F ι₀ q₀) V z = jg ι₀ q₀ y := hy
    obtain ⟨W₀, hyW, hW⟩ := loc_exists ι₀ q₀ y
    let W : Idx ι₀ q₀ := ⟨W₀, hW⟩
    rw [jg_apply ι₀ q₀ W y hyW] at hz
    obtain ⟨k, fk, fW, x, hxz, hxW⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F ι₀ q₀)).mp hz
    obtain ⟨y', rfl⟩ := (piece ι₀ q₀ k).j.surjective x
    rw [F_map_j_apply ι₀ q₀ fW y'] at hxW
    have hyy : Y₀.homOfLE fW.le y' = ⟨y, hyW⟩ := (piece ι₀ q₀ W).j.isClosedEmbedding.injective hxW
    have : (y'.1 : Y₀) = y := by
      obtain ⟨y'', hy''⟩ := y'
      rw [Scheme.homOfLE_apply'] at hyy
      exact congrArg Subtype.val hyy
    rw [← this]
    exact fk.le y'.2
  · intro hy
    show ∃ z, colimit.ι (F ι₀ q₀) V z = jg ι₀ q₀ y
    exact ⟨_, (jg_apply ι₀ q₀ V y hy).symm⟩

theorem isPullback_jg_local (V : Idx ι₀ q₀) :
    IsPullback (jg ι₀ q₀ ∣_ (colimit.ι (F ι₀ q₀) V).opensRange)
      ((jg ι₀ q₀ ⁻¹ᵁ (colimit.ι (F ι₀ q₀) V).opensRange).ι ≫ q₀)
      ((colimit.ι (F ι₀ q₀) V).opensRange.ι ≫ qg ι₀ q₀) (ι₀) := by
  refine (piece ι₀ q₀ V).isPullback.of_iso (Y₀.isoOfEq (preimage_jg_opensRange ι₀ q₀ V).symm)
    (colimit.ι (F ι₀ q₀) V).isoOpensRange (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (colimit.ι (F ι₀ q₀) V).opensRange.ι, Category.assoc, Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc, ι_jg]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ι_qg]
  · simp

theorem isPullback_jg : IsPullback (jg ι₀ q₀) q₀ (qg ι₀ q₀) (ι₀) := by
  exact isPullback_of_iSup_eq_top _ _ _ _ (fun V => (colimit.ι (F ι₀ q₀) V).opensRange)
    (iSup_opensRange ι₀ q₀) (isPullback_jg_local ι₀ q₀)


/-- Every étale object of a closed thickening of a locally Noetherian scheme
comes from an étale object over the original scheme. -/
theorem exists_model :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X) (_ : Etale q) (j : Y₀ ⟶ Y),
      IsPullback j q₀ q ι₀ :=
  ⟨Yg ι₀ q₀, qg ι₀ q₀, etale_qg ι₀ q₀, jg ι₀ q₀, isPullback_jg ι₀ q₀⟩

end PhilipponEtaleThickeningModels

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedFiberCovers (eq_univ_of_contains_closedFiber)
open PhilipponEtaleClosedFiberSections (closedFiberι)


namespace PhilipponFiniteEtaleClosedFiberEffectivity

universe u

/-- For a source-local property of a morphism whose source is proper over a
local ring, it suffices to verify the property near the closed fiber. -/
theorem property_of_near_closedFiber {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g] (f : X ⟶ Y)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h : ∀ x : X, g x = IsLocalRing.closedPoint A → ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f)) :
    P f := by
  let I := {U : X.Opens // P (U.ι ≫ f)}
  have hUniv : (⋃ i : I, (i.1 : Set X)) = Set.univ :=
    eq_univ_of_contains_closedFiber g (isOpen_iUnion fun i => i.1.2) (fun x hx => by
      obtain ⟨U, hxU, hU⟩ := h x hx
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  let 𝒰 : X.OpenCover := {
    I₀ := I
    X i := i.1.toScheme
    f i := i.1.ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, inferInstance⟩
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hUniv x)
      exact ⟨i, ⟨x, hx⟩, rfl⟩ }
  exact (IsZariskiLocalAtSource.iff_of_openCover (P := P) 𝒰).mpr fun i => i.2

/-- A finite model of a closed-fiber chart gives a finite étale lift once
étaleness is verified in neighborhoods of the closed fiber of the model. -/
theorem of_finite_model {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g] (f : Y ⟶ X) [IsFinite f]
    (V : (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g).Etale)
    (e : pullback f (closedFiberι g) ≅ V.left)
    (he : e.hom ≫ V.hom = pullback.snd f (closedFiberι g))
    (h : ∀ y : Y, g (f y) = IsLocalRing.closedPoint A →
      ∃ U : Y.Opens, y ∈ U ∧ Etale (U.ι ≫ f)) :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange (closedFiberι g)).obj W ≅ V) := by
  let : Etale f := property_of_near_closedFiber (f ≫ g) f @Etale h
  let W := Scheme.Etale.mk f
  exact ⟨W, inferInstanceAs (IsFinite f), ⟨MorphismProperty.Over.isoMk e he⟩⟩

/-- Lifting in the canonical closed-fiber pullback implies lifting in any
square that presents that fiber. -/
theorem of_canonical_fiber {A : Type u} [CommRing A] [IsLocalRing A]
    {X T : Scheme.{u}} (g : X ⟶ Spec (.of A))
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ X)
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (H : ∀ V : (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g).Etale,
      IsFinite V.hom → ∃ W : X.Etale, IsFinite W.hom ∧
        Nonempty ((baseChange (closedFiberι g)).obj W ≅ V))
    (V : T.Etale) [IsFinite V.hom] :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange j).obj W ≅ V) := by
  let r := closedFiberι g
  let k := h.isoPullback
  have hk : k.hom ≫ r = j := h.isoPullback_hom_snd
  let V' := Scheme.Etale.mk (V.hom ≫ k.hom)
  obtain ⟨W, hW, ⟨d⟩⟩ := H V' (inferInstanceAs (IsFinite (V.hom ≫ k.hom)))
  have hd : d.hom.left ≫ V.hom ≫ k.hom = pullback.snd W.hom r := MorphismProperty.Over.w d.hom
  have h' : IsPullback (pullback.fst W.hom j) (pullback.snd W.hom j ≫ k.hom) W.hom r :=
    (IsPullback.of_hasPullback W.hom j).of_iso (Iso.refl _) (Iso.refl _) k (Iso.refl _)
      (by simp) (by rw [Iso.refl_hom, Category.id_comp]) (by simp) (by simpa only [Iso.refl_hom, Category.comp_id] using hk.symm)
  let d' := (Scheme.Etale.forget _ ⋙ Over.forget _).mapIso d
  let a := h'.isoPullback ≪≫ d'
  refine ⟨W, hW, ⟨MorphismProperty.Over.isoMk a ?_⟩⟩
  apply (cancel_mono k.hom).mp
  change (h'.isoPullback.hom ≫ d.hom.left) ≫ V.hom ≫ k.hom = pullback.snd W.hom j ≫ k.hom
  rw [Category.assoc, hd, h'.isoPullback_hom_snd]

/-- Étale charts over a locally Noetherian scheme have unique map lifts
across a surjective closed immersion. -/
theorem existsUnique_map_lift {X T : Scheme.{u}} [IsLocallyNoetherian X]
    (i : T ⟶ X) [IsClosedImmersion i] [Surjective i] {U V : X.Etale}
    (a : (baseChange i).obj U ⟶ (baseChange i).obj V) :
    ∃! b : U ⟶ V, (baseChange i).map b = a := by
  let u := pullback.fst U.hom i
  let v := pullback.fst V.hom i
  let : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian (Y := X) U.hom
  let : IsClosedImmersion u := inferInstanceAs (IsClosedImmersion (pullback.fst U.hom i))
  let : Surjective u := inferInstanceAs (Surjective (pullback.fst U.hom i))
  have ha : a.left ≫ pullback.snd V.hom i = pullback.snd U.hom i := MorphismProperty.Over.w a
  have hs : (a.left ≫ v) ≫ V.hom = u ≫ U.hom := by
    change (a.left ≫ pullback.fst V.hom i) ≫ V.hom = pullback.fst U.hom i ≫ U.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, ← pullback.condition]
  obtain ⟨b, ⟨hb, hbu⟩, huniq⟩ :=
    PhilipponEtaleThickeningLifts.existsUnique_lift (T := U.left) V.hom u U.hom (a.left ≫ v) hs
  let c : U ⟶ V := MorphismProperty.Over.homMk b hb
  refine ⟨c, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact (map_isPullback i c).w.symm.trans hbu
    · exact (MorphismProperty.Over.w ((baseChange i).map c)).trans ha.symm
  · intro d hd
    apply MorphismProperty.Over.Hom.ext
    apply huniq d.left
    refine ⟨MorphismProperty.Over.w d, (map_isPullback i d).w.trans ?_⟩
    exact congrArg (fun m => m.left ≫ v) hd

/-- Base change across a surjective closed immersion of a locally
Noetherian base is fully faithful on the small étale site. -/
def baseChangeFullyFaithful {X T : Scheme.{u}} [IsLocallyNoetherian X]
    (i : T ⟶ X) [IsClosedImmersion i] [Surjective i] : (baseChange i).FullyFaithful :=
  ((Functor.FullyFaithful.nonempty_iff_map_bijective (baseChange i)).mpr (by
    intro U V
    constructor
    · intro a b hab
      obtain ⟨c, _, hc⟩ := existsUnique_map_lift i ((baseChange i).map b)
      exact (hc a hab).trans (hc b rfl).symm
    · intro a
      obtain ⟨b, hb, _⟩ := existsUnique_map_lift i a
      exact ⟨b, hb⟩)).some

/-- Between étale charts, an open immersion on the thickened fiber
lifts to an open immersion of the charts. -/
theorem isOpenImmersion_of_baseChange {X T : Scheme.{u}} [IsLocallyNoetherian X]
    (i : T ⟶ X) [IsClosedImmersion i] [Surjective i] {U V : X.Etale} (a : U ⟶ V)
    [IsOpenImmersion ((baseChange i).map a).left] : IsOpenImmersion a.left := by
  let K := Scheme.Etale.forget T ⋙ Over.forget T
  let : Mono (K.map ((baseChange i).map a)) := inferInstanceAs (Mono ((baseChange i).map a).left)
  let : Mono ((baseChange i).map a) := K.mono_of_mono_map inferInstance
  let := (baseChangeFullyFaithful i).faithful
  let : Mono a := (baseChange i).mono_of_mono_map inferInstance
  let J := Scheme.Etale.forget X ⋙ Over.forget X
  let : PreservesLimitsOfShape WalkingCospan J := by dsimp [J]; infer_instance
  let : Mono a.left := show Mono (J.map a) from Functor.map_mono J a
  exact IsOpenImmersion.of_flat_of_mono a.left

/-- An open subscheme of the pullback of an étale chart along a surjective
closed immersion is obtained by pulling back an open subscheme of the chart. -/
theorem exists_open_model {X T : Scheme.{u}} (i : T ⟶ X) [IsClosedImmersion i] [Surjective i]
    (V : X.Etale) (U : (pullback V.hom i).Opens) :
    ∃ O : V.left.Opens, Nonempty
      ((baseChange i).obj (Scheme.Etale.mk (O.ι ≫ V.hom)) ≅
        Scheme.Etale.mk (U.ι ≫ pullback.snd V.hom i)) := by
  let p := pullback.fst V.hom i
  let : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst V.hom i))
  let : Surjective p := inferInstanceAs (Surjective (pullback.fst V.hom i))
  let e := p.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective p.surjective
  let O : V.left.Opens := ⟨e.symm ⁻¹' U.1, U.2.preimage e.symm.continuous⟩
  have h : p ⁻¹ᵁ O = U := by
    ext x
    change e.symm (e x) ∈ U ↔ x ∈ U
    rw [e.symm_apply_apply]
  refine ⟨O, ?_⟩
  rw [← h]
  have hpb := (isPullback_morphismRestrict p O).paste_vert (IsPullback.of_hasPullback V.hom i)
  exact ⟨MorphismProperty.Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd⟩

end PhilipponFiniteEtaleClosedFiberEffectivity

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponFiniteEtaleClosedFiberEffectivity (baseChangeFullyFaithful)
open PhilipponGenericDimensionFormula (isIso_residueFieldMap_of_isPreimmersion)
open PhilipponClosedFiberThickenings (Fiber transition transition_id transition_comp surjective_transition_pow)


namespace PhilipponFiniteEtaleThickenings

universe u

private theorem finite_fiber_of_thickening {X T Y Z : Scheme.{u}}
    {i : T ⟶ X} [IsClosedImmersion i] {f : Y ⟶ X} {p : Z ⟶ T} [IsFinite p]
    {j : Z ⟶ Y} (h : IsPullback j p f i) (x : T) :
    IsFinite (f.fiberToSpecResidueField (i x)) := by
  let r := T.fromSpecResidueField x
  let s := X.fromSpecResidueField (i x)
  let k := Spec.map (i.residueFieldMap x)
  let : IsIso (i.residueFieldMap x) := isIso_residueFieldMap_of_isPreimmersion i x
  let : IsIso k := inferInstanceAs (IsIso (Spec.map (i.residueFieldMap x)))
  have hk : k ≫ s = r ≫ i := i.SpecMap_residueFieldMap_fromSpecResidueField x
  have hp : IsPullback (pullback.fst p r ≫ j) (pullback.snd p r ≫ k) f s :=
    ((IsPullback.of_hasPullback p r).paste_horiz h).of_iso
      (Iso.refl _) (Iso.refl _) (asIso k) (Iso.refl _)
      (by simp) (Category.id_comp _).symm (by simp)
      ((Category.comp_id _).trans hk.symm)
  let e := hp.isoPullback
  have he : e.hom ≫ pullback.snd f s = pullback.snd p r ≫ k := hp.isoPullback_hom_snd
  have hFin : IsFinite (e.hom ≫ pullback.snd f s) := by
    rw [he]
    exact inferInstanceAs (IsFinite (pullback.snd p r ≫ k))
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom _).mp hFin

/-- An étale morphism is finite if its pullback to a surjective closed
thickening of the base is finite. -/
theorem isFinite_of_thickening {X T Y Z : Scheme.{u}}
    {i : T ⟶ X} [IsClosedImmersion i] [Surjective i] {f : Y ⟶ X} [Etale f]
    {p : Z ⟶ T} [IsFinite p] {j : Z ⟶ Y} (h : IsPullback j p f i) : IsFinite f := by
  let : IsClosedImmersion j := MorphismProperty.of_isPullback h.flip inferInstance
  let : Surjective j := MorphismProperty.of_isPullback h.flip inferInstance
  let : IsProper (j ≫ f) := h.w ▸ inferInstanceAs (IsProper (p ≫ i))
  let : UniversallyClosed f := UniversallyClosed.of_comp_surjective j f
  have hDiag : IsClosedMap (pullback.diagonal f) := by
    apply IsClosedMap.of_comp_surjective j.surjective j.continuous
    change IsClosedMap (j ≫ pullback.diagonal f)
    rw [pullback.comp_diagonal]
    have hMap := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (f := j ≫ f) (g := j ≫ f) (f' := f) (g' := f) (i₁ := j) (i₂ := j)
      inferInstance inferInstance rfl rfl
    exact hMap.isClosedEmbedding.isClosedMap.comp
      (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosedMap
  let : IsSeparated f := ⟨IsClosedImmersion.of_isPreimmersion _ hDiag.isClosed_range⟩
  let : IsProper f := { }
  let : LocallyQuasiFinite f := .of_fiberToSpecResidueField f fun x => by
    obtain ⟨x₀, rfl⟩ := i.surjective x
    let : IsFinite (f.fiberToSpecResidueField (i x₀)) := finite_fiber_of_thickening h x₀
    infer_instance
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- Finite étale charts lift across surjective closed immersions with
locally Noetherian target. -/
theorem exists_finiteEtale_model {X T : Scheme.{u}} [IsLocallyNoetherian X]
    (i : T ⟶ X) [IsClosedImmersion i] [Surjective i] (V : T.Etale) [IsFinite V.hom] :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange i).obj W ≅ V) := by
  obtain ⟨Y, f, hF, j, h⟩ := PhilipponEtaleThickeningModels.exists_model i V.hom
  let : Etale f := hF
  refine ⟨Scheme.Etale.mk f, isFinite_of_thickening h, ?_⟩
  exact ⟨MorphismProperty.Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd⟩

/-- Two étale lifts of the same chart on a thickening are isomorphic
by a map inducing the prescribed identity on the common reduction. -/
theorem exists_iso_of_common_reduction {X T Y Z B : Scheme.{u}} [IsLocallyNoetherian X]
    (i : T ⟶ X) [IsClosedImmersion i] [Surjective i]
    {p : B ⟶ T} [Etale p] {f : Y ⟶ X} [Etale f] {g : Z ⟶ X} [Etale g]
    {a : B ⟶ Y} {b : B ⟶ Z} (ha : IsPullback a p f i) (hb : IsPullback b p g i) :
    ∃ e : Y ≅ Z, e.hom ≫ g = f ∧ a ≫ e.hom = b := by
  let A := Scheme.Etale.mk f
  let D := Scheme.Etale.mk g
  let P := Scheme.Etale.mk p
  let F := baseChange i
  let hF := baseChangeFullyFaithful i
  let ea : P ≅ F.obj A := MorphismProperty.Over.isoMk ha.isoPullback ha.isoPullback_hom_snd
  let eb : P ≅ F.obj D := MorphismProperty.Over.isoMk hb.isoPullback hb.isoPullback_hom_snd
  let d := hF.preimageIso (ea.symm ≪≫ eb)
  let e := (Scheme.Etale.forget X ⋙ Over.forget X).mapIso d
  have hd : F.map d.hom = ea.inv ≫ eb.hom := hF.map_preimage _
  have hae : ea.hom.left ≫ pullback.fst f i = a := ha.isoPullback_hom_fst
  have hbe : eb.hom.left ≫ pullback.fst g i = b := hb.isoPullback_hom_fst
  have hcomm : ea.hom ≫ F.map d.hom = eb.hom := by
    rw [hd, Iso.hom_inv_id_assoc]
  have hd' : pullback.fst f i ≫ d.hom.left = (F.map d.hom).left ≫ pullback.fst g i :=
    (map_isPullback i d.hom).w
  refine ⟨e, MorphismProperty.Over.w d.hom, ?_⟩
  change a ≫ d.hom.left = b
  rw [← hae, Category.assoc, hd', ← Category.assoc]
  exact (congrArg (fun t => t.left ≫ pullback.fst g i) hcomm).trans hbe

/-- A map between étale models that agrees with the identifications on the
common reduction is a base-change map. -/
theorem isPullback_of_compatible_reductions {X T S Y Z B : Scheme.{u}}
    [IsLocallyNoetherian X] {i : S ⟶ X} [IsClosedImmersion i] [Surjective i] {t : X ⟶ T}
    {p : B ⟶ S} [Etale p] {f : Y ⟶ X} [Etale f] {g : Z ⟶ T} [Etale g]
    {a : B ⟶ Y} {b : B ⟶ Z} (ha : IsPullback a p f i) (hb : IsPullback b p g (i ≫ t))
    {m : Y ⟶ Z} (hm : m ≫ g = f ≫ t) (hm₀ : a ≫ m = b) : IsPullback m f g t := by
  let k := pullback.lift b (p ≫ i) (by rw [Category.assoc, ← hb.w])
  have kfst : k ≫ pullback.fst g t = b := pullback.lift_fst ..
  have ksnd : k ≫ pullback.snd g t = p ≫ i := pullback.lift_snd ..
  have hk : IsPullback k p (pullback.snd g t) i := by
    apply IsPullback.of_right _ ksnd (IsPullback.of_hasPullback g t)
    rw [kfst]
    exact hb
  obtain ⟨e, he, he₀⟩ := exists_iso_of_common_reduction i ha hk
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsClosedImmersion a := MorphismProperty.of_isPullback ha.flip inferInstance
  let : Surjective a := MorphismProperty.of_isPullback ha.flip inferInstance
  have hcomp : b ≫ g = a ≫ f ≫ t := by rw [hb.w, ← Category.assoc, ← ha.w, Category.assoc]
  have heq : e.hom ≫ pullback.fst g t = m :=
    (PhilipponEtaleThickeningLifts.existsUnique_lift g a (f ≫ t) b hcomp).unique
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, he],
        by rw [← Category.assoc, he₀, kfst]⟩ ⟨hm, hm₀⟩
  exact IsPullback.of_iso_pullback ⟨hm⟩ e heq he

section System

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) (I : Ideal A)

/-- The base change of `X` along the quotient by `I ^ (n + 1)`. -/
abbrev Thickening (n : ℕ) := Fiber g (I ^ (n + 1))

abbrev fromClosed (n : ℕ) : Fiber g I ⟶ Thickening g I n :=
  transition g (Ideal.pow_le_self (Nat.succ_ne_zero n))

abbrev stageMap {m n : ℕ} (h : m ≤ n) : Thickening g I m ⟶ Thickening g I n :=
  transition g (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

private theorem fromClosed_stageMap {m n : ℕ} (h : m ≤ n) :
    fromClosed g I m ≫ stageMap g I h = fromClosed g I n := transition_comp g _ _

private theorem stageMap_id (n : ℕ) : stageMap g I (le_refl n) = 𝟙 _ :=
  transition_id g _

private theorem stage_noetherian [IsLocallyNoetherian X] (n : ℕ) :
    IsLocallyNoetherian (Thickening g I n) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
  let : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q g)

/-- A compatible system of finite étale models of a chart over `X × Spec(A/I)`. -/
structure CompatibleModels (V : (Fiber g I).Etale) where
  model (n : ℕ) : (Thickening g I n).Etale
  finite (n : ℕ) : IsFinite (model n).hom
  reduction (n : ℕ) : V.left ⟶ (model n).left
  isPullback_reduction (n : ℕ) : IsPullback (reduction n) V.hom (model n).hom (fromClosed g I n)
  map {m n : ℕ} (h : m ≤ n) : (model m).left ⟶ (model n).left
  isPullback_map {m n : ℕ} (h : m ≤ n) : IsPullback (map h) (model m).hom (model n).hom (stageMap g I h)
  reduction_map {m n : ℕ} (h : m ≤ n) : reduction m ≫ map h = reduction n
  map_id (n : ℕ) : map (le_refl n) = 𝟙 _
  map_comp {m n p : ℕ} (h : m ≤ n) (k : n ≤ p) : map h ≫ map k = map (h.trans k)

/-- Every finite étale cover of the special fiber gives a compatible system
of finite étale covers over its infinitesimal thickenings. -/
theorem exists_compatible_models [IsLocallyNoetherian X] (V : (Fiber g I).Etale) [IsFinite V.hom] :
    Nonempty (CompatibleModels g I V) := by
  have h₁ (n : ℕ) := by
    let : IsLocallyNoetherian (Thickening g I n) := stage_noetherian g I n
    let : Surjective (fromClosed g I n) := surjective_transition_pow g I (Nat.succ_ne_zero n)
    exact PhilipponEtaleThickeningModels.exists_model (fromClosed g I n) V.hom
  choose Y f hE a hpb using h₁
  let (n : ℕ) : Etale (f n) := hE n
  let (n : ℕ) : Surjective (fromClosed g I n) := surjective_transition_pow g I (Nat.succ_ne_zero n)
  let (n : ℕ) : IsClosedImmersion (a n) := MorphismProperty.of_isPullback (hpb n).flip inferInstance
  let (n : ℕ) : Surjective (a n) := MorphismProperty.of_isPullback (hpb n).flip inferInstance
  let (n : ℕ) : IsLocallyNoetherian (Thickening g I n) := stage_noetherian g I n
  let (n : ℕ) : IsLocallyNoetherian (Y n) := LocallyOfFiniteType.isLocallyNoetherian (f n)
  have h₂ (m n : ℕ) (h : m ≤ n) :
      ∃! b : Y m ⟶ Y n, b ≫ f n = f m ≫ stageMap g I h ∧ a m ≫ b = a n := by
    apply PhilipponEtaleThickeningLifts.existsUnique_lift (f n) (a m) (f m ≫ stageMap g I h) (a n)
    rw [(hpb n).w, ← Category.assoc, (hpb m).w, Category.assoc, fromClosed_stageMap]
  let b {m n : ℕ} (h : m ≤ n) : Y m ⟶ Y n := (h₂ m n h).choose
  have hb {m n : ℕ} (h : m ≤ n) :
      b h ≫ f n = f m ≫ stageMap g I h ∧ a m ≫ b h = a n := (h₂ m n h).choose_spec.1
  refine ⟨{
    model n := Scheme.Etale.mk (f n)
    finite n := isFinite_of_thickening (hpb n)
    reduction := a
    isPullback_reduction := hpb
    map := fun {_ _} h => b h
    isPullback_map := ?_
    reduction_map := fun h => (hb h).2
    map_id := ?_
    map_comp := ?_ }⟩
  · intro m n h
    have hn := hpb n
    rw [← fromClosed_stageMap g I h] at hn
    exact isPullback_of_compatible_reductions (hpb m) hn (hb h).1 (hb h).2
  · intro n
    change b (le_refl n) = 𝟙 (Y n)
    symm
    exact (h₂ n n le_rfl).unique
      ⟨by rw [stageMap_id, Category.comp_id, Category.id_comp], Category.comp_id _⟩ (hb le_rfl)
  · intro m n p h k
    exact (h₂ m p (h.trans k)).unique
      ⟨by rw [Category.assoc, (hb k).1, ← Category.assoc, (hb h).1, Category.assoc, transition_comp],
        by rw [← Category.assoc, (hb h).2, (hb k).2]⟩ (hb (h.trans k))

end System

end PhilipponFiniteEtaleThickenings

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Function Module TensorProduct
open scoped KaehlerDifferential


namespace PhilipponAdicFiniteFlat

universe u

private theorem injective_of_quotient_of_projective {R S M N : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Nontrivial S]
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (hS : Surjective (algebraMap R S)) (f : M →ₗ[R] N) (hf : Surjective f)
    (h : Injective (f.lTensor S)) : Injective f := by
  let J := RingHom.ker (algebraMap R S)
  let e : (R ⧸ J) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS
  have hJ : J ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap R S))).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)
  let E := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  have hmk : E.toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ J) M 1 = TensorProduct.mk R S M 1 := by
    ext x
    change TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M) (1 ⊗ₜ[R] x) = _
    simp
  have hker : LinearMap.ker f ≤ J • ⊤ := by
    intro x hx
    rw [← LinearMap.ker_tensorProductMk]
    apply E.injective
    change E (TensorProduct.mk R (R ⧸ J) M 1 x) = E 0
    have hx' := DFunLike.congr_fun hmk x
    change E (TensorProduct.mk R (R ⧸ J) M 1 x) = TensorProduct.mk R S M 1 x at hx'
    rw [map_zero, hx']
    apply h
    change (1 : S) ⊗ₜ[R] f x = (f.lTensor S) 0
    rw [LinearMap.mem_ker.mp hx, tmul_zero, map_zero]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let q : M →ₗ[R] M := LinearMap.id - s.comp f
  have hq (x : M) (hx : x ∈ LinearMap.ker f) : q x = x := by
    simp [q, LinearMap.mem_ker.mp hx]
  have hRange : LinearMap.range q = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change f (x - s (f x)) = 0
      rw [map_sub, show f (s (f x)) = f x from DFunLike.congr_fun hs (f x), sub_self]
    · intro x hx
      exact ⟨x, hq x hx⟩
  have hmap : (LinearMap.ker f).map q = LinearMap.ker f := by
    apply le_antisymm
    · exact (Submodule.map_mono (f := q) le_top).trans (by rw [Submodule.map_top, hRange])
    · intro x hx
      exact ⟨x, hx, hq x hx⟩
  have hNak := Submodule.map_mono (f := q) hker
  rw [hmap, Submodule.map_smul'', Submodule.map_top, hRange] at hNak
  exact LinearMap.ker_eq_bot.mp (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J
    (LinearMap.ker f) (IsNoetherian.noetherian _) hNak hJ)

private theorem surjective_of_surjective_quotient {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (f : M →ₗ[R] N)
    (h : Surjective (f.lTensor (R ⧸ I))) : Surjective f := by
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
  intro x _
  obtain ⟨y, hy⟩ := h ((1 : R ⧸ I) ⊗ₜ[R] x)
  obtain ⟨z, rfl⟩ := TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective y
  have hsub : x - f z ∈ I • (⊤ : Submodule R N) := by
    rw [← LinearMap.ker_tensorProductMk, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr hy.symm
  exact Submodule.mem_sup.mpr ⟨f z, LinearMap.mem_range_self f z, x - f z, hsub, by abel⟩

private theorem local_of_quotient {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (h : I ≠ ⊤) : IsLocalRing (R ⧸ I) := by
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr h
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- A finite module over a Noetherian local ring is free if it becomes flat
over every positive-power quotient of a proper ideal. -/
theorem free_of_flat_power_quotients {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≠ ⊤)
    (hFlat : ∀ n : ℕ, Module.Flat (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] M)) :
    Module.Free R M := by
  classical
  let C := R ⧸ I
  let : IsLocalRing C := local_of_quotient I hI
  let : Module.Flat C (C ⊗[R] M) := by
    have h₀ := hFlat 0
    change Module.Flat (R ⧸ I ^ (1 : ℕ)) ((R ⧸ I ^ (1 : ℕ)) ⊗[R] M) at h₀
    exact Eq.mp (congrArg (fun J : Ideal R => Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M)) (pow_one I)) h₀
  let : Module.Free C (C ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis C (C ⊗[R] M)
  let D := Module.Free.ChooseBasisIndex C (C ⊗[R] M)
  let F := D →₀ R
  let : Finite D := Module.Finite.finite_basis b
  let : Module.Finite R F := inferInstanceAs (Module.Finite R (D →₀ R))
  choose v hv using fun i : D => TensorProduct.mk_surjective R M C Ideal.Quotient.mk_surjective (b i)
  let f : F →ₗ[R] M := Finsupp.linearCombination R v
  have hC : Bijective (f.lTensor C) := by
    have he : ((b.repr.symm : (D →₀ C) ≃ₗ[C] (C ⊗[R] M)).toLinearMap.restrictScalars R) =
        f.lTensor C ∘ₗ (finsuppScalarRight R R C D).symm.toLinearMap := by
      have key := Finsupp.linearCombination_one_tmul R C M D (v := v)
      change _ = _ at key
      have hv' : (fun i => (1 : C) ⊗ₜ[R] v i) = ⇑b := funext hv
      rw [hv'] at key
      simpa only [Basis.coe_repr_symm] using key
    apply ((finsuppScalarRight R R C D).symm.bijective.of_comp_iff (f.lTensor C)).mp
    change Bijective (f.lTensor C ∘ₗ (finsuppScalarRight R R C D).symm.toLinearMap)
    rw [← he]
    exact b.repr.symm.bijective
  have hJac : I ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.le_maximalIdeal hI).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have hsurj : Surjective f := surjective_of_surjective_quotient I hJac f hC.2
  have hn (n : ℕ) : Injective (f.lTensor (R ⧸ I ^ (n + 1))) := by
    let B := R ⧸ I ^ (n + 1)
    let h := Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n)
    let : IsLocalRing B := local_of_quotient _ (ne_top_of_le_ne_top hI h)
    let : Algebra B C := (Ideal.Quotient.factor h).toAlgebra
    let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : Module.Flat B (B ⊗[R] M) := hFlat n
    let : Module.Free B (B ⊗[R] M) := Module.free_of_flat_of_isLocalRing
    let f' := f.baseChange B
    have hs : Surjective f' := f.lTensor_surjective B hsurj
    let EF := AlgebraTensorModule.cancelBaseChange R B C C F
    let EM := AlgebraTensorModule.cancelBaseChange R B C C M
    have hcomp (x : C ⊗[B] (B ⊗[R] F)) : EM (f'.lTensor C x) = f.lTensor C (EF x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [hx, hy]
      | tmul c y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y z hy hz =>
          simp only [tmul_add, map_add, hy, hz]
        | tmul b x => simp [f', EF, EM]
    have hi : Injective (f'.lTensor C) := fun x y e => EF.injective (hC.1 (by rw [← hcomp, ← hcomp, e]))
    let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
    let : IsNoetherian B (B ⊗[R] F) := isNoetherian_of_isNoetherianRing_of_finite B _
    exact injective_of_quotient_of_projective (R := B) (S := C)
      (Ideal.Quotient.factor_surjective h) f' hs hi
  have hinj : Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hp (n : ℕ) : x ∈ I ^ n • (⊤ : Submodule R F) := by
      cases n with
      | zero => simp
      | succ n =>
        rw [← LinearMap.ker_tensorProductMk, LinearMap.mem_ker]
        apply hn n
        change (1 : R ⧸ I ^ (n + 1)) ⊗ₜ[R] f x = (f.lTensor _) 0
        rw [hx, tmul_zero, map_zero]
    have h' := (Submodule.mem_iInf _).mpr hp
    rw [(IsHausdorff.of_le_jacobson I F hJac).iInf_pow_smul] at h'
    exact h'
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A finite algebra over a Noetherian local ring is étale when its
reductions at every positive power of a proper ideal are étale. -/
theorem etale_of_etale_power_quotients {R B : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    (I : Ideal R) (hI : I ≠ ⊤)
    (h : ∀ n : ℕ, Algebra.Etale (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] B)) :
    Algebra.Etale R B := by
  let : Module.Free R B := free_of_flat_power_quotients I hI fun n => by
    let := h n
    infer_instance
  let C := R ⧸ I
  let : Algebra.Etale C (C ⊗[R] B) := Eq.mp
    (congrArg (fun J : Ideal R => Algebra.Etale (R ⧸ J) ((R ⧸ J) ⊗[R] B)) (pow_one I)) (h 0)
  let e := KaehlerDifferential.tensorKaehlerEquivBase R C B (C ⊗[R] B)
  let : Subsingleton (C ⊗[R] Ω[B⁄R]) := e.injective.subsingleton
  let : Module.Finite R Ω[B⁄R] := Module.Finite.trans B _
  have hJac : I ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.le_maximalIdeal hI).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have htop : (⊤ : Submodule R Ω[B⁄R]) ≤ I • ⊤ := by
    intro x _
    rw [← LinearMap.ker_tensorProductMk, LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  have hz := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I (⊤ : Submodule R Ω[B⁄R])
    Module.Finite.fg_top htop hJac
  let : Algebra.FormallyUnramified R B :=
    ⟨(subsingleton_iff_forall_eq 0).mpr fun x => (Submodule.eq_bot_iff _).mp hz x trivial⟩
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- An étale quotient model remains étale after a base change of the ring and ideal. -/
theorem etale_quotient_tensor_of_baseChange {R B T : Type u}
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T] (I : Ideal R)
    [Algebra.Etale (R ⧸ I) ((R ⧸ I) ⊗[R] B)] :
    Algebra.Etale (T ⧸ I.map (algebraMap R T))
      ((T ⧸ I.map (algebraMap R T)) ⊗[T] (T ⊗[R] B)) := by
  let C := R ⧸ I
  let D := T ⧸ I.map (algebraMap R T)
  let φ : C →+* D := Ideal.quotientMap _ (algebraMap R T) Ideal.le_comap_map
  let : Algebra C D := φ.toAlgebra
  let : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := Algebra.TensorProduct.cancelBaseChange R C D D B
  let e' := Algebra.TensorProduct.cancelBaseChange R T D D B
  let : Algebra.Etale C (C ⊗[R] B) := inferInstanceAs (Algebra.Etale (R ⧸ I) ((R ⧸ I) ⊗[R] B))
  exact Algebra.Etale.of_equiv (e.trans e'.symm)

/-- The same criterion after localizing a Noetherian base at a prime
containing the ideal of definition. -/
theorem etale_atPrime_of_etale_power_quotients {R B : Type u} [CommRing R]
    [IsNoetherianRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    (I P : Ideal R) [P.IsPrime] (hI : I ≤ P)
    (h : ∀ n : ℕ, Algebra.Etale (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] B)) :
    Algebra.Etale (Localization.AtPrime P) ((Localization.AtPrime P) ⊗[R] B) := by
  let T := Localization.AtPrime P
  let J := I.map (algebraMap R T)
  have hJ : J ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal T).ne_top
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P T]
    exact Ideal.map_mono hI
  apply etale_of_etale_power_quotients J hJ
  intro n
  let := h n
  have he : (I ^ (n + 1)).map (algebraMap R T) = J ^ (n + 1) := I.map_pow _ _
  apply Eq.mp (congrArg (fun K : Ideal T => Algebra.Etale (T ⧸ K) ((T ⧸ K) ⊗[T] (T ⊗[R] B))) he)
  exact etale_quotient_tensor_of_baseChange (R := R) (B := B) (T := T) (I ^ (n + 1))

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A point of a finite algebra lying over the adic closed subscheme is in
the étale locus if every positive-power reduction is étale. -/
theorem isEtaleAt_of_etale_power_quotients {R B : Type u} [CommRing R]
    [IsNoetherianRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    (I : Ideal R) (Q : Ideal B) [Q.IsPrime] (hI : I ≤ Q.under R)
    (h : ∀ n : ℕ, Algebra.Etale (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] B)) :
    Algebra.IsEtaleAt R Q := by
  let P := Q.under R
  let T := Localization.AtPrime P
  let C := T ⊗[R] B
  let S := Localization.AtPrime Q
  let : Algebra.Etale T C := etale_atPrime_of_etale_power_quotients I P hI h
  let : Algebra.FormallyEtale R T := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  let : Algebra.FormallyEtale R C := Algebra.FormallyEtale.comp R T C
  let M := Algebra.algebraMapSubmonoid B P.primeCompl
  let : IsLocalization M C := (Algebra.isLocalization_iff_isPushout P.primeCompl T).mpr inferInstance
  have hM : M ≤ Q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr
  let : Algebra C S := IsLocalization.localizationAlgebraOfSubmonoidLe C S M Q.primeCompl hM
  let : IsScalarTower B C S := IsLocalization.localization_isScalarTower_of_submonoid_le C S M Q.primeCompl hM
  let : IsLocalization (Q.primeCompl.map (algebraMap B C)) S :=
    IsLocalization.isLocalization_of_submonoid_le C S M Q.primeCompl hM
  let : Algebra.FormallyEtale C S := Algebra.FormallyEtale.of_isLocalization (Q.primeCompl.map (algebraMap B C))
  let : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq (R := R) (S := C) (A := S) fun x => by
    rw [IsScalarTower.algebraMap_apply R B C, ← IsScalarTower.algebraMap_apply B C S,
      ← IsScalarTower.algebraMap_apply R B S]
  exact Algebra.FormallyEtale.comp R C S

end PhilipponAdicFiniteFlat

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 450000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open PhilipponClosedFiberThickenings (Fiber)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedFiberSections (closedFiberι)
open PhilipponFiniteEtaleThickenings (CompatibleModels Thickening fromClosed)
open PhilipponFiniteEtaleClosedFiberEffectivity (property_of_near_closedFiber)


namespace PhilipponAdicEtaleEffectivity

universe u

private abbrev quotientSpecMap {A : Type u} [CommRing A] (I : Ideal A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

private abbrev fiberMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) (I : Ideal A) : Fiber g I ⟶ X :=
  pullback.snd (quotientSpecMap I) g

private theorem etale_quotient_of_chart {A R B : Type u} [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra R B] {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) (f : Y ⟶ X)
    (p : Spec (.of R) ⟶ X) (q : Spec (.of B) ⟶ Y)
    (hg : Spec.map (CommRingCat.ofHom (algebraMap A R)) = p ≫ g)
    (h : IsPullback q (Spec.map (CommRingCat.ofHom (algebraMap R B))) f p)
    (I : Ideal A) [Etale (pullback.snd f (fiberMap g I))] :
    Algebra.Etale (R ⧸ I.map (algebraMap A R))
      ((R ⧸ I.map (algebraMap A R)) ⊗[R] B) := by
  let J := I.map (algebraMap A R)
  let C := R ⧸ J
  let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let s := Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A R) Ideal.le_comap_map))
  have hcomp : s ≫ quotientSpecMap I = (r ≫ p) ≫ g := by
    rw [Category.assoc, ← hg]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))
  let t := pullback.lift s (r ≫ p) hcomp
  have ht : t ≫ fiberMap g I = r ≫ p := pullback.lift_snd ..
  let a := Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B)))
  let b := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := B)).toRingHom)
  let u := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hC : IsPullback b a u r :=
    ((IsPullback.of_hasPullback r u).of_iso' (pullbackSpecIso R C B).symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((pullbackSpecIso_inv_fst' R C B).trans (Category.comp_id _).symm)
      ((pullbackSpecIso_inv_snd R C B).trans (Category.comp_id _).symm)
      (by simp) (by simp)).flip
  have hAll := hC.paste_horiz h
  let k : Spec (.of (C ⊗[R] B)) ⟶ pullback f (fiberMap g I) :=
    pullback.lift (b ≫ q) (a ≫ t) (by rw [Category.assoc a t, ht]; exact hAll.w)
  have kfst : k ≫ pullback.fst f (fiberMap g I) = b ≫ q := pullback.lift_fst ..
  have ksnd : k ≫ pullback.snd f (fiberMap g I) = a ≫ t := pullback.lift_snd ..
  have hpb : IsPullback k a (pullback.snd f (fiberMap g I)) t := by
    apply IsPullback.of_right _ ksnd (IsPullback.of_hasPullback f (fiberMap g I))
    rw [kfst, ht]
    exact hAll
  have ha : Etale a := MorphismProperty.of_isPullback hpb inferInstance
  exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp ha)

private theorem exists_etale_open_of_affine_model {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [IsNoetherianRing R] [Module.Finite R B] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Spec (.of R) ⟶ X) (q : Spec (.of B) ⟶ Y) [IsOpenImmersion p] [IsOpenImmersion q]
    (h : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ p)
    (I : Ideal R) (x : Spec (.of B)) (hx : I ≤ x.asIdeal.under R)
    (hEt : ∀ n : ℕ, Algebra.Etale (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] B)) :
    ∃ W : Y.Opens, q x ∈ W ∧ Etale (W.ι ≫ f) := by
  let : Algebra.IsEtaleAt R x.asIdeal :=
    PhilipponAdicFiniteFlat.isEtaleAt_of_etale_power_quotients I x.asIdeal hx hEt
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨b, hb, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) x.asIdeal
  let j := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))))
  let v := j ≫ q
  let : IsOpenImmersion v := inferInstanceAs (IsOpenImmersion (j ≫ q))
  have hx' : x ∈ j.opensRange := by
    rw [show j.opensRange = PrimeSpectrum.basicOpen b from Scheme.Hom.opensRange_localizationAway b]
    exact hb
  obtain ⟨z, hz⟩ := hx'
  refine ⟨v.opensRange, ⟨z, congrArg q hz⟩, ?_⟩
  have hv : Etale (v ≫ f) := by
    change Etale ((j ≫ q) ≫ f)
    rw [Category.assoc, h, ← Category.assoc, ← Spec.map_comp]
    let : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b)))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hE)
    exact inferInstanceAs (Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) ≫ p))
  rw [← v.isoOpensRange_inv_comp, Category.assoc]
  exact MorphismProperty.comp_mem @Etale _ _ inferInstance hv

/-- If a finite morphism of a proper scheme over a local ring has étale
base changes to all infinitesimal thickenings of the closed fiber, it is étale. -/
theorem etale_of_etale_thickenings {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (g : X ⟶ Spec (.of A)) [IsProper g]
    (f : Y ⟶ X) [IsFinite f]
    (h : ∀ n : ℕ, Etale (pullback.snd f (fiberMap g (IsLocalRing.maximalIdeal A ^ (n + 1))))) :
    Etale f := by
  apply property_of_near_closedFiber (f ≫ g) f @Etale
  intro y hy
  obtain ⟨U, hU, hyU, _⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show f y ∈ (⊤ : X.Opens) from trivial)
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(X, U)
  let B := Γ(Y, V)
  let φ := f.app U
  let : Algebra R B := φ.hom.toAlgebra
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Module.Finite R B := (RingHom.finite_algebraMap).mp (f.finite_app U hU)
  let p := hU.fromSpec
  let q := hV.fromSpec
  let u := Spec.map φ
  have hc : u ≫ p = q ≫ f := by
    change Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl
  have hpb : IsPullback q u f p := by
    apply (IsOpenImmersion.isPullback u q p f hc.symm ?_).flip
    rw [hU.opensRange_fromSpec, hV.opensRange_fromSpec]
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (p ≫ g)
  let : Algebra A R := ρ.hom.toAlgebra
  let I := IsLocalRing.maximalIdeal A
  let J := I.map (algebraMap A R)
  have hEt (n : ℕ) : Algebra.Etale (R ⧸ J ^ (n + 1)) ((R ⧸ J ^ (n + 1)) ⊗[R] B) := by
    let := h n
    have he : (I ^ (n + 1)).map (algebraMap A R) = J ^ (n + 1) := I.map_pow _ _
    apply Eq.mp (congrArg (fun K : Ideal R => Algebra.Etale (R ⧸ K) ((R ⧸ K) ⊗[R] B)) he)
    exact etale_quotient_of_chart g f p q hρ hpb (I ^ (n + 1))
  have hyq : y ∈ Set.range q := hV.range_fromSpec.symm ▸ hyU
  obtain ⟨x, hx⟩ := hyq
  have hClosed : Spec.map ρ (u x) = IsLocalRing.closedPoint A := by
    rw [← Scheme.Hom.comp_apply, hρ, ← Category.assoc, hc, Category.assoc,
      Scheme.Hom.comp_apply, hx]
    exact hy
  have hxI : J ≤ x.asIdeal.under R := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (congrArg PrimeSpectrum.asIdeal hClosed).symm.le
  simpa only [hx] using exists_etale_open_of_affine_model f p q hc.symm J x hxI hEt

/-- A finite algebraization of the compatible formal models yields a
finite étale lift of the original cover. -/
theorem of_compatible_algebraization {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (g : X ⟶ Spec (.of A)) [IsProper g]
    (V : (Fiber g (IsLocalRing.maximalIdeal A)).Etale)
    (D : CompatibleModels g (IsLocalRing.maximalIdeal A) V) (f : Y ⟶ X) [IsFinite f]
    (a : ∀ n : ℕ, (D.model n).left ⟶ Y)
    (ha : ∀ n : ℕ, IsPullback (a n) (D.model n).hom f
      (fiberMap g (IsLocalRing.maximalIdeal A ^ (n + 1)))) :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange (closedFiberι g)).obj W ≅ V) := by
  let : Etale f := etale_of_etale_thickenings g f fun n => by
    have hEt : Etale ((ha n).isoPullback.inv ≫ (D.model n).hom) := inferInstance
    rwa [(ha n).isoPullback_inv_snd] at hEt
  have hv : IsPullback (D.reduction 0 ≫ a 0) V.hom f (closedFiberι g) := by
    have h' := (D.isPullback_reduction 0).paste_horiz (ha 0)
    rwa [PhilipponClosedFiberThickenings.transition_snd] at h'
  exact ⟨Scheme.Etale.mk f, inferInstanceAs (IsFinite f),
    ⟨MorphismProperty.Over.isoMk hv.isoPullback.symm hv.isoPullback_inv_snd⟩⟩

end PhilipponAdicEtaleEffectivity

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponClosedFiberThickenings (Fiber transition_fst transition_snd)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedFiberSections (closedFiberι)
open PhilipponFiniteEtaleThickenings (Thickening stageMap exists_compatible_models)


namespace PhilipponCompleteFiniteEtaleSpecialization

universe u

private abbrev quotientMap {A : Type u} [CommRing A] (I : Ideal A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- Finite étale specialization on a proper scheme over a complete
Noetherian local ring, by finite-morphism algebraization. -/
theorem exists_lift_of_isAdicComplete {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]
    (V : (Fiber g (IsLocalRing.maximalIdeal A)).Etale) [IsFinite V.hom] :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange (closedFiberι g)).obj W ≅ V) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  let I := IsLocalRing.maximalIdeal A
  obtain ⟨D⟩ := exists_compatible_models g I V
  let sR (n : ℕ) := quotientMap (I ^ (n + 1))
  let d (n : ℕ) : I ^ (n + 1 + 1) ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
  let tR (n : ℕ) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (d n)))
  have hR (n : ℕ) : tR n ≫ sR (n + 1) = sR n := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let eX (n : ℕ) : Thickening g I n ≅ pullback g (sR n) := pullbackSymmetry (sR n) g
  let xn (n : ℕ) := (eX n).inv ≫ stageMap g I (Nat.le_succ n) ≫ (eX (n + 1)).hom
  have hx₁ (n : ℕ) : xn n ≫ pullback.fst g (sR (n + 1)) = pullback.fst g (sR n) := by
    simp only [xn, Category.assoc, eX, pullbackSymmetry_hom_comp_fst]
    exact (transition_snd g (d n) ▸ pullbackSymmetry_inv_comp_snd (sR n) g)
  have hx₂ (n : ℕ) : xn n ≫ pullback.snd g (sR (n + 1)) = pullback.snd g (sR n) ≫ tR n := by
    simp only [xn, Category.assoc, eX, pullbackSymmetry_hom_comp_snd]
    rw [transition_fst g (d n), ← Category.assoc, pullbackSymmetry_inv_comp_fst]
  let q (n : ℕ) := (D.model n).hom ≫ (eX n).hom
  let (n : ℕ) : IsFinite (D.model n).hom := D.finite n
  let (n : ℕ) : IsFinite (q n) := inferInstanceAs (IsFinite ((D.model n).hom ≫ (eX n).hom))
  have hY (n : ℕ) : IsPullback (D.map (Nat.le_succ n)) (q n) (q (n + 1)) (xn n) := by
    refine (D.isPullback_map (Nat.le_succ n)).of_iso (Iso.refl _) (Iso.refl _) (eX n) (eX (n + 1))
      (by simp) (Category.id_comp _).symm (Category.id_comp _).symm ?_
    change _ = (eX n).hom ≫ (eX n).inv ≫ _
    rw [Iso.hom_inv_id_assoc]
  obtain ⟨Z, G, hG, e, he, _⟩ :=
    AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
      A I X g sR (fun _ => rfl) tR hR xn hx₁ hx₂ (fun n => (D.model n).left) q
      (fun n => D.map (Nat.le_succ n)) hY
  let : IsFinite G := hG
  let a (n : ℕ) := (e n).inv ≫ pullback.fst G (pullback.fst g (sR n))
  apply PhilipponAdicEtaleEffectivity.of_compatible_algebraization g V D G a
  intro n
  exact (IsPullback.of_hasPullback G (pullback.fst g (sR n))).of_iso'
    (e n).symm (Iso.refl _) (eX n) (Iso.refl _)
    (Category.comp_id _).symm ((Iso.inv_comp_eq (e n)).mpr (he n).symm)
    (by simp) (by
      simpa only [Iso.refl_hom, Category.comp_id, eX] using
        pullbackSymmetry_hom_comp_fst (sR n) g)

end PhilipponCompleteFiniteEtaleSpecialization

end

section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PhilipponMultiplicity.NoetherianCompletion

open scoped Topology

variable {R : Type*} [CommRing R]

theorem exists_powerSeriesMap (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ R →+* AdicCompletion I R,
      (∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  letI : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hI
  have hcomplete : CompleteSpace S ∧ T2Space S :=
    (IsAdic.isAdicComplete_iff (I := J) rfl).mp inferInstance
  letI : CompleteSpace S := hcomplete.1
  letI : T2Space S := hcomplete.2
  have hcont : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval (fun i => algebraMap R S (a i)) := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_map_of_mem _ (ha i))
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro r
    simp [MvPowerSeries.coe_eval₂Hom, S]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom, S]

theorem powerSeriesMap_surjective (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R)
    (ha : Ideal.span (Set.range a) = I)
    (f : MvPowerSeries σ R →+* AdicCompletion I R)
    (hC : ∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) :
    Function.Surjective f := by
  let S := AdicCompletion I R
  let J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = I.map (algebraMap R S) := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hX]
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, S] using
      congrArg (Ideal.map (algebraMap R S)) ha
  letI : IsAdicComplete (I.map (algebraMap R S)) S :=
    AdicCompletion.isAdicComplete_self I hI
  letI : IsHausdorff (J.map f) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C r)) =
    Ideal.Quotient.mk (J.map f) y
  rw [hC, Ideal.Quotient.eq, hmap]
  change algebraMap R (AdicCompletion I R) r - y ∈
    I.map (algebraMap R (AdicCompletion I R))
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (I := I) hI]
  change AdicCompletion.evalOneₐ I (algebraMap R S r - y) = 0
  rw [map_sub]
  change Ideal.Quotient.mk I r - AdicCompletion.evalOneₐ I y = 0
  rw [hr, sub_self]

theorem isNoetherianRing_completion [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  have hmem : ∀ i, a i ∈ I := fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨f, hC, hX⟩ := exists_powerSeriesMap I I.fg_of_isNoetherianRing a hmem
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) R) (AdicCompletion I R) f
    (powerSeriesMap_surjective I I.fg_of_isNoetherianRing a ha f hC hX)

end PhilipponMultiplicity.NoetherianCompletion

end

section

set_option autoImplicit false

open IsLocalRing MvPolynomial


namespace PhilipponResiduePolynomialApproximation

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

private abbrev C := AdicCompletion (maximalIdeal A) A

/-- Approximation of solutions of finite polynomial systems modulo the
maximal ideal gives the corresponding approximation of algebra maps. -/
theorem exists_algHom_of_polynomial_approximation
    (H : ∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) A) (x' : Fin n → C (A := A)),
      (∀ j, aeval x' (P j) = 0) → ∃ x : Fin n → A, (∀ j, aeval x (P j) = 0) ∧
        ∀ i, residue (C (A := A)) (x' i) = ResidueField.map (algebraMap A (C (A := A))) (residue A (x i)))
    (R : Type u) [CommRing R] [Algebra A R] [Algebra.FinitePresentation A R]
    (f' : R →ₐ[A] C (A := A)) :
    ∃ f : R →ₐ[A] A, (residue (C (A := A))).comp f'.toRingHom =
      (ResidueField.map (algebraMap A (C (A := A)))).comp ((residue A).comp f.toRingHom) := by
  classical
  obtain ⟨n, p, hp, hker⟩ := Algebra.FinitePresentation.out (R := A) (A := R)
  obtain ⟨F, hF⟩ := hker
  let j := Fintype.equivFin ↥F
  let P (i : Fin (Fintype.card ↥F)) : MvPolynomial (Fin n) A := (j.symm i).val
  let x' (i : Fin n) := f' (p (X i))
  have he : aeval x' = f'.comp p := MvPolynomial.algHom_ext fun i => by simp [x']
  have hsol (i : Fin (Fintype.card ↥F)) : aeval x' (P i) = 0 := by
    have hi := Ideal.subset_span (j.symm i).property
    rw [hF] at hi
    change p (P i) = 0 at hi
    rw [he, AlgHom.comp_apply, hi, map_zero]
  obtain ⟨x, hx, hr⟩ := H n _ P x' hsol
  let e : MvPolynomial (Fin n) A →ₐ[A] A := aeval x
  have hle : RingHom.ker p.toRingHom ≤ RingHom.ker e.toRingHom := by
    rw [← hF]
    apply Ideal.span_le.mpr
    intro z hz
    have h := hx (j ⟨z, hz⟩)
    simpa [P, e] using h
  let f := AlgHom.liftOfSurjective p hp e hle
  have hf (z : MvPolynomial (Fin n) A) : f (p z) = e z := AlgHom.liftOfSurjective_apply ..
  let r := ResidueField.map (algebraMap A (C (A := A)))
  have hpull : (residue (C (A := A))).comp (aeval x').toRingHom =
      r.comp ((residue A).comp e.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e, r, ResidueField.map_residue]
    · intro i
      simpa [e, r] using hr i
  refine ⟨f, RingHom.ext fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hp y
  have h := RingHom.congr_fun hpull z
  rw [he] at h
  change residue (C (A := A)) (f' (p z)) = r (residue A (f (p z)))
  rw [hf]
  exact h

end PhilipponResiduePolynomialApproximation

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedFiberSections (closedFiberι)


namespace PhilipponCompletionFiniteEtaleSpecialization

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

abbrev CompleteRing := AdicCompletion (IsLocalRing.maximalIdeal A) A

private abbrev residueSpec (R : Type u) [CommRing R] [IsLocalRing R] :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

abbrev completionMap (A : Type u) [CommRing A] [IsLocalRing A] :=
  Spec.map (CommRingCat.ofHom (algebraMap A (CompleteRing (A := A))))

variable {X : Scheme.{u}} (g : X ⟶ Spec (.of A))

abbrev completedBase := pullback g (completionMap A)

abbrev structureMap : completedBase g ⟶ Spec (.of (CompleteRing (A := A))) :=
  pullback.snd g (completionMap A)

abbrev completedProjection : completedBase g ⟶ X := pullback.fst g (completionMap A)

private def residueIso :
    Spec (.of (IsLocalRing.ResidueField (CompleteRing (A := A)))) ≅ Spec (.of (IsLocalRing.ResidueField A)) :=
  Scheme.Spec.mapIso (RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective A)).toCommRingCatIso.op

private theorem residueIso_comp :
    (residueIso (A := A)).hom ≫ residueSpec A = residueSpec (CompleteRing (A := A)) ≫ completionMap A := by
  change Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap A (CompleteRing (A := A))))) ≫
    residueSpec A = residueSpec (CompleteRing (A := A)) ≫ completionMap A
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

private theorem closedFiber_isPullback :
    IsPullback (closedFiberι (structureMap g) ≫ completedProjection g)
      (pullback.fst (residueSpec (CompleteRing (A := A))) (structureMap g) ≫ (residueIso (A := A)).hom)
      g (residueSpec A) := by
  let r := residueSpec (CompleteRing (A := A))
  have h := (IsPullback.of_hasPullback r (structureMap g)).flip.paste_horiz
    (IsPullback.of_hasPullback g (completionMap A))
  exact h.of_iso (Iso.refl _) (Iso.refl _) (residueIso (A := A)) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (Category.id_comp _).symm (by simp) (by rw [Iso.refl_hom, Category.comp_id, residueIso_comp])

/-- The closed fiber of the pullback to the completed local base is the
original closed fiber, with its given map into `X`. -/
def closedFiberIso :
    pullback (residueSpec (CompleteRing (A := A))) (structureMap g) ≅ pullback (residueSpec A) g :=
  (closedFiber_isPullback g).flip.isoPullback

theorem closedFiberIso_hom_comp :
    (closedFiberIso g).hom ≫ closedFiberι g = closedFiberι (structureMap g) ≫ completedProjection g :=
  (closedFiber_isPullback g).flip.isoPullback_hom_snd

/-- Over a proper Noetherian local base, every finite étale cover of the
closed fiber lifts over the completion of the base ring. -/
theorem exists_lift_on_completion [IsProper g] {V : (pullback (residueSpec A) g).Etale} [IsFinite V.hom] :
    ∃ W : (completedBase g).Etale, IsFinite W.hom ∧
      Nonempty ((baseChange (closedFiberι (structureMap g))).obj W ≅ (baseChange (closedFiberIso g).hom).obj V) := by
  let : IsNoetherianRing (CompleteRing (A := A)) :=
    PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion (IsLocalRing.maximalIdeal A)
  let V' := (baseChange (closedFiberIso g).hom).obj V
  let : IsFinite V'.hom := inferInstanceAs (IsFinite (pullback.snd V.hom (closedFiberIso g).hom))
  exact PhilipponCompleteFiniteEtaleSpecialization.exists_lift_of_isAdicComplete (structureMap g) V'

/-- A finite étale model over a common parameter scheme specializes to the
same cover along two parameter maps agreeing on the closed fiber. -/
theorem exists_lift_of_common_model [IsProper g] {Z : Scheme.{u}}
    (u : X ⟶ Z) (v : completedBase g ⟶ Z)
    (h : closedFiberι (structureMap g) ≫ v = (closedFiberIso g).hom ≫ closedFiberι g ≫ u)
    (B : Z.Etale) [IsFinite B.hom] (V : (pullback (residueSpec A) g).Etale)
    (e : (baseChange (closedFiberι (structureMap g))).obj ((baseChange v).obj B) ≅
      (baseChange (closedFiberIso g).hom).obj V) :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange (closedFiberι g)).obj W ≅ V) := by
  let r := closedFiberι g
  let s := closedFiberι (structureMap g)
  let a := (closedFiberIso g).hom
  let F := baseChange a
  let W := (baseChange u).obj B
  let t := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) s v
  let ε := MorphismProperty.Over.pullbackCongr (P := @Etale) (Q := ⊤) h
  let h₁ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) a (r ≫ u)
  let h₂ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) r u
  have d : F.obj ((baseChange r).obj W) ≅ F.obj V :=
    (F.mapIso (h₂.app B)).symm ≪≫ (h₁.app B).symm ≪≫ (ε.app B).symm ≪≫ t.app B ≪≫ e
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsClosedImmersion (residueSpec A) := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let : IsClosedImmersion r := inferInstanceAs (IsClosedImmersion (pullback.snd (residueSpec A) g))
  let : IsLocallyNoetherian (pullback (residueSpec A) g) := LocallyOfFiniteType.isLocallyNoetherian r
  let : IsClosedImmersion a := inferInstanceAs (IsClosedImmersion (closedFiberIso g).hom)
  let : Surjective a := inferInstanceAs (Surjective (closedFiberIso g).hom)
  let hF := PhilipponFiniteEtaleClosedFiberEffectivity.baseChangeFullyFaithful a
  exact ⟨W, inferInstanceAs (IsFinite (pullback.snd B.hom u)), ⟨hF.preimageIso d⟩⟩

section Parameters

variable {R : Type u} [CommRing R] [Algebra A R]

private abbrev parameterMap := Spec.map (CommRingCat.ofHom (algebraMap A R))

/-- The base-changed parameter scheme over an `A`-algebra. -/
abbrev parameterScheme := pullback g (parameterMap (A := A) (R := R))

/-- Evaluate an `A`-algebra of parameters at an `A`-valued point. -/
def sectionFor (f : R →ₐ[A] A) : X ⟶ parameterScheme (R := R) g :=
  pullback.lift (𝟙 _) (g ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    rw [Category.id_comp, Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (algebraMap A R) ≫ CommRingCat.ofHom f.toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext (RingHom.ext f.commutes)
    rw [h, Spec.map_id, Category.comp_id])

/-- Evaluate an `A`-algebra of parameters at a point valued in the completion. -/
def completedSectionFor (f : R →ₐ[A] (CompleteRing (A := A))) :
    completedBase g ⟶ parameterScheme (R := R) g :=
  pullback.lift (completedProjection g) (structureMap g ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    rw [Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (algebraMap A R) ≫ CommRingCat.ofHom f.toRingHom =
        CommRingCat.ofHom (algebraMap A (CompleteRing (A := A))) := CommRingCat.hom_ext (RingHom.ext f.commutes)
    rw [h]
    exact pullback.condition)

private theorem sectionFor_eq_on_closedFiber
    (f : R →ₐ[A] A) (f' : R →ₐ[A] (CompleteRing (A := A)))
    (h : (IsLocalRing.residue (CompleteRing (A := A))).comp f'.toRingHom =
      (IsLocalRing.ResidueField.map (algebraMap A (CompleteRing (A := A)))).comp ((IsLocalRing.residue A).comp f.toRingHom)) :
    closedFiberι (structureMap g) ≫ completedSectionFor g f' =
      (closedFiberIso g).hom ≫ closedFiberι g ≫ sectionFor g f := by
  let r := residueSpec (CompleteRing (A := A))
  let l := pullback.fst r (structureMap g)
  let l₀ := pullback.fst (residueSpec A) g
  have hr : r ≫ Spec.map (CommRingCat.ofHom f'.toRingHom) =
      (residueIso (A := A)).hom ≫ residueSpec A ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
    change _ = Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map
      (algebraMap A (CompleteRing (A := A))))) ≫ _
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext h)
  have hπ : (closedFiberIso g).hom ≫ l₀ = l ≫ (residueIso (A := A)).hom :=
    (closedFiber_isPullback g).flip.isoPullback_hom_fst
  have hs : closedFiberι (structureMap g) ≫ structureMap g = l ≫ r := pullback.condition.symm
  have ht : closedFiberι g ≫ g = l₀ ≫ residueSpec A := pullback.condition.symm
  apply pullback.hom_ext
  · simp only [Category.assoc, completedSectionFor, sectionFor, pullback.lift_fst, Category.comp_id]
    exact (closedFiberIso_hom_comp g).symm
  · simp only [Category.assoc, completedSectionFor, sectionFor, pullback.lift_snd]
    rw [← Category.assoc (closedFiberι (structureMap g)), hs, Category.assoc, hr,
      ← Category.assoc (closedFiberι g), ht, Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun p => p ≫ residueSpec A ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) hπ.symm

/-- A lift that is modeled over an algebra of parameters descends once
those parameters admit an `A`-valued approximation at the closed point. -/
theorem exists_lift_of_residue_approximation [IsProper g]
    (f : R →ₐ[A] A) (f' : R →ₐ[A] (CompleteRing (A := A)))
    (h : (IsLocalRing.residue (CompleteRing (A := A))).comp f'.toRingHom =
      (IsLocalRing.ResidueField.map (algebraMap A (CompleteRing (A := A)))).comp ((IsLocalRing.residue A).comp f.toRingHom))
    (B : (parameterScheme (R := R) g).Etale) [IsFinite B.hom]
    (V : (pullback (residueSpec A) g).Etale)
    (e : (baseChange (closedFiberι (structureMap g))).obj ((baseChange (completedSectionFor g f')).obj B) ≅
      (baseChange (closedFiberIso g).hom).obj V) :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange (closedFiberι g)).obj W ≅ V) :=
  exists_lift_of_common_model g (sectionFor g f) (completedSectionFor g f')
    (sectionFor_eq_on_closedFiber g f f' h) B V e

end Parameters

/-- Finite-presentation descent from the completion and approximation of
parameter points suffice for specialization over a Noetherian local base. -/
theorem exists_lift_of_parameter_descent [IsProper g]
    (hDesc : ∀ W : (completedBase g).Etale, IsFinite W.hom →
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : Algebra.FinitePresentation A R)
        (f' : R →ₐ[A] (CompleteRing (A := A))) (B : (parameterScheme (R := R) g).Etale),
        IsFinite B.hom ∧ Nonempty ((baseChange (completedSectionFor g f')).obj B ≅ W))
    (hApprox : ∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) A) (x' : Fin n → CompleteRing (A := A)),
      (∀ j, MvPolynomial.aeval x' (P j) = 0) →
      ∃ x : Fin n → A, (∀ j, MvPolynomial.aeval x (P j) = 0) ∧
        ∀ i, IsLocalRing.residue (CompleteRing (A := A)) (x' i) =
          IsLocalRing.ResidueField.map (algebraMap A (CompleteRing (A := A))) (IsLocalRing.residue A (x i)))
    (V : (pullback (residueSpec A) g).Etale) [IsFinite V.hom] :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty ((baseChange (closedFiberι g)).obj W ≅ V) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_lift_on_completion g (V := V)
  obtain ⟨R, hR, hAr, hP, f', B, hB, ⟨d⟩⟩ := hDesc W hW
  let : CommRing R := hR
  let : Algebra A R := hAr
  let : Algebra.FinitePresentation A R := hP
  let : IsFinite B.hom := hB
  obtain ⟨f, hf⟩ := PhilipponResiduePolynomialApproximation.exists_algHom_of_polynomial_approximation hApprox R f'
  exact exists_lift_of_residue_approximation g f f' hf B V
    ((baseChange (closedFiberι (structureMap g))).mapIso d ≪≫ e)

end PhilipponCompletionFiniteEtaleSpecialization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedFiberSections (closedFiberι)


namespace PhilipponFiniteEtaleSpecializationTransfer

universe u

/-- Transport a finite étale specialization lift from a model of the closed
fiber. The two pullbacks of the model along the commutative square agree. -/
theorem of_model {X Y S T : Scheme.{u}} (i : S ⟶ X) (j : T ⟶ Y) (v : Y ⟶ X) (u₀ : T ⟶ S)
    (h : j ≫ v = u₀ ≫ i) (B : S.Etale) {V : T.Etale} (e : (baseChange u₀).obj B ≅ V)
    (W : X.Etale) [IsFinite W.hom] (f : (baseChange i).obj W ≅ B) :
    ∃ U : Y.Etale, IsFinite U.hom ∧ Nonempty ((baseChange j).obj U ≅ V) := by
  let P : MorphismProperty Scheme.{u} := @Etale
  let C := MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) j v
  let D := MorphismProperty.Over.pullbackCongr (P := P) (Q := ⊤) h
  let E := MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) u₀ i
  refine ⟨(baseChange v).obj W, inferInstanceAs (IsFinite (pullback.snd W.hom v)), ?_⟩
  exact ⟨(C.app W).symm ≪≫ D.app W ≪≫ E.app W ≪≫ (baseChange u₀).mapIso f ≪≫ e⟩

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

open PhilipponCompletionFiniteEtaleSpecialization

/-- Approximation of parameter points is sufficient for specialization over
a proper Noetherian local model once finite étale descent is available. -/
theorem exists_lift_of_approximable_model {X Y T : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g]
    (hDesc : ∀ W : (completedBase g).Etale, IsFinite W.hom →
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : Algebra.FinitePresentation A R)
        (f' : R →ₐ[A] (CompleteRing (A := A))) (B : (parameterScheme (R := R) g).Etale),
        IsFinite B.hom ∧ Nonempty ((baseChange (completedSectionFor g f')).obj B ≅ W))
    (hApprox : ∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) A) (x' : Fin n → CompleteRing (A := A)),
      (∀ k, MvPolynomial.aeval x' (P k) = 0) →
      ∃ x : Fin n → A, (∀ k, MvPolynomial.aeval x (P k) = 0) ∧
        ∀ k, IsLocalRing.residue (CompleteRing (A := A)) (x' k) =
          IsLocalRing.ResidueField.map (algebraMap A (CompleteRing (A := A))) (IsLocalRing.residue A (x k)))
    (j : T ⟶ Y) (v : Y ⟶ X) (u₀ : T ⟶ pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (h : j ≫ v = u₀ ≫ closedFiberι g) (B : (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g).Etale)
    [IsFinite B.hom] {V : T.Etale} (e : (baseChange u₀).obj B ≅ V) :
    ∃ U : Y.Etale, IsFinite U.hom ∧ Nonempty ((baseChange j).obj U ≅ V) := by
  obtain ⟨W, hW, ⟨w⟩⟩ := exists_lift_of_parameter_descent g hDesc hApprox B
  let : IsFinite W.hom := hW
  exact of_model (closedFiberι g) j v u₀ h B e W w

end PhilipponFiniteEtaleSpecializationTransfer

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [CommRing A] [HenselianLocalRing A] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g) (V : T.Etale) [IsFinite V.hom] :
    ∃ W : Y.Etale, IsFinite W.hom ∧ Nonempty ((PhilipponEtaleBaseChangeComparison.baseChange j).obj W ≅ V) := by
  obtain ⟨R, hR, hLocal, hNoeth, _, _, X, g₀, hProper, v, z, B, _, _, hcomm, hFinite, ⟨e⟩, hApprox⟩ :=
    AlgebraicGeometry.Scheme.exists_approximable_henselian_stage_for_finite_etale_closed_fiber A g s j h V
  let : CommRing R := hR
  let : HenselianLocalRing R := hLocal
  let : IsNoetherianRing R := hNoeth
  let : IsProper g₀ := hProper
  let : IsFinite B.hom := hFinite
  apply PhilipponFiniteEtaleSpecializationTransfer.exists_lift_of_approximable_model
    g₀ ?_ hApprox j v z hcomm B e
  intro W hW
  let : IsFinite W.hom := hW
  obtain ⟨Q, hQ, hAlg, hPres, f, p, D, hp₁, hp₂, hD, ⟨d⟩⟩ := AlgebraicGeometry.Scheme.exists_finite_etale_parameter_model_over_completion R g₀ W
  let : CommRing Q := hQ
  let : Algebra R Q := hAlg
  let : Algebra.FinitePresentation R Q := hPres
  have hp : p = PhilipponCompletionFiniteEtaleSpecialization.completedSectionFor g₀ f := by
    apply pullback.hom_ext
    · exact hp₁.trans (pullback.lift_fst ..).symm
    · exact hp₂.trans (pullback.lift_snd ..).symm
  exact ⟨Q, hQ, hAlg, hPres, f, D, hD, ⟨hp ▸ d⟩⟩

end

end
