-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjectiveLineFiniteOverlap
-- name    : AlgebraicGeometry_ProjectiveLineFiniteOverlap
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T01:44:13.155086+00:00
-- url     : https://prove2.me/theorems/ede3d3ab-a9c9-5134-b78a-b429702c5f44
-- title:
--   Finite morphisms on the overlap of projective line charts
-- statement:
--   The standard charts have principal intersection and a finite morphism on the intersection extends over the line.
-- source:
--   Principal-localization extension and gluing over the two standard affine charts.

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

section

section

set_option autoImplicit false

namespace PhilipponFiniteAlgebraLocalizationExtension

universe u

variable (R L B : Type*) [CommRing R] [CommRing L] [CommRing B]
  [Algebra R L] [Algebra L B] [Algebra R B] [IsScalarTower R L B]

/-- A finite algebra over a principal localization comes from a finite algebra
over the original ring. The finite model can be taken inside the given algebra. -/
theorem exists_finite_subalgebra (s : R) [IsLocalization.Away s L] [Module.Finite L B] :
    ∃ C : Subalgebra R B, Module.Finite R C ∧ IsLocalization.Away (algebraMap R C s) B := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := L) (M := B)
  have hIntegral (b : t) : ∃ n : ℕ, IsIntegral R (algebraMap R B s ^ n * (b : B)) := by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Submonoid.powers s) (Rₘ := L) (b : B) (Algebra.IsIntegral.isIntegral (R := L) (b : B))
    exact ⟨n, by simpa only [Submonoid.smul_def, Algebra.smul_def, map_pow] using hn⟩
  choose n hn using hIntegral
  let a := algebraMap R B s
  let g (b : t) := a ^ n b * (b : B)
  let C := Algebra.adjoin R (Set.range g)
  have hC : Module.Finite R C := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.finite_range g) (by rintro _ ⟨b, rfl⟩; exact hn b)
  have clearDenominator (b : B) : ∃ k : ℕ, a ^ k * b ∈ C := by
    have hb : b ∈ Submodule.span L (↑t : Set B) := ht.symm ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      exact ⟨n ⟨b, hb⟩, Algebra.subset_adjoin ⟨⟨b, hb⟩, rfl⟩⟩
    | zero => exact ⟨0, by simp⟩
    | add b c _ _ hb hc =>
      obtain ⟨k, hk⟩ := hb
      obtain ⟨l, hl⟩ := hc
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (b + c) = a ^ l * (a ^ k * b) + a ^ k * (a ^ l * c) := by
        rw [pow_add]
        ring
      rw [e]
      have ha : a ∈ C := C.algebraMap_mem s
      exact C.add_mem (C.mul_mem (C.pow_mem ha l) hk) (C.mul_mem (C.pow_mem ha k) hl)
    | smul z b _ hb =>
      obtain ⟨k, hk⟩ := hb
      obtain ⟨⟨d, ⟨_, l, rfl⟩⟩, hd⟩ := IsLocalization.surj (Submonoid.powers s) z
      have e : algebraMap L B z * a ^ l = algebraMap R B d := by
        simpa only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, a] using
          congrArg (algebraMap L B) hd
      refine ⟨k + l, ?_⟩
      rw [Algebra.smul_def, pow_add]
      rw [show a ^ k * a ^ l * (algebraMap L B z * b) =
          algebraMap L B z * a ^ l * (a ^ k * b) by ring, e]
      exact C.mul_mem (C.algebraMap_mem d) hk
  refine ⟨C, hC, (isLocalization_iff (Submonoid.powers (algebraMap R C s)) B).2 ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    have ha : IsUnit (algebraMap L B (algebraMap R L s)) := (IsLocalization.map_units L
      (⟨s, 1, pow_one s⟩ : Submonoid.powers s)).map (algebraMap L B)
    change IsUnit (((algebraMap R C s ^ k : C) : B))
    rw [Subalgebra.coe_pow]
    change IsUnit (a ^ k)
    rw [show a = algebraMap L B (algebraMap R L s) from
      IsScalarTower.algebraMap_apply R L B s]
    exact ha.pow k
  · intro b
    obtain ⟨k, hk⟩ := clearDenominator b
    refine ⟨⟨⟨a ^ k * b, hk⟩, ⟨algebraMap R C s ^ k, k, rfl⟩⟩, ?_⟩
    change b * ((algebraMap R C s ^ k : C) : B) = a ^ k * b
    rw [Subalgebra.coe_pow]
    exact mul_comm _ _
  · intro b c h
    refine ⟨1, ?_⟩
    change (1 : C) * b = 1 * c
    rw [one_mul, one_mul]
    exact Subtype.ext h

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

/-- A finite morphism of affine schemes over a principal open extends to a
finite morphism over the whole affine base. -/
theorem exists_finite_cartesian_extension {R L B : Type u}
    [CommRing R] [CommRing L] [CommRing B]
    [Algebra R L] [Algebra L B] [Algebra R B] [IsScalarTower R L B]
    (s : R) [IsLocalization.Away s L] [Module.Finite L B] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (.of R)) (_ : IsFinite p)
      (a : Spec (.of B) ⟶ Z),
      IsPullback (Spec.map (CommRingCat.ofHom (algebraMap L B))) a
        (Spec.map (CommRingCat.ofHom (algebraMap R L))) p := by
  obtain ⟨C, hC, hLocalization⟩ := exists_finite_subalgebra R L B s
  let : Module.Finite R C := hC
  let : IsLocalization ((Submonoid.powers s).map (algebraMap R C)) B := by
    rw [Submonoid.map_powers]
    exact hLocalization
  let p := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hp : IsFinite p := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr hC)
  have comm : (algebraMap L B).comp (algebraMap R L) =
      (algebraMap C B).comp (algebraMap R C) :=
    (IsScalarTower.algebraMap_eq R L B).symm.trans (IsScalarTower.algebraMap_eq R C B)
  let e := CommRingCat.isPushout_of_isLocalization (algebraMap R C) (algebraMap L B)
    comm (Submonoid.powers s)
  exact ⟨Spec (.of C), p, hp, Spec.map (CommRingCat.ofHom (algebraMap C B)), e.op.map Scheme.Spec⟩

/-- A finite morphism to a principal open in an affine scheme has a finite
extension whose restriction recovers the given morphism. -/
theorem exists_finite_extension {X Y : Scheme.{u}} [IsAffine X] (s : Γ(X, ⊤))
    (q : Y ⟶ X.basicOpen s) [IsFinite q] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (_ : IsFinite p) (a : Y ⟶ Z),
      IsPullback q a (X.basicOpen s).ι p := by
  let W := X.basicOpen s
  have hW : IsAffineOpen W := (isAffineOpen_top X).basicOpen s
  let : IsAffine (W : Scheme) := hW
  let : IsAffine Y := isAffine_of_isAffineHom q
  let R := Γ(X, ⊤)
  let L := Γ(X, W)
  let B := Γ(Y, ⊤)
  let l : L ⟶ B := W.topIso.inv ≫ q.appTop
  let : Algebra L B := l.hom.toAlgebra
  let : Algebra R B := ((algebraMap L B).comp (algebraMap R L)).toAlgebra
  let : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq' rfl
  have hl : l.hom.Finite := q.finite_appTop.comp (RingHom.Finite.of_surjective _
    (W.topIso.symm.commRingCatIsoToRingEquiv.surjective))
  let : Module.Finite L B := RingHom.finite_algebraMap.mp hl
  obtain ⟨Z, p, hp, a, hs⟩ := exists_finite_cartesian_extension (L := L) (B := B) s
  let : IsFinite p := hp
  let eX := X.isoSpec
  let eW := hW.isoSpec
  let eY := Y.isoSpec
  have hq : eY.hom ≫ Spec.map l = q ≫ eW.hom := by
    change Y.toSpecΓ ≫ Spec.map (W.topIso.inv ≫ q.appTop) =
      q ≫ W.toSpecΓ
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    rfl
  have hres : eW.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) =
      W.ι ≫ eX.hom := W.toSpecΓ_SpecMap_presheaf_map_top
  refine ⟨Z, p ≫ eX.inv, inferInstance, eY.hom ≫ a,
    hs.of_iso eY.symm eW.symm (Iso.refl _) eX.symm ?_ ?_ ?_ ?_⟩
  · change Spec.map l ≫ eW.inv = eY.inv ≫ q
    apply (cancel_mono eW.hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (cancel_epi eY.hom).mp (by simpa only [Iso.hom_inv_id_assoc] using hq)
  · simp
  · apply (cancel_mono eX.hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (cancel_epi eW.hom).mp (by simpa only [Iso.hom_inv_id_assoc] using hres)
  · simp

end PhilipponFiniteAlgebraLocalizationExtension

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteMorphismTwoOpenGluing

universe u

variable {X : Scheme.{u}} (U V : X.Opens)

private abbrev toLeft : (U ⊓ V).toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
private abbrev toRight : (U ⊓ V).toScheme ⟶ V.toScheme := X.homOfLE inf_le_right

private abbrev baseDiagram := span (toLeft U V) (toRight U V)

private def inclusion : ∀ i, (baseDiagram U V).obj i ⟶ X
  | .zero => (U ⊓ V).ι
  | .left => U.ι
  | .right => V.ι

private instance (i : WalkingSpan) : IsOpenImmersion (inclusion U V i) := by
  rcases i with _ | i
  · exact inferInstanceAs (IsOpenImmersion (U ⊓ V).ι)
  · cases i
    · exact inferInstanceAs (IsOpenImmersion U.ι)
    · exact inferInstanceAs (IsOpenImmersion V.ι)

private def cover (h : U ⊔ V = ⊤) : X.OpenCover where
  I₀ := WalkingSpan
  X := (baseDiagram U V).obj
  f := inclusion U V
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => inferInstanceAs (IsOpenImmersion (inclusion U V i))⟩
    have hx : x ∈ U ⊔ V := h.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    rcases hx with hx | hx
    · exact ⟨.left, ⟨⟨x, hx⟩, rfl⟩⟩
    · exact ⟨.right, ⟨⟨x, hx⟩, rfl⟩⟩

private theorem transition_over {i j : WalkingSpan} (f : i ⟶ j) :
    (baseDiagram U V).map f ≫ inclusion U V j = inclusion U V i := by
  cases f with
  | id i => exact Category.id_comp _
  | init i =>
    cases i
    · exact X.homOfLE_ι inf_le_left
    · exact X.homOfLE_ι inf_le_right

private theorem pointLift {i j k : WalkingSpan} (f : k ⟶ i) (g : k ⟶ j)
    (h : IsPullback ((baseDiagram U V).map f) ((baseDiagram U V).map g)
      (inclusion U V i) (inclusion U V j))
    (x : (pullback (inclusion U V i) (inclusion U V j)).carrier) :
    ∃ y : (baseDiagram U V).obj k,
      pullback.lift ((baseDiagram U V).map f) ((baseDiagram U V).map g)
        ((transition_over U V f).trans (transition_over U V g).symm) y = x := by
  refine ⟨h.isoPullback.inv x, ?_⟩
  exact congrArg (fun a : pullback (inclusion U V i) (inclusion U V j) ⟶
    pullback (inclusion U V i) (inclusion U V j) => a x) h.isoPullback.inv_hom_id

private theorem pullback_of_transition {i j : WalkingSpan} (f : i ⟶ j) :
    IsPullback ((baseDiagram U V).map (𝟙 i)) ((baseDiagram U V).map f)
      (inclusion U V i) (inclusion U V j) := by
  rw [(baseDiagram U V).map_id]
  exact IsPullback.of_horiz_isIso_mono
    ⟨(Category.id_comp _).trans (transition_over U V f).symm⟩

private instance categoryOnCover (h : U ⊔ V = ⊤) : Category (cover U V h).I₀ :=
  inferInstanceAs (Category WalkingSpan)

private instance thinOnCover (h : U ⊔ V = ⊤) : Quiver.IsThin (cover U V h).I₀ := by
  intro i j
  constructor
  intro a b
  cases a <;> cases b <;> rfl

private instance directedCover (h : U ⊔ V = ⊤) : (cover U V h).LocallyDirected where
  trans := (baseDiagram U V).map
  trans_id := (baseDiagram U V).map_id
  trans_comp := (baseDiagram U V).map_comp
  w := transition_over U V
  directed := by
    intro i j x
    change WalkingSpan at i j
    have hUV : IsPullback ((baseDiagram U V).map WalkingSpan.Hom.fst)
        ((baseDiagram U V).map WalkingSpan.Hom.snd) (inclusion U V .left) (inclusion U V .right) :=
      isPullback_opens_inf U V
    let z := WalkingSpan.zero
    let l := WalkingSpan.left
    let r := WalkingSpan.right
    let fst : z ⟶ l := WalkingSpan.Hom.fst
    let snd : z ⟶ r := WalkingSpan.Hom.snd
    have diag (i : WalkingSpan) := pointLift U V (𝟙 i) (𝟙 i) (pullback_of_transition U V (𝟙 i))
    rcases i with _ | (_ | _) <;> rcases j with _ | (_ | _)
    · exact ⟨z, 𝟙 z, 𝟙 z, diag z x⟩
    · exact ⟨z, 𝟙 z, fst, pointLift U V (𝟙 z) fst (pullback_of_transition U V fst) x⟩
    · exact ⟨z, 𝟙 z, snd, pointLift U V (𝟙 z) snd (pullback_of_transition U V snd) x⟩
    · exact ⟨z, fst, 𝟙 z, pointLift U V fst (𝟙 z) (pullback_of_transition U V fst).flip x⟩
    · exact ⟨l, 𝟙 l, 𝟙 l, diag l x⟩
    · exact ⟨z, fst, snd, pointLift U V fst snd hUV x⟩
    · exact ⟨z, snd, 𝟙 z, pointLift U V snd (𝟙 z) (pullback_of_transition U V snd).flip x⟩
    · exact ⟨z, snd, fst, pointLift U V snd fst hUV.flip x⟩
    · exact ⟨r, 𝟙 r, 𝟙 r, diag r x⟩
  property_trans := by
    intro i j f
    change i ⟶ j at f
    cases f with
    | id i =>
      change IsOpenImmersion (𝟙 ((baseDiagram U V).obj i))
      infer_instance
    | init i =>
      cases i
      · exact inferInstanceAs (IsOpenImmersion (toLeft U V))
      · exact inferInstanceAs (IsOpenImmersion (toRight U V))

/-- Finite morphisms on the members of a two-open cover glue when their
restrictions are given by a common morphism on the intersection. -/
theorem glue_finite (h : U ⊔ V = ⊤) {T L R : Scheme.{u}}
    (q : T ⟶ (U ⊓ V).toScheme) (pL : L ⟶ U.toScheme) (pR : R ⟶ V.toScheme)
    [IsFinite pL] [IsFinite pR] (a : T ⟶ L) (b : T ⟶ R)
    (hL : IsPullback q a (toLeft U V) pL) (hR : IsPullback q b (toRight U V) pR) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (_ : IsFinite p) (z : T ⟶ Z),
      IsPullback q z (U ⊓ V).ι p := by
  let 𝒰 := cover U V h
  let : 𝒰.LocallyDirected := directedCover U V h
  let : Quiver.IsThin 𝒰.I₀ := thinOnCover U V h
  let D : 𝒰.I₀ ⥤ Scheme.{u} := span a b
  let f : D ⟶ 𝒰.functorOfLocallyDirected := {
    app := fun
      | .zero => q
      | .left => pL
      | .right => pR
    naturality := by
      intro i j f
      change i ⟶ j at f
      cases f with
      | id i => exact (Category.id_comp _).trans (Category.comp_id _).symm
      | init i =>
        cases i
        · exact hL.w.symm
        · exact hR.w.symm }
  let d : 𝒰.RelativeGluingData := {
    functor := D
    natTrans := f
    equifibered := by
      intro i j u
      change i ⟶ j at u
      cases u with
      | id i =>
        change IsPullback (𝟙 _) (f.app i) (f.app i) (𝟙 _)
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩
      | init i =>
        cases i
        · exact hL.flip
        · exact hR.flip }
  let : ∀ {i j : 𝒰.I₀} (u : i ⟶ j), IsOpenImmersion (d.functor.map u) :=
    fun u => MorphismProperty.of_isPullback (d.equifibered u).flip (𝒰.property_trans u)
  let : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin d
  have hq : IsFinite q := MorphismProperty.of_isPullback hL.flip inferInstance
  have hFinite (i : 𝒰.I₀) : IsFinite (f.app i) := by
    change WalkingSpan at i
    rcases i with _ | (_ | _)
    · exact hq
    · exact ‹IsFinite pL›
    · exact ‹IsFinite pR›
  have hp : IsFinite d.toBase := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰
    intro i
    change IsFinite (pullback.snd d.toBase (𝒰.f i))
    let : IsFinite (f.app i) := hFinite i
    rw [← (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd]
    infer_instance
  exact ⟨d.glued, d.toBase, hp, colimit.ι d.functor .zero, d.isPullback_natTrans_ι_toBase .zero⟩

private theorem extend_on_chart {W C T : Scheme.{u}} [IsAffine C] (s : Γ(C, ⊤))
    (e : W ≅ C.basicOpen s) (j : W ⟶ C) (hj : e.hom ≫ (C.basicOpen s).ι = j)
    (q : T ⟶ W) [IsFinite q] :
    ∃ (L : Scheme.{u}) (p : L ⟶ C) (_ : IsFinite p) (a : T ⟶ L), IsPullback q a j p := by
  obtain ⟨L, p, hp, a, h⟩ :=
    PhilipponFiniteAlgebraLocalizationExtension.exists_finite_extension s (q ≫ e.hom)
  refine ⟨L, p, hp, a, h.of_iso (.refl _) e.symm (.refl _) (.refl _) ?_ ?_ ?_ ?_⟩
  · simp
  · simp
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, ← hj, Iso.inv_hom_id_assoc]
  · simp

/-- A finite morphism on the intersection of two affine opens extends to their
union when the intersection is principal in both charts. -/
theorem extend_from_intersection (h : U ⊔ V = ⊤)
    [IsAffine (U : Scheme)] [IsAffine (V : Scheme)]
    (s : Γ((U : Scheme), ⊤)) (t : Γ((V : Scheme), ⊤))
    (eu : (U ⊓ V).toScheme ≅ (U : Scheme).basicOpen s)
    (ev : (U ⊓ V).toScheme ≅ (V : Scheme).basicOpen t)
    (hu : eu.hom ≫ ((U : Scheme).basicOpen s).ι = toLeft U V)
    (hv : ev.hom ≫ ((V : Scheme).basicOpen t).ι = toRight U V)
    {T : Scheme.{u}} (q : T ⟶ (U ⊓ V).toScheme) [IsFinite q] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (_ : IsFinite p) (z : T ⟶ Z),
      IsPullback q z (U ⊓ V).ι p := by
  obtain ⟨L, pL, hpL, a, hL⟩ := extend_on_chart s eu _ hu q
  obtain ⟨R, pR, hpR, b, hR⟩ := extend_on_chart t ev _ hv q
  let : IsFinite pL := hpL
  let : IsFinite pR := hpR
  exact glue_finite U V h q pL pR a b hL hR

end PhilipponFiniteMorphismTwoOpenGluing

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponEtaleProjectiveLineTwoAffine

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

/-- The standard charts in a relative projective line are affine and their
intersection is principal in each chart. -/
theorem exists_two_affine_opens_with_principal_intersection {R A : Type u}
    [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R) (h : IsPullback r d v (ProjSpace.π R 1)) :
    ∃ U V : P.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
      (∃ s : Γ((U : Scheme), ⊤),
        (P.homOfLE (inf_le_left : U ⊓ V ≤ U)).opensRange = (U : Scheme).basicOpen s) ∧
      (∃ t : Γ((V : Scheme), ⊤),
        (P.homOfLE (inf_le_right : U ⊓ V ≤ V)).opensRange = (V : Scheme).basicOpen t) := by
  let D := ProjSpace.affineOpenCover R 1
  let C := D.openCover
  let W (i : Fin 2) := d ⁻¹ᵁ (C.f i).opensRange
  have hAffine (i : Fin 2) : IsAffineOpen (W i) := by
    let g := C.f i ≫ ProjSpace.π R 1
    let : IsAffine (C.X i) := inferInstanceAs (IsAffine (Spec (D.X i)))
    have hQ := (IsPullback.of_hasPullback (C.f i) d).paste_vert h.flip
    let e : pullback (C.f i) d ≅ pullback g v := hQ.isoPullback
    let : IsAffine (pullback (C.f i) d) := IsAffine.of_isIso e.hom
    rw [show W i = (pullback.snd (C.f i) d).opensRange from
      (Scheme.Hom.opensRange_pullbackSnd (C.f i) d).symm]
    exact isAffineOpen_opensRange _
  have hCover : W 0 ⊔ W 1 = ⊤ := by
    have hSup : ⨆ i, W i = ⊤ := d.iSup_preimage_eq_top C.iSup_opensRange
    rw [← hSup]
    apply le_antisymm
    · exact sup_le (le_iSup W 0) (le_iSup W 1)
    · apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
  have hPrincipal (i k : Fin 2) :
      ∃ s : Γ((W i : Scheme), ⊤), (W i).ι ⁻¹ᵁ (W k) = (W i : Scheme).basicOpen s := by
    let g := (W i).ι ≫ d
    let b : (W i : Scheme) ⟶ C.X i := IsOpenImmersion.lift (C.f i) g (by
      rintro _ ⟨x, rfl⟩
      exact x.2)
    have hb : b ≫ C.f i = g := IsOpenImmersion.lift_fac _ _ _
    let xi := ProjSpace.X_mem_one R 1 i
    let xk := ProjSpace.X_mem_one R 1 k
    let c : D.X i := HomogeneousLocalization.Away.isLocalizationElem xi xk
    let t : Γ(C.X i, ⊤) := (Scheme.ΓSpecIso (D.X i)).inv c
    have ht : C.f i ⁻¹ᵁ (C.f k).opensRange = (C.X i).basicOpen t := by
      let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) R
      change (Proj.awayι 𝒜 (MvPolynomial.X i) xi one_pos) ⁻¹ᵁ
          (Proj.awayι 𝒜 (MvPolynomial.X k) xk one_pos).opensRange = (Spec (D.X i)).basicOpen t
      rw [Proj.opensRange_awayι 𝒜 (MvPolynomial.X k) xk one_pos]
      exact (Proj.awayι_preimage_basicOpen 𝒜 xi one_pos xk one_pos).trans
        (basicOpen_eq_of_affine c).symm
    refine ⟨b.appTop t, ?_⟩
    change (W i).ι ⁻¹ᵁ (d ⁻¹ᵁ (C.f k).opensRange) = _
    rw [← Scheme.Hom.comp_preimage, ← show b ≫ C.f i = (W i).ι ≫ d from hb,
      Scheme.Hom.comp_preimage, ht, Scheme.preimage_basicOpen_top]
  obtain ⟨s, hs⟩ := hPrincipal 0 1
  obtain ⟨t, ht⟩ := hPrincipal 1 0
  refine ⟨W 0, W 1, hAffine 0, hAffine 1, hCover, ⟨s, ?_⟩, ⟨t, ?_⟩⟩
  · rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact hs
  · rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact ht

/-- The two standard affine charts remain affine after base change to an affine scheme. -/
theorem exists_two_affine_opens {R A : Type u} [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R) (h : IsPullback r d v (ProjSpace.π R 1)) :
    ∃ U V : P.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  obtain ⟨U, V, hU, hV, hCover, _, _⟩ := exists_two_affine_opens_with_principal_intersection v r d h
  exact ⟨U, V, hU, hV, hCover⟩

end PhilipponEtaleProjectiveLineTwoAffine

end

end


