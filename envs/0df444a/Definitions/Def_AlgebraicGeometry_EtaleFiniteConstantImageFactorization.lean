-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteConstantImageFactorization
-- name    : AlgebraicGeometry_EtaleFiniteConstantImageFactorization
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T00:10:44.625777+00:00
-- url     : https://prove2.me/theorems/d4192a71-f393-5e79-a299-33c13db084bd
-- title:
--   Factoring maps to constant direct images through finite stages
-- statement:
--   Maps from finite étale presentations to an integral constant direct image factor through a finite stage.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_EtaleFiniteChartPresentationDescent
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

section

section

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

namespace PhilipponEtaleGenericIdempotents

/-- Integral elements in the generic fiber of a smooth algebra over an
integrally closed domain descend to the algebra. -/
theorem exists_preimage_of_isIntegral {R S K : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x : S ⊗[R] K) (hx : IsIntegral S x) : ∃ s : S, algebraMap S (S ⊗[R] K) s = x := by
  have hSurj : Function.Surjective (algebraMap R (integralClosure R K)) := by
    intro y
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral y.property
    exact ⟨r, Subtype.ext hr⟩
  let descent := TensorProduct.toIntegralClosure R S K
  have hDescent : Function.Surjective descent := TensorProduct.toIntegralClosure_bijective_of_smooth.2
  obtain ⟨z, hz⟩ := hDescent ⟨x, hx⟩
  obtain ⟨s, hs⟩ := Algebra.TensorProduct.includeLeft_surjective S S hSurj z
  have he : descent (algebraMap S (S ⊗[R] integralClosure R K) s) = ⟨x, hx⟩ :=
    (congrArg descent hs).trans hz
  have hMap := (descent.commutes s).symm.trans he
  exact ⟨s, congrArg Subtype.val hMap⟩

/-- A finite product decomposition of the generic fiber of a smooth
algebra over a normal domain lifts to a complete family of idempotents. -/
theorem exists_lift_completeOrthogonalIdempotents {R S K : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [Field K] [Algebra R K] [IsFractionRing R K] {I : Type*} [Fintype I] [DecidableEq I]
    (e : S ⊗[R] K ≃+* (I → K)) :
    ∃ a : I → S, CompleteOrthogonalIdempotents a ∧
      ∀ i, e (algebraMap S (S ⊗[R] K) (a i)) = Pi.single i 1 := by
  let d (i : I) : I → K := Pi.single i 1
  have hD : CompleteOrthogonalIdempotents d := CompleteOrthogonalIdempotents.single (fun _ => K)
  let v (i : I) := e.symm (d i)
  have hV : CompleteOrthogonalIdempotents v := hD.map e.symm.toRingHom
  have hIntegral (i : I) : IsIntegral S (v i) := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by decide)), ?_⟩
    simp [pow_two, (hV.idem i).eq]
  choose a ha using fun i => exists_preimage_of_isIntegral (v i) (hIntegral i)
  let g := e.toRingHom.comp (algebraMap S (S ⊗[R] K))
  have hInjective : Function.Injective g := e.injective.comp
    (Algebra.TensorProduct.includeLeft_injective (S := S) (IsFractionRing.injective R K))
  have hEq (i : I) : g (a i) = d i := by
    change e (algebraMap S (S ⊗[R] K) (a i)) = _
    rw [ha, e.apply_symm_apply]
  refine ⟨a, (CompleteOrthogonalIdempotents.map_injective_iff g hInjective).mp ?_, hEq⟩
  rw [show g ∘ a = d from funext hEq]
  exact hD

universe u

/-- An affine étale algebra over a normal domain with separably closed
fraction field has coordinate idempotents lifting those of its generic fiber. -/
theorem exists_etale_coordinate_idempotents {R S K : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (e : K ⊗[R] S ≃ₐ[K] (I → K))
      (a : I → S), CompleteOrthogonalIdempotents a ∧
      ∀ i, e (1 ⊗ₜ[R] a i) = Pi.single i 1 := by
  classical
  let B := K ⊗[R] S
  let : Algebra.Etale K B := inferInstanceAs (Algebra.Etale K (K ⊗[R] S))
  let : Module.Finite K B := Algebra.FormallyUnramified.finite_of_free K B
  let : IsArtinianRing B := isArtinian_of_tower K inferInstance
  let I := PrimeSpectrum B
  let : Fintype I := Fintype.ofFinite I
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K B
  let e' := (Algebra.TensorProduct.comm R S K).toRingEquiv.trans e.toRingEquiv
  obtain ⟨a, ha, hCoordinates⟩ := exists_lift_completeOrthogonalIdempotents e'
  refine ⟨I, inferInstance, inferInstance, e, a, ha, ?_⟩
  intro i
  simpa [e', Algebra.TensorProduct.comm_tmul] using hCoordinates i

end PhilipponEtaleGenericIdempotents

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open TopologicalSpace Polynomial

namespace PhilipponEtaleGenericConstantSections

universe u v w

/-- A finite clopen partition specified on a dense image determines a
continuous extension to the target. -/
theorem exists_section_of_clopens
    {X : Type u} {Y : Type v} {M : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M] (f : C(X, Y)) (hf : DenseRange f)
    (s : C(X, M)) (U : M → Clopens Y)
    (hU : ∀ m : M, f ⁻¹' (U m : Set Y) = s ⁻¹' {m}) :
    ∃ t : C(Y, M), t.comp f = s := by
  classical
  have hc : IsClosed (⋃ m, (U m : Set Y)) := isClosed_iUnion_of_finite fun m => (U m).isClosed
  have hRange : Set.range f ⊆ ⋃ m, (U m : Set Y) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ f ⁻¹' (U (s x) : Set Y) := by rw [hU]; rfl
    exact Set.mem_iUnion.mpr ⟨s x, hx⟩
  have hAll (y : Y) : ∃ m, y ∈ U m :=
    Set.mem_iUnion.mp (hc.closure_subset_iff.mpr hRange (hf y))
  have hDense : Dense (Set.range f) := hf
  have hUnique {y : Y} {a b : M} (ha : y ∈ U a) (hb : y ∈ U b) : a = b := by
    obtain ⟨_, ⟨ha', hb'⟩, ⟨x, rfl⟩⟩ :=
      hDense.inter_open_nonempty _ ((U a).isOpen.inter (U b).isOpen) ⟨y, ha, hb⟩
    have ha'' : s x = a := by
      change x ∈ f ⁻¹' (U a : Set Y) at ha'
      rwa [hU] at ha'
    have hb'' : s x = b := by
      change x ∈ f ⁻¹' (U b : Set Y) at hb'
      rwa [hU] at hb'
    exact ha''.symm.trans hb''
  let t (y : Y) := (hAll y).choose
  have ht (y : Y) : y ∈ U (t y) := (hAll y).choose_spec
  have hFiber (m : M) : t ⁻¹' {m} = (U m : Set Y) := by
    ext y
    exact ⟨fun h => (show t y = m from h) ▸ ht y, fun h => hUnique (ht y) h⟩
  have htCont : Continuous t := (IsLocallyConstant.iff_continuous t).mp <|
    IsLocallyConstant.iff_isOpen_fiber.mpr fun m => by rw [hFiber]; exact (U m).isOpen
  refine ⟨⟨t, htCont⟩, ContinuousMap.ext fun x => ?_⟩
  have hx : f x ∈ U (s x) := by
    change x ∈ f ⁻¹' (U (s x) : Set Y)
    rw [hU]
    rfl
  exact hUnique (ht (f x)) hx

variable {R S K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [Algebra R S] [Algebra.Smooth R S]
  [Field K] [Algebra R K] [IsFractionRing R K]

private abbrev T := S ⊗[R] K

/-- The map from the generic fiber of a smooth affine scheme over a
normal affine domain to the whole affine scheme. -/
def genericMap : C(PrimeSpectrum (T (R := R) (S := S) (K := K)), PrimeSpectrum S) :=
  ⟨PrimeSpectrum.comap (algebraMap S (T (R := R) (S := S) (K := K))),
    PrimeSpectrum.continuous_comap _⟩

/-- Restrictions of finite locally constant functions to the generic
fiber of a smooth affine algebra over a normal domain are bijective. -/
theorem bijective_genericMap_sections (M : Type v) [TopologicalSpace M] [DiscreteTopology M]
    [Finite M] :
    Function.Bijective (fun s : C(PrimeSpectrum S, M) =>
      s.comp (genericMap (R := R) (S := S) (K := K))) := by
  classical
  let B := T (R := R) (S := S) (K := K)
  let p := genericMap (R := R) (S := S) (K := K)
  let g := algebraMap S B
  have hg : Function.Injective g :=
    Algebra.TensorProduct.includeLeft_injective (S := S) (IsFractionRing.injective R K)
  have hd : DenseRange p := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).mpr
    (((RingHom.injective_iff_ker_eq_bot g).mp hg).trans_le bot_le)
  constructor
  · intro s t h
    exact ContinuousMap.ext (congrFun (hd.equalizer s.continuous t.continuous
      (congrArg ContinuousMap.toFun h)))
  · intro s
    suffices h : ∀ m : M, ∃ V : Clopens (PrimeSpectrum S), p ⁻¹' (V : Set (PrimeSpectrum S)) =
        s ⁻¹' {m} by
      choose U hU using h
      exact exists_section_of_clopens p hd s U hU
    intro m
    have hc : IsClopen (s ⁻¹' {m}) := (isClopen_discrete {m}).preimage s.continuous
    obtain ⟨e, he, heU⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hc
    have hInt : IsIntegral S e := by
      refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by decide)), ?_⟩
      simp [pow_two, he.eq]
    obtain ⟨a, ha⟩ := PhilipponEtaleGenericIdempotents.exists_preimage_of_isIntegral e hInt
    have hId : IsIdempotentElem a := hg (by rw [map_mul, ha, he.eq])
    refine ⟨PrimeSpectrum.isIdempotentElemEquivClopens ⟨a, hId⟩, ?_⟩
    rw [PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply, heU]
    exact (congrArg (fun V : Opens (PrimeSpectrum B) => (V : Set (PrimeSpectrum B)))
      (PrimeSpectrum.comap_basicOpen g a)).trans (congrArg (fun b : B =>
        (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B))) ha)

end PhilipponEtaleGenericConstantSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponEtaleConstantSectionLimit

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Scheme.{u}} (c : Cone D) (hc : IsLimit c)

include hc in
/-- A map to a finite discrete space descends to an affine stage if the
projections from the limit are surjective. -/
theorem exists_stage_continuousMap [CompactSpace c.pt]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (hSurj : ∀ i, Function.Surjective (c.π.app i : c.pt → D.obj i))
    {M : Type v} [TopologicalSpace M] [DiscreteTopology M] [Finite M] (s : C(c.pt, M)) :
    ∃ (i : I) (t : C(D.obj i, M)), t.comp ⟨c.π.app i, (c.π.app i).continuous⟩ = s := by
  classical
  let : Fintype M := Fintype.ofFinite M
  let U (m : M) : Clopens c.pt :=
    ⟨s ⁻¹' {m}, (isClopen_discrete {m}).preimage s.continuous⟩
  choose i V _ hV using fun m =>
    exists_preimage_eq D c hc (U m).toOpens (U m).isClosed.isCompact
  choose j W _ hW using fun m =>
    exists_preimage_eq D c hc (U m)ᶜ.toOpens ((U m)ᶜ).isClosed.isCompact
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists ((Finset.univ.image i) ∪ (Finset.univ.image j))
  let a (m : M) : k ⟶ i m :=
    (hk (Finset.mem_union_left _ (Finset.mem_image_of_mem i (Finset.mem_univ m)))).some
  let b (m : M) : k ⟶ j m :=
    (hk (Finset.mem_union_right _ (Finset.mem_image_of_mem j (Finset.mem_univ m)))).some
  let V' (m : M) := D.map (a m) ⁻¹ᵁ V m
  let W' (m : M) := D.map (b m) ⁻¹ᵁ W m
  have hV' (m : M) : c.π.app k ⁻¹ᵁ V' m = (U m).toOpens := by
    dsimp only [V']
    rw [← Scheme.Hom.comp_preimage, c.w, hV]
  have hW' (m : M) : c.π.app k ⁻¹ᵁ W' m = ((U m)ᶜ).toOpens := by
    dsimp only [W']
    rw [← Scheme.Hom.comp_preimage, c.w, hW]
  have hSet (m : M) : (W' m : Set (D.obj k)) = (V' m : Set (D.obj k))ᶜ := by
    apply Set.preimage_injective.mpr (hSurj k)
    rw [Set.preimage_compl]
    exact (congrArg (fun V : c.pt.Opens => (V : Set c.pt)) (hW' m)).trans
      (congrArg (fun V : c.pt.Opens => (V : Set c.pt)ᶜ) (hV' m)).symm
  let B (m : M) : Clopens (D.obj k) :=
    ⟨V' m, ⟨isOpen_compl_iff.mp (hSet m ▸ (W' m).isOpen), (V' m).isOpen⟩⟩
  let p : C(c.pt, D.obj k) := ⟨c.π.app k, (c.π.app k).continuous⟩
  obtain ⟨t, ht⟩ := PhilipponEtaleGenericConstantSections.exists_section_of_clopens p
    (hSurj k).denseRange s B (fun m =>
      congrArg (fun V : c.pt.Opens => (V : Set c.pt)) (hV' m))
  exact ⟨k, t, ht⟩

/-- Precompose continuous functions with a scheme morphism. -/
def restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Type v) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] : AddCommGrpCat.of C(Y, M) ⟶ AddCommGrpCat.of C(X, M) :=
  AddCommGrpCat.ofHom
    { toFun := fun s => s.comp ⟨f, f.continuous⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem restrict_injective {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Function.Surjective f)
    (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] :
    Function.Injective (restrict f M) := by
  intro a b hab
  apply ContinuousMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun z : C(X, M) => z x) hab

include hc in
/-- An additive family of continuous sections with finite source and
coefficient groups descends to one stage. Surjectivity of the limit
projection verifies the group law for the descended family. -/
theorem exists_stage_additive [CompactSpace c.pt]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (hSurj : ∀ i, Function.Surjective (c.π.app i : c.pt → D.obj i))
    {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    {A : AddCommGrpCat.{u}} [Finite A] (s : A ⟶ AddCommGrpCat.of C(c.pt, M)) :
    ∃ (i : I) (t : A ⟶ AddCommGrpCat.of C(D.obj i, M)), t ≫ restrict (c.π.app i) M = s := by
  classical
  let : Fintype A := Fintype.ofFinite A
  choose i t ht using fun a : A => exists_stage_continuousMap c hc hSurj (s a)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let f (a : A) : j ⟶ i a := (hj (Finset.mem_image_of_mem i (Finset.mem_univ a))).some
  let r (a : A) : C(D.obj j, M) := restrict (D.map (f a)) M (t a)
  let k := restrict (c.π.app j) M
  have hk (a : A) : k (r a) = s a := by
    apply ContinuousMap.ext
    intro x
    change t a (D.map (f a) (c.π.app j x)) = s a x
    rw [← Scheme.Hom.comp_apply, c.w]
    exact congrArg (fun z : C(c.pt, M) => z x) (ht a)
  have hInj := restrict_injective (c.π.app j) (hSurj j) M
  let g : A ⟶ AddCommGrpCat.of C(D.obj j, M) := AddCommGrpCat.ofHom
    { toFun := r
      map_zero' := hInj (by rw [hk, map_zero, map_zero])
      map_add' := fun a b => hInj (by rw [hk, map_add, map_add, hk, hk]) }
  exact ⟨j, g, ConcreteCategory.hom_ext _ _ hk⟩

end PhilipponEtaleConstantSectionLimit

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (continuousSheaf)
open PhilipponEtaleConstantSectionLimit (restrict restrict_injective exists_stage_additive)


namespace PhilipponEtaleConstantImageStage

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y Z W : Scheme.{u}} {p : Y ⟶ X} {q : Z ⟶ X} {r : W ⟶ X}

/-- The projection between the two pullbacks of an étale chart along
a morphism over the same base scheme. -/
def chartProjection (a : Y ⟶ Z) (h : a ≫ q = p) (U : X.Etale) :
    ((baseChange p).obj U).left ⟶ ((baseChange q).obj U).left :=
  pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ a) (by
    rw [Category.assoc, h, pullback.condition])

@[reassoc (attr := simp)]
theorem chartProjection_fst (a : Y ⟶ Z) (h : a ≫ q = p) (U : X.Etale) :
    chartProjection a h U ≫ pullback.fst U.hom q = pullback.fst U.hom p :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem chartProjection_snd (a : Y ⟶ Z) (h : a ≫ q = p) (U : X.Etale) :
    chartProjection a h U ≫ pullback.snd U.hom q = pullback.snd U.hom p ≫ a :=
  pullback.lift_snd ..

private theorem chartProjection_isPullback (a : Y ⟶ Z) (h : a ≫ q = p) (U : X.Etale) :
    IsPullback (chartProjection a h U) (pullback.snd U.hom p) (pullback.snd U.hom q) a := by
  apply IsPullback.flip
  refine IsPullback.of_bot ?_ (chartProjection_snd a h U).symm
    (IsPullback.of_hasPullback U.hom q).flip
  simpa only [chartProjection_fst, h] using (IsPullback.of_hasPullback U.hom p).flip

theorem chartProjection_surjective (a : Y ⟶ Z) (h : a ≫ q = p) (U : X.Etale)
    (ha : Function.Surjective a) : Function.Surjective (chartProjection a h U) := by
  intro z
  obtain ⟨y, hy⟩ := ha (pullback.snd U.hom q z)
  obtain ⟨x, hx, _⟩ := Scheme.exists_preimage_of_isPullback (chartProjection_isPullback a h U)
    z y hy.symm
  exact ⟨x, hx⟩

@[reassoc]
private theorem chartProjection_comp (a : Y ⟶ Z) (h : a ≫ q = p)
    (b : W ⟶ Y) (h' : b ≫ p = r) (U : X.Etale) :
    chartProjection b h' U ≫ chartProjection a h U =
      chartProjection (b ≫ a) ((Category.assoc _ _ _).trans ((congrArg (b ≫ ·) h).trans h')) U := by
  apply pullback.hom_ext <;> simp [Category.assoc]

@[reassoc]
private theorem baseChange_map_fst {U V : X.Etale} (g : U ⟶ V) (f : Y ⟶ X) :
    ((baseChange f).map g).left ≫ pullback.fst V.hom f = pullback.fst U.hom f ≫ g.left :=
  pullback.lift_fst ..

@[reassoc]
private theorem baseChange_map_snd {U V : X.Etale} (g : U ⟶ V) (f : Y ⟶ X) :
    ((baseChange f).map g).left ≫ pullback.snd V.hom f = pullback.snd U.hom f :=
  pullback.lift_snd ..

private theorem chartProjection_naturality (a : Y ⟶ Z) (h : a ≫ q = p)
    {U V : X.Etale} (g : U ⟶ V) :
    chartProjection a h U ≫ ((baseChange q).map g).left =
      ((baseChange p).map g).left ≫ chartProjection a h V := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChange_map_fst,
      chartProjection_fst, chartProjection_fst_assoc]
  · simp only [Category.assoc, baseChange_map_snd, baseChange_map_snd_assoc,
      chartProjection_snd]

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

/-- The direct image of continuous functions with discrete values. -/
abbrev continuousImage (f : Y ⟶ X) : Ab X := (pushforward f).obj (continuousSheaf Y M)

/-- Restriction along a map of schemes over the base gives a morphism
between their direct images of the discrete coefficient sheaves. -/
def restriction (a : Y ⟶ Z) (h : a ≫ q = p) : continuousImage M q ⟶ continuousImage M p :=
  ⟨{
    app := fun U => restrict (chartProjection a h U.unop) M
    naturality := by
      intro U V g
      apply ConcreteCategory.hom_ext
      intro s
      apply ContinuousMap.ext
      intro x
      let s' : C(((baseChange q).obj U.unop).left, M) := s
      exact congrArg (fun (f : ((baseChange p).obj V.unop).left ⟶
        ((baseChange q).obj U.unop).left) => s' (f x)) (chartProjection_naturality a h g.unop) }⟩

theorem restriction_comp (a : Y ⟶ Z) (h : a ≫ q = p) (b : W ⟶ Y) (h' : b ≫ p = r) :
    restriction M a h ≫ restriction M b h' =
      restriction M (b ≫ a) ((Category.assoc _ _ _).trans ((congrArg (b ≫ ·) h).trans h')) := by
  apply (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).map_injective
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ContinuousMap.ext
  intro x
  let s' : C(((baseChange q).obj U.unop).left, M) := s
  exact congrArg (fun (f : ((baseChange r).obj U.unop).left ⟶
    ((baseChange q).obj U.unop).left) => s' (f x)) (chartProjection_comp a h b h' U.unop)

theorem mono_restriction (a : Y ⟶ Z) (h : a ≫ q = p) (ha : Function.Surjective a) :
    Mono (restriction M a h) := by
  let L := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let ρ := L.map (restriction M a h)
  let : ∀ U, Mono (ρ.app U) := fun U => (AddCommGrpCat.mono_iff_injective _).mpr
    (restrict_injective _ (chartProjection_surjective a h U.unop ha) M)
  exact L.mono_of_mono_map (NatTrans.mono_of_mono_app ρ)

set_option maxHeartbeats 1600000 in
/-- On an affine étale chart, an additive family of sections of the
constant direct image descends to a single affine stage. -/
theorem exists_stage_on_chart [IsAffine X] [Finite M]
    {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (t : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ t.app i = f)
    (hSurj : ∀ i, Function.Surjective (c.π.app i : c.pt → D.obj i))
    (U : X.Etale) [IsAffine U.left] {A : AddCommGrpCat.{u}} [Finite A]
    (s : A ⟶ (continuousImage M f).obj.obj (op U)) :
    ∃ (i : I) (sᵢ : A ⟶ (continuousImage M (t.app i)).obj.obj (op U)),
      sᵢ ≫ (restriction M (c.π.app i) (hf i)).hom.app (op U) = s := by
  let : IsConnected I := IsCofiltered.isConnected I
  let : Nonempty I := IsCofiltered.nonempty
  let P := Over.pullback U.hom ⋙ Over.forget U.left
  let D' := Over.lift D t ⋙ P
  let d : Cone D' := P.mapCone (Over.liftCone D t c f hf)
  have hd : IsLimit d := isLimitOfPreserves P (Over.isLimitLiftCone D t c f hf hc)
  let e : ((baseChange f).obj U).left ≅ d.pt := pullbackSymmetry U.hom f
  let eᵢ (i : I) : ((baseChange (t.app i)).obj U).left ≅ D'.obj i :=
    pullbackSymmetry U.hom (t.app i)
  have hIso (i : I) : e.hom ≫ d.π.app i = chartProjection (c.π.app i) (hf i) U ≫ (eᵢ i).hom := by
    have hfst : d.π.app i ≫ pullback.fst (t.app i) U.hom = pullback.fst f U.hom ≫ c.π.app i :=
      pullback.lift_fst ..
    have hsnd : d.π.app i ≫ pullback.snd (t.app i) U.hom = pullback.snd f U.hom :=
      pullback.lift_snd ..
    apply pullback.hom_ext
    · change (e.hom ≫ d.π.app i) ≫ pullback.fst (t.app i) U.hom =
        (chartProjection (c.π.app i) (hf i) U ≫ (eᵢ i).hom) ≫ pullback.fst (t.app i) U.hom
      simp only [e, eᵢ, Category.assoc, hfst, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_fst_assoc, chartProjection_snd]
    · change (e.hom ≫ d.π.app i) ≫ pullback.snd (t.app i) U.hom =
        (chartProjection (c.π.app i) (hf i) U ≫ (eᵢ i).hom) ≫ pullback.snd (t.app i) U.hom
      simp only [e, eᵢ, Category.assoc, hsnd, pullbackSymmetry_hom_comp_snd, chartProjection_fst]
  have hSurj' (i : I) : Function.Surjective (d.π.app i : d.pt → D'.obj i) := by
    intro z
    obtain ⟨z', hz'⟩ := (eᵢ i).hom.surjective z
    let k := chartProjection (c.π.app i) (hf i) U
    obtain ⟨x, hx⟩ := chartProjection_surjective (c.π.app i) (hf i) U (hSurj i) z'
    exact ⟨e.hom x, (congrArg (fun (a : ((baseChange f).obj U).left ⟶ D'.obj i) => a x)
      (hIso i)).trans ((congrArg (eᵢ i).hom (show k x = z' from hx)).trans hz')⟩
  let u : U.left ⟶ X := U.hom
  let : IsAffineHom u := isAffineHom_of_isAffine u
  let : IsAffineHom U.hom := ‹IsAffineHom u›
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let : IsAffine d.pt := inferInstanceAs (IsAffine (pullback f U.hom))
  let : CompactSpace d.pt := inferInstance
  let (i : I) : IsAffine (D'.obj i) := inferInstanceAs (IsAffine (pullback (t.app i) U.hom))
  let {i j : I} (a : i ⟶ j) : IsAffineHom (D'.map a) := isAffineHom_of_isAffine _
  let s' := s ≫ restrict e.inv M
  obtain ⟨i, b, hb⟩ := exists_stage_additive d hd hSurj' s'
  refine ⟨i, b ≫ restrict (eᵢ i).hom M, ?_⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply ContinuousMap.ext
  intro x
  let g : C(D'.obj i, M) := b a
  have hb' := congrArg (fun (z : C(d.pt, M)) => z (e.hom x))
    (ConcreteCategory.congr_hom hb a)
  let sₐ : C(((baseChange f).obj U).left, M) := s a
  change g ((eᵢ i).hom (chartProjection (c.π.app i) (hf i) U x)) = sₐ x
  change g (d.π.app i (e.hom x)) = sₐ (e.inv (e.hom x)) at hb'
  rw [← Scheme.Hom.comp_apply, e.hom_inv_id] at hb'
  change g (d.π.app i (e.hom x)) = sₐ x at hb'
  exact (congrArg (fun (a : ((baseChange f).obj U).left ⟶ D'.obj i) => g (a x))
    (hIso i)).symm.trans hb'

end PhilipponEtaleConstantImageStage

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleRefinementAffine
  (finiteSubalgebraDiagram finiteSubalgebraCocone finiteSubalgebraIsColimit
    finite_surjective_of_fg_subalgebra structureMaps)


namespace PhilipponEtaleIntegralFiniteDiagram

universe u

private theorem subalgebra_projection_surjective (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (C : Subalgebra R S) :
    Surjective (Spec.map (CommRingCat.ofHom C.val.toRingHom)) := by
  let : Algebra.IsIntegral C S := Algebra.IsIntegral.tower_top R
  let : FaithfulSMul C S := (faithfulSMul_iff_algebraMap_injective C S).mpr Subtype.val_injective
  exact ⟨Algebra.IsIntegral.comap_surjective C S⟩

set_option maxHeartbeats 1400000 in
private theorem exists_finite_diagram_of_isoSpec {Y V : Scheme.{u}}
    (R S : CommRingCat.{u}) (eY : Y ≅ Spec R) (eV : V ≅ Spec S)
    (f : V ⟶ Y) [IsIntegralHom f] [Surjective f] :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (π : (Functor.const I).obj V ⟶ D) (t : D ⟶ (Functor.const I).obj Y),
      Nonempty (IsLimit (Cone.mk V π)) ∧
        (∀ i, π.app i ≫ t.app i = f) ∧ (∀ i, IsFinite (t.app i) ∧ Surjective (t.app i)) ∧
        (∀ i, Surjective (π.app i)) := by
  classical
  let b := Spec.preimage (eV.inv ≫ f ≫ eY.hom)
  have hb : Spec.map b = eV.inv ≫ f ≫ eY.hom := Spec.map_preimage _
  have hIntegral : IsIntegralHom (Spec.map b) :=
    hb.symm ▸ inferInstanceAs (IsIntegralHom (eV.inv ≫ f ≫ eY.hom))
  have hSurj : Surjective (Spec.map b) :=
    hb.symm ▸ inferInstanceAs (Surjective (eV.inv ≫ f ≫ eY.hom))
  let : Algebra R S := b.hom.toAlgebra
  let : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hIntegral)
  let ringDiagram := finiteSubalgebraDiagram R S
  let D := ringDiagram.op ⋙ Scheme.Spec
  let c₀ := Scheme.Spec.mapCone (finiteSubalgebraCocone R S).op
  let c := c₀.extend eV.hom
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec (finiteSubalgebraIsColimit R S).op
  have hc : IsLimit c := hc₀.extendIso eV.hom
  let t : D ⟶ (Functor.const _).obj Y :=
    { app := fun i => Spec.map ((structureMaps R S).app i.unop) ≫ eY.inv
      naturality := fun i j g => by
        have h := (structureMaps R S).naturality g.unop
        change 𝟙 _ ≫ (structureMaps R S).app i.unop =
          (structureMaps R S).app j.unop ≫ ringDiagram.map g.unop at h
        rw [Category.id_comp] at h
        change Spec.map (ringDiagram.map g.unop) ≫
          Spec.map ((structureMaps R S).app j.unop) ≫ eY.inv =
          (Spec.map ((structureMaps R S).app i.unop) ≫ eY.inv) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← h] }
  have ht (i : (Finset S)ᵒᵖ) : c.π.app i ≫ t.app i = f := by
    have hComp : (structureMaps R S).app i.unop ≫
        (finiteSubalgebraCocone R S).ι.app i.unop = b := by
      ext r
      rfl
    change (eV.hom ≫ Spec.map ((finiteSubalgebraCocone R S).ι.app i.unop)) ≫
      Spec.map ((structureMaps R S).app i.unop) ≫ eY.inv = f
    rw [Category.assoc eV.hom, ← Category.assoc (Spec.map ((finiteSubalgebraCocone R S).ι.app i.unop)),
      ← Spec.map_comp, hComp, hb]
    simp
  have hStages (i : (Finset S)ᵒᵖ) : IsFinite (t.app i) ∧ Surjective (t.app i) := by
    let C := Algebra.adjoin R (i.unop : Set S)
    have hFG : C.FG := Subalgebra.fg_def.mpr ⟨_, i.unop.finite_toSet, rfl⟩
    have hModel : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) := hSurj
    obtain ⟨hFin, hSurj⟩ := finite_surjective_of_fg_subalgebra hModel C hFG
    let _ := hFin
    let _ := hSurj
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ eY.inv) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ eY.inv)
    exact ⟨inferInstance, inferInstance⟩
  have hπ (i : (Finset S)ᵒᵖ) : Surjective (c.π.app i) := by
    let C := Algebra.adjoin R (i.unop : Set S)
    let p := Spec.map (CommRingCat.ofHom C.val.toRingHom)
    let : Surjective p := subalgebra_projection_surjective R S C
    change Surjective (eV.hom ≫ p)
    infer_instance
  exact ⟨(Finset S)ᵒᵖ, inferInstance, inferInstance, D, c.π, t, ⟨hc⟩, ht, hStages, hπ⟩

/-- An integral surjection over an affine scheme is a cofiltered limit of
finite surjections with surjective projections to the stages. -/
theorem exists_finite_surjective_limit_of_integral_with_projections {Y V : Scheme.{u}} [IsAffine Y]
    (f : V ⟶ Y) [IsIntegralHom f] [Surjective f] :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (π : (Functor.const I).obj V ⟶ D) (t : D ⟶ (Functor.const I).obj Y),
      Nonempty (IsLimit (Cone.mk V π)) ∧
        (∀ i, π.app i ≫ t.app i = f) ∧ (∀ i, IsFinite (t.app i) ∧ Surjective (t.app i)) ∧
        (∀ i, Surjective (π.app i)) := by
  let : IsAffine V := isAffine_of_isAffineHom f
  exact exists_finite_diagram_of_isoSpec _ _ Y.isoSpec V.isoSpec f

end PhilipponEtaleIntegralFiniteDiagram

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso)
open PhilipponEtaleConstantImageStage (continuousImage exists_stage_on_chart mono_restriction
  restriction restriction_comp)
open PhilipponEtaleFinitePresentations (ChartPresentation finiteEtalePresentations
  exists_chartPresentation generatorCoefficients generatorCoefficients_finite)
open PhilipponEtaleIntegralFiniteDiagram (exists_finite_surjective_limit_of_integral_with_projections)
open PhilipponFiniteRelationTransport (exists_factor_of_finite_generators)
open PhilipponFreeEtaleSheaf (freeSheaf homEquiv homEquiv_comp)


namespace PhilipponEtaleIntegralModelFactorization

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X : Scheme.{u}} [IsAffine X]

set_option maxHeartbeats 1500000 in
/-- A map from a finite étale presentation to a constant direct image
on a surjective inverse limit factors through one of its stages. -/
theorem exists_stage_factor {N : ℕ} (hN : N ≠ 0) {F : Ab X}
    (hF : finiteEtalePresentations X N F)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (t : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ t.app i = f)
    (hSurj : ∀ i, Function.Surjective (c.π.app i : c.pt → D.obj i))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    (m : F ⟶ continuousImage M f) :
    ∃ (i : I) (mᵢ : F ⟶ continuousImage M (t.app i)),
      mᵢ ≫ restriction M (c.π.app i) (hf i) = m := by
  obtain ⟨p, ⟨e⟩⟩ := exists_chartPresentation hF
  let Q (i : Iᵒᵖ) := continuousImage M (t.app i.unop)
  let ι (i : Iᵒᵖ) : Q i ⟶ continuousImage M f := restriction M (c.π.app i.unop) (hf i.unop)
  let hTrans {i j : Iᵒᵖ} (a : i ⟶ j) : D.map a.unop ≫ t.app i.unop = t.app j.unop :=
    (t.naturality a.unop).trans (Category.comp_id _)
  let b {i j : Iᵒᵖ} (a : i ⟶ j) : Q i ⟶ Q j := restriction M (D.map a.unop) (@hTrans i j a)
  have hb {i j : Iᵒᵖ} (a : i ⟶ j) : @b i j a ≫ ι j = ι i := by
    dsimp only [b, ι]
    rw [restriction_comp]
    congr 1
    exact c.w a.unop
  let G (j : p.generators) := freeSheaf (p.generator j) (generatorCoefficients N)
  let : Finite (generatorCoefficients.{u} N) := (generatorCoefficients_finite N hN).1
  obtain ⟨i, mᵢ, hi⟩ := exists_factor_of_finite_generators G p.differential (e.hom ≫ m) Q ι
    (fun i => mono_restriction M _ _ (hSurj i.unop)) (fun {i j} a => @b i j a)
    (fun {i j} a => @hb i j a) (by
      intro j
      let U := p.generator j
      let : IsAffine U.left := p.affineGenerator j
      let H := generatorCoefficients.{u} N
      let k : freeSheaf U H ⟶ continuousImage M f := Sigma.ι G j ≫ cokernel.π p.differential ≫ e.hom ≫ m
      obtain ⟨i, s, hs⟩ := exists_stage_on_chart M c hc t f hf hSurj U (homEquiv U H _ k)
      refine ⟨op i, (homEquiv U H _).symm s, ?_⟩
      change (homEquiv U H _).symm s ≫ restriction M (c.π.app i) (hf i) = k
      apply (homEquiv U H _).injective
      rw [homEquiv_comp, Equiv.apply_symm_apply]
      exact hs)
  refine ⟨i.unop, e.inv ≫ mᵢ, ?_⟩
  change (e.inv ≫ mᵢ) ≫ ι i = m
  rw [Category.assoc, hi, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 1500000 in
/-- Any map from a finite étale presentation into the constant direct
image of an integral cover of an affine scheme factors through a finite
cover of the same closed subscheme. -/
theorem exists_finite_factor {N : ℕ} (hN : N ≠ 0) {F : Ab X}
    (hF : finiteEtalePresentations X N F) {T Y : Scheme.{u}} [IsAffine T]
    (i : T ⟶ X) (p : Y ⟶ T) [IsIntegralHom p] [Surjective p]
    (M : AddCommGrpCat.{u}) [Finite M]
    (m : F ⟶ (pushforward (p ≫ i)).obj ((constantSheaf Y.smallEtaleTopology _).obj M)) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ T) (_ : IsFinite q)
      (m₀ : F ⟶ (pushforward (q ≫ i)).obj ((constantSheaf Z.smallEtaleTopology _).obj M))
      (a : (pushforward (q ≫ i)).obj ((constantSheaf Z.smallEtaleTopology _).obj M) ⟶
        (pushforward (p ≫ i)).obj ((constantSheaf Y.smallEtaleTopology _).obj M)), m₀ ≫ a = m := by
  let M₀ : Type u := M
  let : TopologicalSpace M₀ := ⊥
  let : DiscreteTopology M₀ := ⟨rfl⟩
  let : AddCommGroup M₀ := inferInstanceAs (AddCommGroup M)
  let : Finite M₀ := inferInstanceAs (Finite M)
  obtain ⟨I, _, _, D, π, t, ⟨hc⟩, ht, hStage, hπ⟩ :=
    exists_finite_surjective_limit_of_integral_with_projections p
  let c := Cone.mk Y π
  let t' := t ≫ (Functor.const I).map i
  let (j : I) : IsAffine (D.obj j) := by
    let q : D.obj j ⟶ T := t.app j
    let : IsFinite q := (hStage j).1
    exact isAffine_of_isAffineHom q
  have ht' (j : I) : c.π.app j ≫ t'.app j = p ≫ i := by
    change π.app j ≫ t.app j ≫ i = p ≫ i
    rw [← Category.assoc, ht]
  let hM (S : Scheme.{u}) := constantSheafIso S M₀
  let d := (pushforward (p ≫ i)).mapIso (hM Y)
  obtain ⟨j, g, hg⟩ := exists_stage_factor hN hF c hc t' (p ≫ i) ht'
    (fun j => (hπ j).surj) M₀ (m ≫ d.hom)
  let q : D.obj j ⟶ T := t.app j
  let d₀ := (pushforward (q ≫ i)).mapIso (hM (D.obj j))
  let k : continuousImage M₀ (q ≫ i) ⟶ continuousImage M₀ (p ≫ i) :=
    restriction M₀ (π.app j) (ht' j)
  have hk : g ≫ k = m ≫ d.hom := hg
  refine ⟨D.obj j, q, (hStage j).1, g ≫ d₀.inv, d₀.hom ≫ k ≫ d.inv, ?_⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ d.inv) hk).trans
      ((Category.assoc m d.hom d.inv).trans (by rw [d.hom_inv_id, Category.comp_id])))

end PhilipponEtaleIntegralModelFactorization

end

end


