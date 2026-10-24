-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_surjective_cover_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T15:05:05.584676+00:00
-- url     : https://prove2.me/submissions/ae3989ec-55fc-4a1e-955f-6223bc1eea70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_integral_projective

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HomogeneousIdeal HomogeneousLocalization
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponIntegralMultisection

lemma reduced_vanishing_subscheme {X : Scheme.{u}} (S : TopologicalSpace.Closeds X) :
    AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hred (U : X.affineOpens) : AlgebraicGeometry.IsReduced
      (Spec (.of (Γ(X, U) ⧸ I.ideal U))) := by
    have hrad : (I.ideal U).IsRadical := by
      change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (S : Set X))).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hrad
    infer_instance
  letI (U : I.subschemeCover.openCover.I₀) :
      AlgebraicGeometry.IsReduced (I.subschemeCover.openCover.X U) := hred U
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

lemma integral_reduced_closure {X : Scheme.{u}} (x : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({x} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme := by
  let S : TopologicalSpace.Closeds X := ⟨closure {x}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have : AlgebraicGeometry.IsReduced I.subscheme := reduced_vanishing_subscheme S
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    have hsupport : (I.support : Set X) = closure ({x} : Set X) := by
      simp [I, S]
    rw [hsupport]
    exact Subtype.irreducibleSpace isIrreducible_singleton.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _


end PhilipponIntegralMultisection

namespace PhilipponProjectiveCoordinateEmbedding

lemma localRingHom_surjective_of_graded_section
    {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (s : ℬ →+*ᵍ 𝒜) (hs : ∀ b, f (s b) = b)
    (J : Ideal B) [J.IsPrime] :
    Function.Surjective (HomogeneousLocalization.localRingHom f (J.comap f) J rfl) := by
  intro z
  obtain ⟨c, rfl⟩ := z.mk_surjective
  let d : NumDenSameDeg 𝒜 (J.comap f).primeCompl :=
    { deg := c.deg
      num := ⟨s c.num, s.2 c.num.property⟩
      den := ⟨s c.den, s.2 c.den.property⟩
      den_mem := by
        change f (s c.den) ∉ J
        rw [hs]
        exact c.den_mem }
  refine ⟨HomogeneousLocalization.mk d, ?_⟩
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.localRingHom, HomogeneousLocalization.map_mk,
    d, hs, HomogeneousLocalization.val_mk]

lemma isClosedImmersion_proj_map_of_graded_section
    {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (s : ℬ →+*ᵍ 𝒜) (hs : ∀ b, f (s b) = b)
    (hf : ℬ₊ ≤ 𝒜₊.map f) [IsProper (Proj.map f hf)] :
    IsClosedImmersion (Proj.map f hf) := by
  let m := Proj.map f hf
  have hsurj : Function.Surjective f := fun b => ⟨s b, hs b⟩
  have hinj : Function.Injective m := by
    intro x y h
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    apply Ideal.comap_injective_of_surjective f.toRingHom hsurj
    exact congrArg (fun z : ProjectiveSpectrum 𝒜 => z.asHomogeneousIdeal.toIdeal) h
  have : SurjectiveOnStalks m := by
    constructor
    intro x
    change Function.Surjective ((Proj.sheafedSpaceMap f hf).hom.stalkMap x)
    rw [← Proj.localRingHom_comp_stalkIso]
    exact ((ConcreteCategory.bijective_of_isIso (Proj.stalkIso ℬ x).inv).surjective).comp
      ((localRingHom_surjective_of_graded_section f s hs _).comp
        (ConcreteCategory.bijective_of_isIso
          (Proj.stalkIso 𝒜 (ProjectiveSpectrum.comap f hf x)).hom).surjective)
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    m.continuous hinj m.isClosedMap⟩

lemma proj_map_toSpecZero
    {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι ℬ (f s.2) (f.2 s.2.2) s.1.2 ≫
      (Proj.map f hf ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (f s.2) (f.2 s.2.2) s.1.2 ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 s.2 s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]

section Coordinates

variable {K : Type u} [CommRing K] {m n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def variableProjection (e : Fin (m + 1) ↪ Fin (n + 1)) (j : Fin (n + 1)) :
    MvPolynomial (Fin (m + 1)) K := by
  classical
  exact if h : ∃ i, e i = j then MvPolynomial.X (Classical.choose h) else 0

@[simp] lemma variableProjection_apply (e : Fin (m + 1) ↪ Fin (n + 1))
    (i : Fin (m + 1)) : variableProjection (K := K) e (e i) = MvPolynomial.X i := by
  classical
  rw [variableProjection, dif_pos ⟨i, rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ j, e j = e i from ⟨i, rfl⟩))

lemma variableProjection_homogeneous (e : Fin (m + 1) ↪ Fin (n + 1)) (j : Fin (n + 1)) :
    (variableProjection (K := K) e j).IsHomogeneous 1 := by
  classical
  unfold variableProjection
  split
  · exact MvPolynomial.isHomogeneous_X _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

def projection (e : Fin (m + 1) ↪ Fin (n + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K where
  toRingHom := MvPolynomial.eval₂Hom MvPolynomial.C (variableProjection e)
  map_mem := by
    intro d p hp
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    change (MvPolynomial.eval₂ MvPolynomial.C (variableProjection e) p).IsHomogeneous d
    simpa only [one_mul] using hp.eval₂ MvPolynomial.C (variableProjection e)
      (fun _ => MvPolynomial.isHomogeneous_C _ _) (variableProjection_homogeneous e)

def sectionMap (e : Fin (m + 1) ↪ Fin (n + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K where
  toRingHom := (MvPolynomial.rename e).toRingHom
  map_mem := by
    intro d p hp
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    exact hp.rename_isHomogeneous

@[simp] lemma projection_X (e : Fin (m + 1) ↪ Fin (n + 1)) (i : Fin (m + 1)) :
    projection (K := K) e (MvPolynomial.X (e i)) = MvPolynomial.X i := by
  simp [projection]

@[simp] lemma projection_C (e : Fin (m + 1) ↪ Fin (n + 1)) (r : K) :
    projection e (MvPolynomial.C r) = MvPolynomial.C r := by simp [projection]

lemma projection_section (e : Fin (m + 1) ↪ Fin (n + 1)) (p : MvPolynomial (Fin (m + 1)) K) :
    projection e (sectionMap e p) = p := by
  have h : (projection (K := K) e).toRingHom.comp (sectionMap e).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sectionMap]
    · intro i
      simp [sectionMap]
  exact congrArg (fun f : MvPolynomial (Fin (m + 1)) K →+* MvPolynomial _ K => f p) h

lemma irrelevant_le_map_projection (e : Fin (m + 1) ↪ Fin (n + 1)) :
    (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)₊ ≤
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)₊.map (projection e) := by
  rw [← toIdeal_le_toIdeal_iff]
  apply le_trans (ProjSpace.irrelevant_le_span_X K m)
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← projection_X e i]
  apply Ideal.mem_map_of_mem
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < 1 by omega) (ProjSpace.X_mem_one K n (e i))

def coordinateEmbedding (e : Fin (m + 1) ↪ Fin (n + 1)) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) :=
  Proj.map (projection e) (irrelevant_le_map_projection e)

@[reassoc] lemma coordinateEmbedding_comp_pi (e : Fin (m + 1) ↪ Fin (n + 1)) :
    coordinateEmbedding (K := K) e ≫ ProjSpace.π K n = ProjSpace.π K m := by
  unfold coordinateEmbedding ProjSpace.π
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact projection_C e r

instance coordinateEmbedding_isClosedImmersion (e : Fin (m + 1) ↪ Fin (n + 1)) :
    IsClosedImmersion (coordinateEmbedding (K := K) e) := by
  have : IsProper (coordinateEmbedding (K := K) e ≫ ProjSpace.π K n) := by
    rw [coordinateEmbedding_comp_pi]
    infer_instance
  have hproper : IsProper (coordinateEmbedding (K := K) e) :=
    IsProper.of_comp _ (ProjSpace.π K n)
  change IsProper (Proj.map (projection e) (irrelevant_le_map_projection e)) at hproper
  letI := hproper
  exact isClosedImmersion_proj_map_of_graded_section
    (projection e) (sectionMap e) (projection_section e) _

lemma X_mem_coordinateEmbedding_of_not_mem (e : Fin (m + 1) ↪ Fin (n + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e)
    (x : Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)) :
    MvPolynomial.X j ∈ (coordinateEmbedding e x).asHomogeneousIdeal := by
  change projection e (MvPolynomial.X j) ∈ x.asHomogeneousIdeal
  simp [projection, variableProjection, show ¬ ∃ i, e i = j from hj]

lemma disjoint_range_coordinateEmbedding {l : ℕ}
    (e : Fin (m + 1) ↪ Fin (n + 1)) (f : Fin (l + 1) ↪ Fin (n + 1))
    (hef : Disjoint (Set.range e) (Set.range f)) :
    Disjoint (Set.range (coordinateEmbedding (K := K) e))
      (Set.range (coordinateEmbedding (K := K) f)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have hvars : ∀ j : Fin (n + 1),
      MvPolynomial.X j ∈ (coordinateEmbedding (K := K) e x).asHomogeneousIdeal := by
    intro j
    by_cases hj : j ∈ Set.range e
    · rw [← hy]
      exact X_mem_coordinateEmbedding_of_not_mem f j
        (fun h => Set.disjoint_left.mp hef hj h) y
    · exact X_mem_coordinateEmbedding_of_not_mem e j hj x
  apply (coordinateEmbedding (K := K) e x).not_irrelevant_le
  apply le_trans (ProjSpace.irrelevant_le_span_X K n)
  exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hvars j)

end Coordinates

lemma exists_disjoint_coordinate_embeddings {A : Type u} [Fintype A] (d : A → ℕ) :
    ∃ (N : ℕ) (e : ∀ a, Fin (d a + 1) ↪ Fin (N + 1)),
      Pairwise (fun a b => Disjoint (Set.range (e a)) (Set.range (e b))) := by
  classical
  let B := Σ a, Fin (d a + 1)
  let e₀ : B ↪ Fin (Fintype.card B + 1) :=
    (Fintype.equivFin B).toEmbedding.trans Fin.castSuccEmb
  let e (a : A) : Fin (d a + 1) ↪ Fin (Fintype.card B + 1) :=
    (Function.Embedding.sigmaMk a).trans e₀
  refine ⟨Fintype.card B, e, ?_⟩
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  apply hab
  have heq : (⟨a, i⟩ : B) = ⟨b, j⟩ := e₀.injective (hi.trans hj.symm)
  exact congrArg Sigma.fst heq

end PhilipponProjectiveCoordinateEmbedding

namespace PhilipponIntegralProjectiveCover

lemma exists_integral_closed_dominating {X Z : Scheme.{u}} [IsIntegral X]
    (p : Z ⟶ X) [IsProper p] [Surjective p] :
    ∃ (W : Scheme.{u}) (i : W ⟶ Z),
      IsIntegral W ∧ IsClosedImmersion i ∧ Surjective (i ≫ p) := by
  classical
  obtain ⟨z, hz⟩ := p.surjective (genericPoint X)
  let S : Closeds Z := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal S
  let W := I.subscheme
  let i : W ⟶ Z := I.subschemeι
  let g := i ≫ p
  letI : IsIntegral W := PhilipponIntegralMultisection.integral_reduced_closure z
  have hsupport : (I.support : Set Z) = closure ({z} : Set Z) := by simp [I, S]
  let wz : W := ⟨z, by
    change z ∈ (I.support : Set Z)
    rw [hsupport]
    exact subset_closure (Set.mem_singleton z)⟩
  have hgen : g wz = genericPoint X := hz
  have hsurj : Surjective g := by
    constructor
    have hc : IsClosed (Set.range g) := by
      simpa only [Set.image_univ] using g.isClosedMap _ isClosed_univ
    have hall : Set.univ ⊆ Set.range g := by
      rw [← genericPoint_spec X]
      exact closure_minimal (Set.singleton_subset_iff.mpr ⟨wz, hgen⟩) hc
    exact fun x => hall (Set.mem_univ x)
  exact ⟨W, i, inferInstance, inferInstance, hsurj⟩

lemma chow_map_surjective {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (D : ChowDatumProj π) : Surjective D.p := by
  have hU : (D.U : Set X) ⊆ Set.range D.p := by
    intro x hx
    obtain ⟨q, hq⟩ := (pullback.snd D.p D.U.ι).surjective ⟨x, hx⟩
    refine ⟨pullback.fst D.p D.U.ι q, ?_⟩
    have h := congrArg (fun f : pullback D.p D.U.ι ⟶ X => f q)
      (pullback.condition (f := D.p) (g := D.U.ι))
    simpa only [Scheme.Hom.comp_apply, hq, Scheme.Opens.ι_apply] using h
  have hc : IsClosed (Set.range D.p) := by
    simpa only [Set.image_univ] using D.p.isClosedMap _ isClosed_univ
  have hall : Set.univ ⊆ Set.range D.p := by
    rw [← D.hU_dense.closure_eq]
    exact closure_minimal hU hc
  exact ⟨fun x => hall (Set.mem_univ x)⟩

theorem exists_integral_projective_cover {K : Type u} [Field K] {X : Scheme.{u}}
    [IsIntegral X] (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (W : Scheme.{u}) (f : W ⟶ X),
      IsIntegral W ∧ IsProper f ∧ Surjective f ∧
      ∃ (n : ℕ) (j : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K n = f ≫ π := by
  obtain ⟨D⟩ := ChowDatumProj.nonempty_of π (ChowDatum.nonempty π)
  letI : Surjective D.p := chow_map_surjective π D
  obtain ⟨W, i, hW, hi, hsurj⟩ := exists_integral_closed_dominating D.p
  letI := hW
  letI := hi
  refine ⟨W, i ≫ D.p, hW, inferInstance, hsurj, D.Nd, i ≫ D.ιN,
    inferInstance, ?_⟩
  rw [Category.assoc, D.hoverN, ← Category.assoc]

lemma integral_vanishing_subscheme {X : Scheme.{u}} (S : Closeds X)
    (hS : IsIrreducible (S : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have : AlgebraicGeometry.IsReduced I.subscheme :=
    PhilipponIntegralMultisection.reduced_vanishing_subscheme S
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    have hs : (I.support : Set X) = S := by simp [I]
    rw [hs]
    exact Subtype.irreducibleSpace hS
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem exists_finite_integral_projective_family {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (A : Type u) (_ : Fintype A) (Y : A → Scheme.{u}) (f : ∀ a, Y a ⟶ X),
      (∀ a, IsIntegral (Y a)) ∧ (∀ a, IsProper (f a)) ∧
      (⋃ a, Set.range (f a)) = Set.univ ∧
      ∀ a, ∃ (n : ℕ)
        (j : Y a ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K n = f a ≫ π := by
  classical
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  let A := irreducibleComponents X
  letI : Fintype A := NoetherianSpace.finite_irreducibleComponents.fintype
  have each (a : A) :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsIntegral Y ∧ IsProper f ∧ Set.range f = a.val ∧
        ∃ (n : ℕ)
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K n = f ≫ π := by
    let S : Closeds X := ⟨a.val, isClosed_of_mem_irreducibleComponents _ a.property⟩
    let I := Scheme.IdealSheafData.vanishingIdeal S
    let W := I.subscheme
    let ι : W ⟶ X := I.subschemeι
    letI : IsIntegral W := integral_vanishing_subscheme S a.property.1
    obtain ⟨Y, f, hY, hp, hs, n, j, hj, hover⟩ :=
      exists_integral_projective_cover (ι ≫ π)
    letI := hp
    letI := hs
    refine ⟨Y, f ≫ ι, hY, inferInstance, ?_, n, j, hj, ?_⟩
    · rw [range_eq_range_of_surjective (f ≫ ι) ι f rfl]
      change Set.range I.subschemeι = a.val
      calc
        Set.range I.subschemeι = (I.support : Set X) := I.range_subschemeι
        _ = a.val := by simp [I, S]
    · simpa only [Category.assoc] using hover
  choose Y f hY hp hr hemb using each
  refine ⟨A, inferInstance, Y, f, hY, hp, ?_, hemb⟩
  apply Set.eq_univ_iff_forall.mpr
  intro x
  let a : A := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  apply Set.mem_iUnion.mpr
  refine ⟨a, ?_⟩
  rw [hr a]
  exact mem_irreducibleComponent

open scoped Function in
lemma isClosedImmersion_sigmaDesc {A : Type u} [Finite A]
    {Y : A → Scheme.{u}} {X : Scheme.{u}} (f : ∀ a, Y a ⟶ X)
    [∀ a, IsClosedImmersion (f a)]
    (hf : Pairwise (Disjoint on (Set.range <| f ·))) :
    IsClosedImmersion (Sigma.desc f) := by
  have : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) (fun _ => inferInstance)
  constructor
  suffices Topology.IsClosedEmbedding (Sigma.desc f ∘ sigmaMk Y) by
    convert! this.comp (sigmaMk Y).symm.isClosedEmbedding using 1
    ext x
    simp
  refine .of_continuous_injective_isClosedMap ?_ ?_ ?_
  · fun_prop
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hxy : f a x = f b y := by
      simpa [← Scheme.Hom.comp_apply] using h
    obtain rfl : a = b := by
      by_contra hne
      exact Set.disjoint_iff_forall_ne.mp (hf hne) ⟨x, rfl⟩ ⟨y, hxy.symm⟩ rfl
    rw [(f a).isClosedEmbedding.injective hxy]
  · intro S hS
    have heq : (Sigma.desc f ∘ sigmaMk Y) '' S =
        ⋃ a, (f a) '' ((fun x : Y a => (⟨a, x⟩ : Σ b, Y b)) ⁻¹' S) := by
      ext z
      simp only [Set.mem_image, Set.mem_iUnion, Sigma.exists]
      constructor
      · rintro ⟨a, x, hx, rfl⟩
        refine ⟨a, x, hx, ?_⟩
        simp [← Scheme.Hom.comp_apply]
      · rintro ⟨a, x, hx, rfl⟩
        refine ⟨a, x, hx, ?_⟩
        simp [← Scheme.Hom.comp_apply]
    rw [heq]
    exact isClosed_iUnion_of_finite (fun a =>
      (f a).isClosedEmbedding.isClosedMap _ (hS.preimage continuous_sigmaMk))

theorem exists_projective_embedding_sigma {K : Type u} [CommRing K]
    {A : Type u} [Fintype A] (Y : A → Scheme.{u})
    (π : ∀ a, Y a ⟶ Spec (.of K)) (d : A → ℕ)
    (j : ∀ a, Y a ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d a + 1)) K))
    [∀ a, IsClosedImmersion (j a)] (hj : ∀ a, j a ≫ ProjSpace.π K (d a) = π a) :
    ∃ (N : ℕ) (i : (∐ Y) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)),
      IsClosedImmersion i ∧ i ≫ ProjSpace.π K N = Sigma.desc π := by
  classical
  obtain ⟨N, e, he⟩ :=
    PhilipponProjectiveCoordinateEmbedding.exists_disjoint_coordinate_embeddings d
  let f (a : A) := j a ≫ PhilipponProjectiveCoordinateEmbedding.coordinateEmbedding (e a)
  letI (a : A) : IsClosedImmersion (f a) := inferInstance
  have hdisj : Pairwise (fun a b => Disjoint (Set.range (f a)) (Set.range (f b))) := by
    intro a b hab
    apply (PhilipponProjectiveCoordinateEmbedding.disjoint_range_coordinateEmbedding
      (K := K) (e a) (e b) (he hab)).mono
    · rintro _ ⟨x, rfl⟩
      exact ⟨j a x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨j b x, rfl⟩
  refine ⟨N, Sigma.desc f, isClosedImmersion_sigmaDesc f hdisj, ?_⟩
  apply Sigma.hom_ext
  intro a
  simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
  change (j a ≫ PhilipponProjectiveCoordinateEmbedding.coordinateEmbedding (e a)) ≫
    ProjSpace.π K N = π a
  rw [Category.assoc,
    PhilipponProjectiveCoordinateEmbedding.coordinateEmbedding_comp_pi, hj]

theorem smooth_projective_cover_of_integral_projective_covers
    (K : Type u) [Field K] [IsAlgClosed K]
    (hcover : ∀ {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
      [IsIntegral X] [IsProper π] (n : ℕ)
      (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
      [IsClosedImmersion i], i ≫ ProjSpace.π K n = π →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
        ∃ (m : ℕ)
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π)
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (n : ℕ)
        (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π K n = f ≫ π := by
  classical
  obtain ⟨A, hA, Y, f, hY, hf, hsurj, hemb⟩ := exists_finite_integral_projective_family π
  letI := hA
  letI (a : A) := hY a
  letI (a : A) := hf a
  have each (a : A) :
      ∃ (Z : Scheme.{u}) (g : Z ⟶ Y a),
        IsIntegral Z ∧ IsProper g ∧ Surjective g ∧ Smooth (g ≫ (f a ≫ π)) ∧
        ∃ (m : ℕ)
          (j : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = g ≫ (f a ≫ π) := by
    obtain ⟨n, i, hi, hover⟩ := hemb a
    letI := hi
    exact hcover (f a ≫ π) n i hover
  choose Z g hZ hg hgs hsmooth n j hj hover using each
  letI (a : A) := hgs a
  letI (a : A) := hsmooth a
  letI (a : A) := hj a
  let q (a : A) := g a ≫ (f a ≫ π)
  let p (a : A) := g a ≫ f a
  let d : (∐ Z) ⟶ X := Sigma.desc p
  have hd : d ≫ π = Sigma.desc q := by
    apply Sigma.hom_ext
    intro a
    simp [d, p, q]
  obtain ⟨N, i, hi, hiq⟩ := exists_projective_embedding_sigma Z q n j hover
  letI := hi
  have hproper : IsProper (d ≫ π) := by
    rw [hd, ← hiq]
    infer_instance
  letI := hproper
  have hp : IsProper d := IsProper.of_comp d π
  have hsd : Smooth (d ≫ π) := by
    rw [hd]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth) (fun a => hsmooth a)
  have hsurjd : Surjective d := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    have hprange (a : A) : Set.range (p a) = Set.range (f a) :=
      range_eq_range_of_surjective (p a) (f a) (g a) rfl
    simpa only [hprange] using hsurj
  refine ⟨∐ Z, d, hp, hsurjd, hsd, N, i, hi, ?_⟩
  rw [hd]
  exact hiq

end PhilipponIntegralProjectiveCover

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
        ∃ (n : ℕ)
          (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
          IsClosedImmersion i ∧ i ≫ ProjSpace.π K n = f ≫ π  := by
  refine PhilipponIntegralProjectiveCover.smooth_projective_cover_of_integral_projective_covers K ?_ π
  intro Z z hZ hz n i hi hover
  exact AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective K z n i hover
