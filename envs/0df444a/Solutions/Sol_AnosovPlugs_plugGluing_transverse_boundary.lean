-- Prove2me | solution 1 for AnosovPlugs.plugGluing_transverse_boundary
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T18:57:02.723991+00:00
-- url     : https://prove2.me/submissions/1eea8138-b591-4b5b-bb4c-c2d5fd6927b5

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

/-- A C¹ map with injective derivative at an interior point sends it to an interior point.
In dimension 3 to 3, an injective derivative is surjective, and Mathlib has the surjective
version. -/
theorem interiorPoint_image_of_mfderiv_injective
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (f : M → N) (x : M) (hf : ContMDiffAt I3 I3 1 f x)
    (hinj : Function.Injective (mfderiv I3 I3 f x)) (hx : x ∈ I3.interior M) :
    f x ∈ I3.interior N := by
  have hsurj : Function.Surjective (mfderiv I3 I3 f x) := by
    let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (mfderiv I3 I3 f x).toLinearMap
    exact LinearMap.surjective_of_injective (f := L) (fun a b hab => hinj hab)
  exact (hf.mdifferentiableAt one_ne_zero).isInteriorPoint_of_surjective_mfderiv hsurj hx


/-- Linear algebra step: an injective linear map that keeps the hyperplane `v 0 = 0` sends a vector
with nonzero coordinate `0` to a vector with nonzero coordinate `0`. -/
lemma linAlg_aux (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hinj : Function.Injective D)
    (hD : ∀ h : EuclideanSpace ℝ (Fin 3), h 0 = 0 → (D h) 0 = 0)
    (v : EuclideanSpace ℝ (Fin 3)) (hv : v 0 ≠ 0) : (D v) 0 ≠ 0 := by
  set H : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    LinearMap.ker (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).toLinearMap with hH
  have hmem : ∀ w, w ∈ H ↔ w 0 = 0 := by
    intro w
    simp [hH]
  have hle : H.map (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact (hmem _).2 (hD h ((hmem h).1 hh))
  have hrank : Module.finrank ℝ (H.map (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)))
      = Module.finrank ℝ H :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) hinj H)).symm
  have heq := Submodule.eq_of_le_of_finrank_eq hle hrank
  intro h0
  have : D v ∈ H := (hmem _).2 h0
  rw [← heq] at this
  obtain ⟨w, hw, hDw⟩ := this
  have : w = v := hinj hDw
  subst this
  exact hv ((hmem _).1 hw)

/-- Analytic step: a map of the half space into the half space that fixes the boundary hyperplane
at `a` has a derivative that keeps the hyperplane `h 0 = 0`. -/
lemma deriv_aux (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (a : EuclideanSpace ℝ (Fin 3))
    (hFD : HasFDerivWithinAt F D (range I3) a)
    (ha : a 0 = 0) (hFa : (F a) 0 = 0) (hrange : ∀ y, 0 ≤ (F y) 0)
    (h : EuclideanSpace ℝ (Fin 3)) (hh : h 0 = 0) : (D h) 0 = 0 := by
  let γ : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => a + t • h
  have hγ : HasDerivAt γ h 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add a
    simpa only [id_eq, one_smul] using this
  have hmaps : MapsTo γ univ (range I3) := by
    intro t _
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp [γ, ha, hh]
  have h1 : HasDerivWithinAt (F ∘ γ) (D h) univ 0 := by
    have h0 : γ 0 = a := by simp [γ]
    rw [← h0] at hFD
    exact hFD.comp_hasDerivWithinAt (x := 0) hγ.hasDerivWithinAt hmaps
  have h2 : HasDerivAt (fun t => (F (γ t)) 0) ((D h) 0) 0 := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt.comp_hasDerivAt (x := (0:ℝ))
      (hasDerivWithinAt_univ.mp h1)
    exact this
  have hmin : IsLocalMin (fun t => (F (γ t)) 0) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h0 : γ 0 = a := by simp [γ]
    simp only [h0, hFa]
    exact hrange _
  exact hmin.hasDerivAt_eq_zero h2

theorem normalCoord_mfderiv_ne_zero_of_isBoundaryPoint
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (f : M → N) (x : M) (hf : ContMDiffAt I3 I3 1 f x)
    (hinj : Function.Injective (mfderiv I3 I3 f x))
    (hx : x ∈ I3.boundary M) (hfx : f x ∈ I3.boundary N)
    (v : TangentSpace I3 x) (hv : normalCoord v ≠ 0) :
    normalCoord (mfderiv I3 I3 f x v) ≠ 0 := by
  have hmd : MDifferentiableAt I3 I3 f x := hf.mdifferentiableAt one_ne_zero
  have hF := (hmd.hasMFDerivAt).2
  have ha : (extChartAt I3 x x) 0 = 0 := by
    have := (I3.isBoundaryPoint_iff (x := x)).1 hx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at this
    exact this.symm
  have hfa : (extChartAt I3 (f x) (f x)) 0 = 0 := by
    have := (I3.isBoundaryPoint_iff (x := f x)).1 hfx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at this
    exact this.symm
  have hFa : (writtenInExtChartAt I3 I3 x f (extChartAt I3 x x)) 0 = 0 := by
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt I3 x).left_inv (mem_extChartAt_source x)]
    exact hfa
  have hrange : ∀ y, 0 ≤ (writtenInExtChartAt I3 I3 x f y) 0 := by
    intro y
    have : writtenInExtChartAt I3 I3 x f y ∈ range I3 := by
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
      exact mem_range_self _
    rw [range_modelWithCornersEuclideanHalfSpace] at this
    exact this
  exact linAlg_aux _ hinj
    (deriv_aux _ _ _ hF ha hFa hrange) v hv

theorem solution
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsPlug X) (hY : IsPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    ∀ w ∈ I3.boundary W, normalCoord (Z w) ≠ 0 := by
  intro w hw
  obtain ⟨hcU, hcV, -, -, hdU, hdV, hcover, -, hZU, hZV⟩ := hglue
  have hw' : w ∈ range iU ∪ range iV := by rw [hcover]; exact mem_univ w
  rcases hw' with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · have hx : x ∈ I3.boundary U := by
      rcases I3.isInteriorPoint_or_isBoundaryPoint x with h | h
      · exact absurd (interiorPoint_image_of_mfderiv_injective iU x (hcU x) (hdU x) h)
          (fun h' => Set.disjoint_left.1 I3.disjoint_interior_boundary h' hw)
      · exact h
    rw [← hZU x]
    exact normalCoord_mfderiv_ne_zero_of_isBoundaryPoint iU x (hcU x) (hdU x) hx hw (X x)
      (hX.2.2 x hx)
  · have hy : y ∈ I3.boundary V := by
      rcases I3.isInteriorPoint_or_isBoundaryPoint y with h | h
      · exact absurd (interiorPoint_image_of_mfderiv_injective iV y (hcV y) (hdV y) h)
          (fun h' => Set.disjoint_left.1 I3.disjoint_interior_boundary h' hw)
      · exact h
    rw [← hZV y]
    exact normalCoord_mfderiv_ne_zero_of_isBoundaryPoint iV y (hcV y) (hdV y) hy hw (Y y)
      (hY.2.2 y hy)
