-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_sigma_factor_of_localRing
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:47.442208+00:00
-- url     : https://prove2.me/submissions/0085c460-51f1-4582-aaa8-ca2a070cd026

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing NeronModelInfra

namespace AlgebraicGeometry.Scheme

/-- A point over a local ring factors through a unique coproduct component.
This restriction on the source is essential. -/
theorem _root_.solution
    {ι : Type} (X : ι → Scheme.{0})
    {K : Type} [CommRing K] [IsLocalRing K]
    (u : Spec (CommRingCat.of K) ⟶ ∐ X) :
    ∃! z : Σ i, (Spec (CommRingCat.of K) ⟶ X i), z.2 ≫ Sigma.ι X z.1 = u := by
  classical
  obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk X).surjective (u (closedPoint K))
  have hx' : u (closedPoint K) ∈ (Sigma.ι X i).opensRange := by
    exact ⟨x, (by simpa using hx)⟩
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem u hx'
  have hrange : Set.range u ⊆ Set.range (Sigma.ι X i) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ u ⁻¹ᵁ (Sigma.ι X i).opensRange := by rw [htop]; trivial
    exact hy
  let v := IsOpenImmersion.lift (Sigma.ι X i) u hrange
  have hv : v ≫ Sigma.ι X i = u := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨i, v⟩, hv, ?_⟩
  rintro ⟨j, w⟩ hw
  have heq : Sigma.ι X j (w (closedPoint K)) = Sigma.ι X i (v (closedPoint K)) := by
    change (w ≫ Sigma.ι X j) (closedPoint K) = (v ≫ Sigma.ι X i) (closedPoint K)
    rw [hw, hv]
  have hij : j = i := congrArg Sigma.fst ((sigmaι_eq_iff X j i _ _).mp heq)
  subst j
  have hwv : w = v := (cancel_mono (Sigma.ι X i)).mp (hw.trans hv.symm)
  cases hwv
  rfl

end AlgebraicGeometry.Scheme
