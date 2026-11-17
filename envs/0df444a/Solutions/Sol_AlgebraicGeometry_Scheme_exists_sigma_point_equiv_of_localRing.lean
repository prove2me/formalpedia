-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_sigma_point_equiv_of_localRing
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:11.614889+00:00
-- url     : https://prove2.me/submissions/333e8442-683c-44d8-a9ce-b87de59d622a

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_sigma_factor_of_localRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing NeronModelInfra

namespace AlgebraicGeometry.Scheme

/-- Over a local test ring, points of the coproduct are precisely the disjoint
union of the points of its components, preserving their structure maps. -/
theorem _root_.solution
    {ι : Type} {S : Scheme.{0}} (X : ι → Scheme.{0}) (f : ∀ i, X i ⟶ S)
    {K : Type} [CommRing K] [IsLocalRing K]
    (t : Spec (CommRingCat.of K) ⟶ S) :
    ∃ e : (Σ i, SchemeHomOver t (f i)) ≃ SchemeHomOver t (Sigma.desc f),
      ∀ x, (e x).1 = x.2.1 ≫ Sigma.ι X x.1 := by
  classical
  let F : (Σ i, SchemeHomOver t (f i)) → SchemeHomOver t (Sigma.desc f) :=
    fun x => ⟨x.2.1 ≫ Sigma.ι X x.1, by simpa using x.2.2⟩
  have hinj : Function.Injective F := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hh : x.1 ≫ Sigma.ι X i = y.1 ≫ Sigma.ι X j := congrArg Subtype.val h
    have hp : Sigma.ι X i (x.1 (closedPoint K)) =
        Sigma.ι X j (y.1 (closedPoint K)) := by
      exact
        congrArg (fun v => v (closedPoint K)) hh
    have hij := congrArg Sigma.fst ((sigmaι_eq_iff X i j _ _).mp hp)
    dsimp at hij
    subst j
    have hxy : x = y := Subtype.ext ((cancel_mono (Sigma.ι X i)).mp hh)
    cases hxy
    rfl
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨⟨i, x⟩, hx, _⟩ := existsUnique_sigma_factor_of_localRing X y.1
    have ho : x ≫ f i = t := by
      rw [← Sigma.ι_desc f i, ← Category.assoc, hx]
      exact y.2
    exact ⟨⟨i, ⟨x, ho⟩⟩, Subtype.ext hx⟩
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun _ => rfl⟩

end AlgebraicGeometry.Scheme
