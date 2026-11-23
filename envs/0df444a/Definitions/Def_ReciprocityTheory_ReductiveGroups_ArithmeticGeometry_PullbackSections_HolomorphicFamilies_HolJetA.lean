-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:42.838843+00:00
-- url     : https://prove2.me/theorems/ee4c3b2d-282f-46e5-8b47-7e57b091caf1
-- title:
--   Hol Jet A
-- statement:
--   Definitions and structural lemmas for Hol Jet A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {Y : Scheme.{0}}
section Lift
variable (y₀ : Y) (A : CommRingCat.{0})
def nbhdLift (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) :
    Y.presheaf.stalk y₀ ⟶ A :=
  Limits.colimit.desc ((OpenNhds.inclusion y₀).op ⋙ Y.presheaf)
    { pt := A
      ι := { app := fun U => ψ U.unop.1 U.unop.2
             naturality := fun U V i =>
               (hψ U.unop.1 V.unop.1 U.unop.2 V.unop.2 (leOfHom i.unop)).trans (Category.comp_id _).symm } }
variable {y₀ A}
def nbhdPt (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) : Spec A ⟶ Y :=
  Spec.map (nbhdLift y₀ A ψ hψ) ≫ Y.fromSpecStalk y₀
end Lift
section Jet
variable (K : Type) [Field K] (ι : Type) (m : ℕ)
open Formalism.L2.Pj MvPolynomial
theorem jet_nilpotent_of_orig {p : MvPolynomial ι K} (hp : p ∈ orig K ι) :
    IsNilpotent (Ideal.Quotient.mk (orig K ι ^ (m + 1)) p) := by
  refine ⟨m + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hp _
instance isLocalRing_jet : IsLocalRing (Jet K ι m) := by
  haveI : Nontrivial (Jet K ι m) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    intro htop
    have h1 : (1 : MvPolynomial ι K) ∈ orig K ι := by
      have := (Ideal.eq_top_iff_one _).mp htop
      exact Ideal.pow_le_self (Nat.succ_ne_zero m) this
    have h1' : (1 : MvPolynomial ι K) ∈ Ideal.span (X '' Set.univ) := by rw [Set.image_univ]; exact h1
    obtain ⟨i, _, hi⟩ := (MvPolynomial.mem_ideal_span_X_image.mp h1') 0 (by simp)
    simp at hi
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hn := jet_nilpotent_of_orig K ι m (sub_const_mem_orig (R := K) p)
  have hsplit : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
      algebraMap K (Jet K ι m) (constantCoeff p) +
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - C (constantCoeff p)) := by
    have e : algebraMap K (Jet K ι m) (constantCoeff p) =
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (C (constantCoeff p)) := by
      rw [← MvPolynomial.algebraMap_eq]; rfl
    rw [map_sub, e, add_sub_cancel]
  by_cases hc : constantCoeff p = 0
  · right
    have e : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - C (constantCoeff p)) := by
      rw [hc]; simp
    rw [e, sub_eq_add_neg]
    exact IsNilpotent.isUnit_add_left_of_commute hn.neg isUnit_one (Commute.all _ _)
  · left
    rw [hsplit]
    exact IsNilpotent.isUnit_add_left_of_commute hn
      ((isUnit_iff_ne_zero.mpr hc).map (algebraMap K (Jet K ι m))) (Commute.all _ _)
end Jet
end ReciprocityTheory.ChartRestriction.G.PullbackSections


