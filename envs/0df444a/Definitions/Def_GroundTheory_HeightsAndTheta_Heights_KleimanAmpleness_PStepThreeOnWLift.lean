-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:31:59.154793+00:00
-- url     : https://prove2.me/theorems/a086dcc7-31ec-558d-b960-ed608e8cf57d
-- title:
--   PStep Three On WLift
-- statement:
--   Definitions and structural lemmas for PStep Three On WLift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace StepThreeOnWLift
section Forms
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
theorem homogeneousComponent_mul_of_isHomogeneous {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}
    {l : ℕ} (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
theorem exists_finset_forms (P : Ideal (Poly k N)) :
    ∃ T : Finset (Poly k N), (∀ h ∈ T, h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e) ∧
      ∀ f ∈ P, ∀ e : ℕ, f.IsHomogeneous e → f ∈ Ideal.span (T : Set (Poly k N)) := by
  classical
  obtain ⟨G0, hG0⟩ := IsNoetherian.noetherian (Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e})
  have hmem : ∀ g ∈ G0, ∃ T : Finset (Poly k N),
      (T : Set (Poly k N)) ⊆ {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} ∧
        g ∈ Ideal.span (T : Set (Poly k N)) := by
    intro g hg
    have hg' : g ∈ Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} :=
      hG0 ▸ Submodule.subset_span hg
    exact Submodule.mem_span_finite_of_mem_span hg'
  choose! Tf hTf hgT using hmem
  refine ⟨G0.biUnion Tf, fun h hh => ?_, fun f hf e he => ?_⟩
  · obtain ⟨g, hg, hhg⟩ := Finset.mem_biUnion.mp hh
    exact hTf g hg hhg
  · have h1 : f ∈ Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} :=
      Ideal.subset_span ⟨hf, e, he⟩
    rw [← hG0] at h1
    refine (Submodule.span_le.mpr ?_) h1
    intro g hg
    refine Ideal.span_mono ?_ (hgT g hg)
    intro z hz
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, hg, hz⟩)
variable (x) in

def idealGraded (P : Ideal (Poly k N)) : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ P ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z |
      ∃ (f : Poly k N) (e : ℕ), f ∈ P ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f})
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, P.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    classical
    obtain ⟨T, hT, hspan⟩ := exists_finset_forms P
    choose! dg hdg using fun h (hh : h ∈ T) => (hT h hh).2
    refine ⟨T.card, fun j => (dg (T.equivFin.symm j).1 : ℤ), fun j => aeval x (T.equivFin.symm j).1,
      fun j => Submodule.subset_span ⟨_, _, (hT _ (T.equivFin.symm j).2).1,
        hdg _ (T.equivFin.symm j).2, rfl, rfl⟩, fun c => ?_⟩
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, e, hfP, hf, rfl, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp (hspan f hfP e hf)
    have h0 : homogeneousComponent e f = f := by rw [homogeneousComponent_of_mem hf, if_pos rfl]
    have hfe : f = ∑ h : T, homogeneousComponent e (h.1 * a h) := by
      calc f = homogeneousComponent e f := h0.symm
        _ = homogeneousComponent e (∑ h : T, a h • h.1) := by rw [ha]
        _ = ∑ h : T, homogeneousComponent e (h.1 * a h) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun h _ => by rw [smul_eq_mul, mul_comm]
    rw [SetLike.mem_coe, hfe, map_sum]
    refine Submodule.sum_mem _ fun h _ => ?_
    rw [homogeneousComponent_mul_of_isHomogeneous (hdg h.1 h.2)]
    split_ifs with hle
    · refine Submodule.subset_span ⟨T.equivFin h, homogeneousComponent (e - dg h.1) (a h), e - dg h.1,
        homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
        push_cast [hle]
        ring
      · simp only [Equiv.symm_apply_apply, map_mul, smul_eq_mul]
        ring
    · rw [map_zero]; exact Submodule.zero_mem _
end Forms
section Lift
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
end Lift
end StepThreeOnWLift
end
end GroundTheory.Heights₂.Heights.Kleiman


