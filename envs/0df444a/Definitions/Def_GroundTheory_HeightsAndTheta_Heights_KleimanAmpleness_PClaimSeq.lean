-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:26:48.609206+00:00
-- url     : https://prove2.me/theorems/8a94a526-7291-4224-b77e-c4fec85eae5b
-- title:
--   PClaim Seq
-- statement:
--   Definitions and structural lemmas for PClaim Seq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
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
section Forms
variable {R : Type u} [CommRing R] {N : ℕ}
theorem homogeneousComponent_mul_form (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _
theorem mem_span_forms_of_mem_ideal {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by
  obtain ⟨c, t, htG, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  rw [← homogeneousComponent_eq_self he, map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hc := homogeneousComponent_mul_form (c g) g (hG g (htG hg)) e
  rw [smul_eq_mul]
  refine Submodule.span_le.mpr ?_ hc
  rintro _ ⟨h, d', hh, hd, rfl⟩
  exact Submodule.subset_span ⟨g, htG hg, h, d', hh, hd, rfl⟩
theorem isHomogeneous_totalDegree {g : Poly R N} {d : ℕ} (hg : g.IsHomogeneous d) :
    g.IsHomogeneous g.totalDegree := by
  by_cases h0 : g = 0
  · rw [h0]; exact isHomogeneous_zero _ _ _
  · rwa [hg.totalDegree h0]
end Forms
section Chart
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x)
def StepData.Jg : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z | ∃ (f : Poly k N)
      (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, T.J.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; rw [smul_comm]; exact Submodule.smul_mem _ a hz
  fg := by
    classical
    set G : Set (Poly k N) := {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o} with hGdef
    have hJ : T.J = Ideal.span G := rfl
    have hfg : (Submodule.span (Poly k N) G).FG := IsNoetherian.noetherian _
    obtain ⟨G₀, hG₀, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
    have hG : ∀ g ∈ (G₀ : Set (Poly k N)), g.IsHomogeneous g.totalDegree :=
      fun g hg => by obtain ⟨c, hc, _⟩ := hG₀ hg; exact isHomogeneous_totalDegree hc
    let gj : Fin G₀.card → Poly k N := fun j => (G₀.equivFin.symm j : Poly k N)
    refine ⟨G₀.card, fun j => ((gj j).totalDegree : ℤ), fun j => aeval x (gj j), fun j => ?_, fun c => ?_⟩
    · refine Submodule.subset_span ⟨gj j, _, ?_, hG _ (G₀.equivFin.symm j).2, rfl, rfl⟩
      rw [hJ]; exact Ideal.subset_span (hG₀ (G₀.equivFin.symm j).2)
    · rw [Submodule.span_le]
      rintro _ ⟨f, e, hf, he, rfl, rfl⟩
      rw [hJ, Ideal.span, hspan] at hf
      have hm := mem_span_forms_of_mem_ideal _ hG hf he
      refine Submodule.span_induction (p := fun f _ => aeval x f ∈ _) ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨g, hg, h, d', hh, hd, rfl⟩
        refine Submodule.subset_span ⟨G₀.equivFin ⟨g, hg⟩, h, d', hh, ?_, ?_⟩
        · simp only [gj, Equiv.symm_apply_apply]; omega
        · simp only [gj, Equiv.symm_apply_apply, map_mul, smul_eq_mul]
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz; rw [map_smul]; exact Submodule.smul_mem _ a hz
end Chart
end
end GroundTheory.Heights₂.Heights.Kleiman


