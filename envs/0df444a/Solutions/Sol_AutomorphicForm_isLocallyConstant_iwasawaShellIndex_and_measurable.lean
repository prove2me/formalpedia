-- Prove2me | solution 1 for AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e16b6e82-b681-570c-8e8c-752258d89b3f

import Definitions.Def_AutomorphicForm_IwasawaShellIndex
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (iwasawaShellIndex K v) ∧ Measurable (iwasawaShellIndex K v) := by

  have hent : ∀ i j : Fin 2, Continuous fun g : AdelicGL2 (𝓞 K) K => localMatrix v g i j := by
    intro i j
    have h1 : Continuous fun g : AdelicGL2 (𝓞 K) K => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) :=
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j
    exact ((continuous_finAdeleEval (𝓞 K) K v).comp (continuous_adeleFin (𝓞 K) K)).comp h1
  have hdet : Continuous fun g : AdelicGL2 (𝓞 K) K => (localMatrix v g).det := by
    simp_rw [Matrix.det_fin_two]
    exact ((hent 0 0).mul (hent 1 1)).sub ((hent 0 1).mul (hent 1 0))

  have key : ∀ {f : AdelicGL2 (𝓞 K) K → v.adicCompletion K}, Continuous f → ∀ g, f g ≠ 0 →
      ∀ᶠ g' in 𝓝 g, Valued.v (f g') = Valued.v (f g) := by
    intro f hf g hg
    exact hf.continuousAt.preimage_mem_nhds (Valued.locally_const ((Valuation.ne_zero_iff _).mpr hg))

  have small : ∀ {f : AdelicGL2 (𝓞 K) K → v.adicCompletion K}, Continuous f → ∀ g, f g = 0 →
      ∀ (y₀ : v.adicCompletion K), y₀ ≠ 0 → ∀ᶠ g' in 𝓝 g, Valued.v (f g') < Valued.v y₀ := by
    intro f hf g hg y₀ hy₀
    have hr : (Valued.v.restrict y₀ : MonoidWithZeroHom.ValueGroup₀
        (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))))) ≠ 0 := by
      rw [ne_eq, Valuation.restrict_eq_zero_iff _, Valuation.zero_iff]; exact hy₀
    have hmem : {y : v.adicCompletion K | Valued.v y < Valued.v y₀} ∈ 𝓝 (f g) := by
      rw [hg, Valued.mem_nhds_zero]
      exact ⟨Units.mk0 _ hr, fun y hy => (Valuation.restrict_lt_iff _).mp hy⟩
    exact hf.continuousAt.preimage_mem_nhds hmem
  have hlc : IsLocallyConstant (iwasawaShellIndex K v) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have hD := key hdet g (det_localMatrix_ne_zero v g)

    have hM : ∀ᶠ g' in 𝓝 g, max (Valued.v (localMatrix v g' 1 0)) (Valued.v (localMatrix v g' 1 1)) =
        max (Valued.v (localMatrix v g 1 0)) (Valued.v (localMatrix v g 1 1)) := by
      have hne : max (Valued.v (localMatrix v g 1 0)) (Valued.v (localMatrix v g 1 1)) ≠ 0 :=
        max_finEntryValuation_ne_zero v g
      by_cases h0 : localMatrix v g 1 0 = 0
      · have h1 : localMatrix v g 1 1 ≠ 0 := by
          intro h1; apply hne; simp [h0, h1]
        have hv1 : Valued.v (localMatrix v g 1 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr h1
        filter_upwards [key (hent 1 1) g h1, small (hent 1 0) g h0 _ h1] with g' ha hb
        rw [ha, h0, Valuation.map_zero, max_eq_right hb.le, max_eq_right zero_le']
      · by_cases h1 : localMatrix v g 1 1 = 0
        · have hv0 : Valued.v (localMatrix v g 1 0) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
          filter_upwards [key (hent 1 0) g h0, small (hent 1 1) g h1 _ h0] with g' ha hb
          rw [ha, h1, Valuation.map_zero, max_eq_left hb.le, max_eq_left zero_le']
        · filter_upwards [key (hent 1 0) g h0, key (hent 1 1) g h1] with g' ha hb
          rw [ha, hb]
    filter_upwards [hD, hM] with g' hD' hM'
    rw [iwasawaShellIndex_eq, iwasawaShellIndex_eq, hD', hM']
  exact ⟨hlc, hlc.continuous.measurable⟩

end S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable
end P2MW
export P2MW.S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable (solution)
