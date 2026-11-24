-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:25.122935+00:00
-- url     : https://prove2.me/theorems/d3a8d58a-c5bf-41d9-a4e4-19f05d507922
-- title:
--   Integrable Complex Continuous Bounded Support
-- statement:
--   Definitions and structural lemmas for Integrable Complex Continuous Bounded Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IntegrableComplexContinuousBoundedSupport.lean

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Theorems.Thm_Formalism_REAL_complex_parts_mem_lie_algebra_holds
import Theorems.Thm_Formalism_REAL_continuous_coeMatrix
import Theorems.Thm_Formalism_REAL_continuous_frobenius_on_group
import Theorems.Thm_Formalism_REAL_exp_indefinite_unitary_holds
import Theorems.Thm_Formalism_REAL_indefinite_unitary_mul_mem
import Theorems.Thm_Formalism_REAL_rdSmooth_of
import Theorems.Thm_Formalism_REAL_right_derivative_extends
import Theorems.Thm_Formalism_REAL_right_derivative_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section F4BA
variable {n : ℕ} {ε : Fin n → Bool}
lemma curve_mem_indefinite_unitary {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (t : ℝ) :
    inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) :=
  indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t)
lemma smooth_on_group_add {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) :
    SmoothOnG ε (fun x => f x + h x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', H, hU', hgU', hH, hhH⟩ := hh g₀ hg₀
  exact ⟨U ∩ U', fun x => F x + H x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right),
    fun g hg hgJ => by simp only; rw [hfF g hg.1 hgJ, hhH g hg.2 hgJ]⟩
lemma smooth_on_group_mul {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) :
    SmoothOnG ε (fun x => f x * h x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', H, hU', hgU', hH, hhH⟩ := hh g₀ hg₀
  exact ⟨U ∩ U', fun x => F x * H x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).mul (hH.mono Set.inter_subset_right),
    fun g hg hgJ => by simp only; rw [hfF g hg.1 hgJ, hhH g hg.2 hgJ]⟩
lemma smooth_on_group_const_fun (c : ℂ) : SmoothOnG ε (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  fun _ _ => ⟨Set.univ, fun _ => c, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
lemma smooth_on_group_const_mul (c : ℂ) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    SmoothOnG ε (fun x => c * f x) := smooth_on_group_mul (smooth_on_group_const_fun c) hf
lemma smooth_right_derivative_alt {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hX : inG ε X) : SmoothOnG ε (Rd X f) :=
  rdSmooth_of right_derivative_extends n ε f X hf hX
lemma smooth_complexified_derivative {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) : SmoothOnG ε (Ec ε Z f) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  exact smooth_on_group_add (smooth_right_derivative_alt hf h1) (smooth_on_group_const_mul Complex.I (smooth_right_derivative_alt hf h2))
lemma smooth_lie_derivative {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) (hf : SmoothOnG ε f) :
    SmoothOnG ε (Eab ε a b f) := smooth_complexified_derivative _ hf
lemma smooth_iterated_lie_derivative {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    ∀ w : List (Fin n × Fin n), SmoothOnG ε (Eword ε w f)
  | [] => hf
  | p :: w => smooth_lie_derivative p.1 p.2 (smooth_iterated_lie_derivative hf w)
lemma right_derivative_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} {g X : Matrix (Fin n) (Fin n) ℂ}
    (e : ∀ x, inUJ ε x → f x = h x) (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X h g := by
  unfold Rd
  congr 1
  funext t
  exact e _ (curve_mem_indefinite_unitary hg hX t)
lemma right_derivative_const_zero {g X : Matrix (Fin n) (Fin n) ℂ} :
    Rd X (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : ℂ)) g = 0 := by
  simp [Rd]
end F4BA
section F4BB
variable {n : ℕ} {ε : Fin n → Bool}
lemma real_part_single_mem (ε : Fin n → Bool) (a b : Fin n) : inG ε (cpart1 ε (Matrix.single a b 1)) :=
  (complex_parts_mem_lie_algebra_holds n ε _).1
lemma imaginary_part_single_mem (ε : Fin n → Bool) (a b : Fin n) : inG ε (cpart2 ε (Matrix.single a b 1)) :=
  (complex_parts_mem_lie_algebra_holds n ε _).2.1
lemma lie_derivative_def (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε a b f g = Rd (cpart1 ε (Matrix.single a b 1)) f g +
      Complex.I * Rd (cpart2 ε (Matrix.single a b 1)) f g := rfl
lemma lie_derivative_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (e : ∀ x, inUJ ε x → f x = h x) (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b h g := by
  rw [lie_derivative_def, lie_derivative_def, right_derivative_congr e (real_part_single_mem ε a b) hg, right_derivative_congr e (imaginary_part_single_mem ε a b) hg]
lemma lie_derivative_add_smul {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) (c : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) (hg : inUJ ε g) :
    Eab ε a b (fun x => f x + c * h x) g = Eab ε a b f g + c * Eab ε a b h g := by
  rw [lie_derivative_def, lie_derivative_def, lie_derivative_def,
    (right_derivative_linear n ε f h _ _ 0 c g hf hh (real_part_single_mem ε a b) (real_part_single_mem ε a b) hg).2.2,
    (right_derivative_linear n ε f h _ _ 0 c g hf hh (imaginary_part_single_mem ε a b) (imaginary_part_single_mem ε a b) hg).2.2]
  ring
lemma lie_derivative_const_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε a b (fun _ => (0 : ℂ)) g = 0 := by
  rw [lie_derivative_def, right_derivative_const_zero, right_derivative_const_zero]; ring
def lieDerivativeLogFrobeniusBound (ε : Fin n → Bool) (a b : Fin n) : ℝ :=
  2 * Real.sqrt (hs (cpart1 ε (Matrix.single a b (1 : ℂ)))) +
    2 * Real.sqrt (hs (cpart2 ε (Matrix.single a b (1 : ℂ))))
def VanishesOutsideBall (ε : Fin n → Bool) (R : ℝ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g, inUJ ε g → R < hs g → f g = 0
lemma continuous_smooth_on_group_eval {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    Continuous (fun g : UJ ε => f (toM g)) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (toM g) g.2
  have hFc : ContinuousAt F (toM g) := (hF.continuousOn).continuousAt (hU.mem_nhds hgU)
  have h1 : ContinuousAt (fun g : UJ ε => F (toM g)) g := hFc.comp (continuous_coeMatrix ε).continuousAt
  refine h1.congr ?_
  have hpre : ∀ᶠ g' : UJ ε in 𝓝 g, toM g' ∈ U :=
    (continuous_coeMatrix ε).continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  filter_upwards [hpre] with g' hg'
  exact (hfF _ hg' g'.2).symm
end F4BB
def cutoffProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)
lemma contDiff_cutoff_profile : ContDiff ℝ ∞ cutoffProfile :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)
lemma cutoff_profile_eq_one_near {t : ℝ} (h : t ≤ 1) : cutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma cutoff_profile_eq_zero {t : ℝ} (h : 2 ≤ t) : cutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma exists_cutoff_deriv_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv cutoffProfile t| ≤ B := by
  have hc : Continuous (deriv cutoffProfile) := contDiff_cutoff_profile.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases h1 : t < 1
  · have : deriv cutoffProfile t = 0 := by
      have hev : cutoffProfile =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds h1] with s hs
        exact cutoff_profile_eq_one_near (le_of_lt hs)
      rw [hev.deriv_eq]; simp
    rw [this]; simp
  by_cases h2 : 2 < t
  · have : deriv cutoffProfile t = 0 := by
      have hev : cutoffProfile =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h2] with s hs
        exact cutoff_profile_eq_zero (le_of_lt hs)
      rw [hev.deriv_eq]; simp
    rw [this]; simp
  have := hC t ⟨le_of_not_gt h1, le_of_not_gt h2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)
def cutoffDerivBound : ℝ := Classical.choose exists_cutoff_deriv_bound
def radialCutoff (R t : ℝ) : ℝ := cutoffProfile (t / R)
def weightProfileAlt (a R t : ℝ) : ℝ := radialCutoff R t ^ 2 * Real.exp (2 * a * t)
section F4BML
variable {n : ℕ} {ε : Fin n → Bool}
lemma smooth_on_group_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i ∈ s, SmoothOnG ε (f i)) : SmoothOnG ε (fun x => ∑ i ∈ s, f i x) := by
  first | exact _root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c .. | (apply _root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c <;> assumption) | (intros; apply _root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c <;> assumption) | (intros; apply @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c <;> first | assumption | infer_instance) | exact @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c n ε ι s f h | exact @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c n ε ι s f | exact @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c n ε ι s | exact @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c n ε ι | exact @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c n ε | exact @_root_.P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c n
def signedCasimirDifference (ε : Fin n → Bool) (u : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun x => ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) * Eab ε j i (Eab ε i j u) x
lemma smooth_signedCasimir {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) : SmoothOnG ε (signedCasimirDifference ε u) :=
  smooth_on_group_sum _ _ fun i _ => smooth_on_group_sum _ _ fun j _ =>
    smooth_on_group_const_mul _ (smooth_lie_derivative j i (smooth_lie_derivative i j hu))
def radialWeight (a R : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ := ((weightProfileAlt a R (hh x) : ℝ) : ℂ)
lemma measurable_exponential_weight (a : ℝ) : Measurable (fun g : UJ ε => Real.exp (2 * a * hh (toM g))) :=
  Real.measurable_exp.comp (measurable_const.mul
    (Real.measurable_log.comp (continuous_frobenius_on_group ε).measurable))
lemma aestronglyMeasurable_weighted_norm_sq (a : ℝ) {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) :
    AEStronglyMeasurable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2)
      (muG ε) :=
  ((measurable_exponential_weight a).mul ((continuous_smooth_on_group_eval hu).norm.pow 2).measurable).aestronglyMeasurable
end F4BML
section F4BML2
variable {n : ℕ} {ε : Fin n → Bool}
end F4BML2
section Integrability
variable {n : ℕ} {ε : Fin n → Bool}
end Integrability
section F4BUL
variable {n : ℕ} {ε : Fin n → Bool}
def radialCutoffFunction (R : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ := ((radialCutoff R (hh x) : ℝ) : ℂ)
end F4BUL
section F4BAlg
variable {n : ℕ} (ε : Fin n → Bool)
def smoothFunctionsOnGroup : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {f | SmoothOnG ε f}
  add_mem' := fun hf hh => smooth_on_group_add hf hh
  zero_mem' := smooth_on_group_const_fun 0
  smul_mem' := fun c _ hf => smooth_on_group_const_mul c hf
def vanishingOnGroup : Submodule ℂ (smoothFunctionsOnGroup ε) where
  carrier := {f | ∀ g, inUJ ε g → (f : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0}
  add_mem' := by
    intro f h hf hh g hg
    show (f : Matrix (Fin n) (Fin n) ℂ → ℂ) g + (h : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0
    rw [hf g hg, hh g hg, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf g hg
    show c * (f : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0
    rw [hf g hg, mul_zero]
abbrev SmoothFunctionsModGroup := (smoothFunctionsOnGroup ε) ⧸ (vanishingOnGroup ε)
variable {ε}
lemma smoothFunctions_smooth (u : smoothFunctionsOnGroup ε) : SmoothOnG ε (u : Matrix (Fin n) (Fin n) ℂ → ℂ) := u.2
def quotientMkAlt (u : smoothFunctionsOnGroup ε) : SmoothFunctionsModGroup ε := Submodule.Quotient.mk u
lemma quotient_mk_eq_iff {u v : smoothFunctionsOnGroup ε} :
    quotientMkAlt u = quotientMkAlt v ↔ ∀ g, inUJ ε g → (u : Matrix (Fin n) (Fin n) ℂ → ℂ) g = (v : Matrix (Fin n) (Fin n) ℂ → ℂ) g := by
  unfold quotientMkAlt
  rw [Submodule.Quotient.eq]
  constructor
  · intro h g hg
    have := h g hg
    exact sub_eq_zero.1 this
  · intro h g hg
    show (u : Matrix (Fin n) (Fin n) ℂ → ℂ) g - (v : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0
    rw [h g hg, sub_self]
lemma quotient_mk_add (u v : smoothFunctionsOnGroup ε) : quotientMkAlt (u + v) = quotientMkAlt u + quotientMkAlt v := rfl
lemma quotient_mk_smul (c : ℂ) (u : smoothFunctionsOnGroup ε) : quotientMkAlt (c • u) = c • quotientMkAlt u := rfl
lemma quotient_mk_zero : quotientMkAlt (0 : smoothFunctionsOnGroup ε) = 0 := rfl
lemma quotient_mk_surjective (m : SmoothFunctionsModGroup ε) : ∃ u : smoothFunctionsOnGroup ε, m = quotientMkAlt u := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨u, rfl⟩
variable (ε)
def lieOperatorSmooth (i j : Fin n) : smoothFunctionsOnGroup ε →ₗ[ℂ] SmoothFunctionsModGroup ε where
  toFun u := quotientMkAlt ⟨Eab ε i j u, smooth_lie_derivative i j u.2⟩
  map_add' u v := by
    rw [← quotient_mk_add, quotient_mk_eq_iff]
    intro g hg
    show Eab ε i j (fun x => (u : Matrix (Fin n) (Fin n) ℂ → ℂ) x + (v : Matrix (Fin n) (Fin n) ℂ → ℂ) x) g =
      Eab ε i j u g + Eab ε i j v g
    have := lie_derivative_add_smul i j 1 u.2 v.2 hg
    simp only [one_mul] at this
    exact this
  map_smul' c u := by
    rw [RingHom.id_apply, ← quotient_mk_smul, quotient_mk_eq_iff]
    intro g hg
    show Eab ε i j (fun x => c * (u : Matrix (Fin n) (Fin n) ℂ → ℂ) x) g = c * Eab ε i j u g
    have := lie_derivative_add_smul i j c (smooth_on_group_const_fun (ε := ε) 0) u.2 hg
    simp only [zero_add, lie_derivative_const_zero] at this
    exact this
def lieOperatorQuotient (i j : Fin n) : Module.End ℂ (SmoothFunctionsModGroup ε) :=
  (vanishingOnGroup ε).liftQ (lieOperatorSmooth ε i j) (by
    intro u hu
    rw [LinearMap.mem_ker]
    show quotientMkAlt _ = 0
    rw [← quotient_mk_zero, quotient_mk_eq_iff]
    intro g hg
    show Eab ε i j u g = 0
    rw [lie_derivative_congr (h := fun _ => (0 : ℂ)) i j (fun x hx => hu x hx) hg, lie_derivative_const_zero])
variable {ε}
end F4BAlg
section F4BAlg2
variable {n : ℕ} {ε : Fin n → Bool}
lemma smooth_casimir {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) : SmoothOnG ε (CasF ε u) :=
  smooth_on_group_sum _ _ fun a _ => smooth_on_group_sum _ _ fun b _ => smooth_lie_derivative a b (smooth_lie_derivative b a hu)
def signedCasimirQuotient (ε : Fin n → Bool) : Module.End ℂ (SmoothFunctionsModGroup ε) :=
  ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) • (lieOperatorQuotient ε j i * lieOperatorQuotient ε i j)
def wordActionQuotient (ε : Fin n → Bool) : List (Fin n × Fin n) → SmoothFunctionsModGroup ε → SmoothFunctionsModGroup ε
  | [] => fun m => m
  | p :: w => fun m => lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)
variable (ε)
def weightVectorsQuotient (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Set (SmoothFunctionsModGroup ε) :=
  {m | ∃ f ∈ W, ∃ hf : SmoothOnG ε f, m = quotientMkAlt ⟨f, hf⟩}
def wordFiltration (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (k : ℕ) : Submodule ℂ (SmoothFunctionsModGroup ε) :=
  Submodule.span ℂ {x | ∃ w : List (Fin n × Fin n), ∃ m ∈ weightVectorsQuotient ε W, w.length ≤ k ∧ x = wordActionQuotient ε w m}
variable {ε}
variable {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}
end F4BAlg2
section F4BMain
variable {n : ℕ} {ε : Fin n → Bool}
variable (ε) in
def evalSmoothFunctions : smoothFunctionsOnGroup ε →ₗ[ℂ] (UJ ε → ℂ) where
  toFun u := fun g => (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (ε) in
def evalQuotient : SmoothFunctionsModGroup ε →ₗ[ℂ] (UJ ε → ℂ) :=
  (vanishingOnGroup ε).liftQ (evalSmoothFunctions ε) (by
    intro u hu
    rw [LinearMap.mem_ker]
    funext g
    exact hu _ g.2)
lemma evalQuotient_mk (u : smoothFunctionsOnGroup ε) :
    evalQuotient ε (quotientMkAlt u) = fun g => (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) := rfl
variable (ε) in
def weightedSquareIntegrable (a : ℝ) : Submodule ℂ (SmoothFunctionsModGroup ε) where
  carrier := {m | Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖evalQuotient ε m g‖ ^ 2)
    (muG ε)}
  zero_mem' := by
    show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖evalQuotient ε 0 g‖ ^ 2) (muG ε)
    simp only [map_zero, Pi.zero_apply, norm_zero]
    simpa using (integrable_zero (UJ ε) ℝ (muG ε))
  add_mem' := by
    intro x y hx hy
    obtain ⟨u, rfl⟩ := quotient_mk_surjective x
    obtain ⟨v, rfl⟩ := quotient_mk_surjective y
    show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
      ‖evalQuotient ε (quotientMkAlt u + quotientMkAlt v) g‖ ^ 2) (muG ε)
    have hx' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
        ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) (muG ε) := hx
    have hy' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
        ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) (muG ε) := hy
    rw [← quotient_mk_add, evalQuotient_mk]
    have hb : Integrable (fun g : UJ ε => 2 * (Real.exp (2 * a * hh (toM g)) *
        ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) + 2 * (Real.exp (2 * a * hh (toM g)) *
        ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2)) (muG ε) :=
      Integrable.add (f := fun g : UJ ε => 2 * (Real.exp (2 * a * hh (toM g)) *
          ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2))
        (g := fun g : UJ ε => 2 * (Real.exp (2 * a * hh (toM g)) *
          ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2))
        (Integrable.const_mul (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) hx' 2)
        (Integrable.const_mul (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) hy' 2)
    refine hb.mono' (aestronglyMeasurable_weighted_norm_sq a (smoothFunctions_smooth (u + v))) (Eventually.of_forall fun g => ?_)
    have he := Real.exp_pos (2 * a * hh (toM g))
    have e1 : ((u + v : smoothFunctionsOnGroup ε) : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) =
        (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) + (v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) := rfl
    beta_reduce
    rw [e1, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := norm_add_le ((u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g))
      ((v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g))
    have h2 : ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) + (v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2
        ≤ 2 * ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2 +
          2 * ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2 := by
      have := norm_nonneg ((u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) +
        (v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g))
      nlinarith [sq_nonneg (‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ -
        ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖)]
    nlinarith
  smul_mem' := by
    intro c x hx
    obtain ⟨u, rfl⟩ := quotient_mk_surjective x
    show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
      ‖evalQuotient ε (c • quotientMkAlt u) g‖ ^ 2) (muG ε)
    have hx' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
        ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) (muG ε) := hx
    rw [← quotient_mk_smul, evalQuotient_mk]
    refine (hx'.const_mul (‖c‖ ^ 2)).congr (Eventually.of_forall fun g => ?_)
    show ‖c‖ ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) =
      Real.exp (2 * a * hh (toM g)) * ‖c * (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2
    rw [norm_mul]; ring
end F4BMain
end Formalism.REAL


