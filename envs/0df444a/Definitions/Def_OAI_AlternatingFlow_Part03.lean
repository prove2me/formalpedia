-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part03
-- name    : OAI_AlternatingFlow_Part03
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:30:26.745455+00:00
-- url     : https://prove2.me/theorems/8b41b4b7-126c-43e2-bac7-ca425ba1322a
-- title:
--   Alternating-flow construction, part 3 of 11 (port of OpenAI's formalization): spatial curls, time gluing, the construction and its analytic properties
-- statement:
--   Part 3 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains spatial curls, time gluing, the construction and its analytic properties.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `SpatialCurls`, `TimeGlue`, `Construction`, `Analytic` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/SpatialCurls.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/TimeGlue.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Construction.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Analytic.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 3 of 11: spatial curls, time gluing, the construction and its analytic properties.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: SpatialCurls.lean, TimeGlue.lean, Construction.lean, Analytic.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`; one side-goal tactic in SpatialCurls adjusted for Mathlib 0df444a.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part02

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/SpatialCurls.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Spatial

noncomputable def d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) (x : Space) : E := fderiv ℝ F x (e i)

lemma coord_smooth (i : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x i) :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff

lemma coord_hasFDeriv (i : Fin 3) (x : Space) :
    HasFDerivAt (fun x : Space => x i) (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i) x :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt

lemma e_apply (i j : Fin 3) : e i j = if j = i then 1 else 0 := by
  simp [e, EuclideanSpace.single, PiLp.single_apply]

lemma d_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (d i F) := by
  exact (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).clm_apply contDiff_const

lemma d_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) : tsupport (d i F) ⊆ tsupport F :=
  tsupport_fderiv_apply_subset ℝ (e i)

lemma d_comm (i j : Fin 3) (F : Space → ℝ) (hF : ContDiff ℝ ∞ F) :
    d i (d j F) = d j (d i F) := by
  ext x
  have hd := (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).differentiable (by simp)
  have heq (a b : Fin 3) : d a (d b F) x = fderiv ℝ (fderiv ℝ F) x (e a) (e b) := by
    unfold d
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [heq, heq]
  exact hF.contDiffAt.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) _ _

noncomputable def curl (i j : Fin 3) (φ : Space → ℝ) (x : Space) : Space :=
  d j φ x • e i - d i φ x • e j

lemma curl_smooth (i j : Fin 3) (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (curl i j φ) :=
  ((d_smooth j φ hφ).smul contDiff_const).sub ((d_smooth i φ hφ).smul contDiff_const)

lemma curl_tsupport (i j : Fin 3) (φ : Space → ℝ) : tsupport (curl i j φ) ⊆ tsupport φ := by
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact (tsupport_smul_subset_left _ _).trans (d_tsupport j φ)
  · exact (tsupport_smul_subset_left _ _).trans (d_tsupport i φ)

lemma curl_div (i j : Fin 3) (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    (∑ k : Fin 3, d k (curl i j φ) x k) = 0 := by
  have hd (k : Fin 3) := (d_smooth k φ hφ).differentiable (by simp)
  have hc (k : Fin 3) : d k (curl i j φ) x k =
      d k (d j φ) x * (if k = i then 1 else 0) -
        d k (d i φ) x * (if k = j then 1 else 0) := by
    change (fderiv ℝ ((fun y => d j φ y • e i) - (fun y => d i φ y • e j)) x (e k)) k = _
    rw [fderiv_sub ((hd j x).smul_const _) ((hd i x).smul_const _),
      fderiv_smul_const (hd j x), fderiv_smul_const (hd i x)]
    simp [e_apply, d]
  simp_rw [hc]
  rw [Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [d_comm i j φ hφ, sub_self]

def box : Set Space := {x | ∀ i : Fin 3, |x i| ≤ 3}

def plateau : Set Space := {x | ∀ i : Fin 3, |x i| < 2}

noncomputable def cutoff (x : Space) : ℝ :=
  letI := threeAtLeastTwo
  ∏ i : Fin 3, Real.smoothTransition (3 - x i) * Real.smoothTransition (3 + x i)

lemma cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  apply contDiff_prod
  intro i _
  have hi := coord_smooth i
  fun_prop

lemma isClosed_box : IsClosed box := by
  have heq : box = ⋂ i : Fin 3, {x : Space | |x i| ≤ 3} := by ext; simp [box]
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le (coord_smooth i).continuous.abs continuous_const)

lemma box_compact : IsCompact box := by
  apply (isCompact_closedBall (0 : Space) 9).of_isClosed_subset isClosed_box
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  calc
    ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ ∑ _i : Fin 3, (3 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
    _ ≤ 9 ^ 2 := by norm_num

lemma plateau_open : IsOpen plateau := by
  have heq : plateau = ⋂ i : Fin 3, {x : Space | |x i| < 2} := by ext; simp [plateau]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (coord_smooth i).continuous.abs continuous_const)

lemma cutoff_one (x : Space) (hx : x ∈ plateau) : cutoff x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  have hi := abs_lt.1 (hx i)
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 - x i),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 + x i), one_mul]

lemma cutoff_one_near (x : Space) (hx : x ∈ plateau) :
    cutoff =ᶠ[𝓝 x] (fun _ => 1) :=
  Filter.eventually_of_mem (plateau_open.mem_nhds hx) (fun y hy => cutoff_one y hy)

lemma cutoff_support : tsupport cutoff ⊆ box := by
  apply closure_minimal _ isClosed_box
  intro x hx i
  by_contra hi
  have hn : 3 < |x i| := lt_of_not_ge hi
  have hz : Real.smoothTransition (3 - x i) * Real.smoothTransition (3 + x i) = 0 := by
    rcases (lt_abs.1 hn) with hn | hn
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - x i ≤ 0), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 + x i ≤ 0), mul_zero]
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

noncomputable def shearPotential (d i j : Fin 3) (L E : ℝ → ℝ) (x : Space) : ℝ :=
  x j * L (x d) - x i * E (x d)

noncomputable def localizedShear (d i j : Fin 3) (L E : ℝ → ℝ) : Space → Space :=
  curl i j (fun x => cutoff x * shearPotential d i j L E x)

lemma shearPotential_smooth (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (shearPotential d i j L E) :=
  ((coord_smooth j).mul (hL.comp (coord_smooth d))).sub
    ((coord_smooth i).mul (hE.comp (coord_smooth d)))

lemma localizedShear_smooth (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (localizedShear d i j L E) :=
  curl_smooth i j _ (cutoff_smooth.mul (shearPotential_smooth d i j L E hL hE))

lemma localizedShear_support (d i j : Fin 3) (L E : ℝ → ℝ) :
    tsupport (localizedShear d i j L E) ⊆ box :=
  (curl_tsupport _ _ _).trans (tsupport_mul_subset_left.trans cutoff_support)

lemma localizedShear_div (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) (x : Space) :
    (∑ k : Fin 3, Spatial.d k (localizedShear d i j L E) x k) = 0 :=
  curl_div i j _ (cutoff_smooth.mul (shearPotential_smooth d i j L E hL hE)) x

lemma localizedShear_plateau (d i j : Fin 3) (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (L E : ℝ → ℝ) (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E)
    (x : Space) (hx : x ∈ plateau) :
    localizedShear d i j L E x = L (x d) • e i + E (x d) • e j := by
  have heq : (fun y => cutoff y * shearPotential d i j L E y) =ᶠ[𝓝 x]
      shearPotential d i j L E := by
    filter_upwards [cutoff_one_near x hx] with y hy
    rw [hy, one_mul]
  have hL' := ((hL.differentiable (by simp)) (x d)).hasFDerivAt.comp x (coord_hasFDeriv d x)
  have hE' := ((hE.differentiable (by simp)) (x d)).hasFDerivAt.comp x (coord_hasFDeriv d x)
  have hφ := ((coord_hasFDeriv j x).mul hL').sub ((coord_hasFDeriv i x).mul hE')
  have hφeq := hφ.fderiv
  change fderiv ℝ (shearPotential d i j L E) x = _ at hφeq
  simp only [localizedShear, curl, Spatial.d, heq.fderiv_eq, hφeq]
  simp [ContinuousLinearMap.comp_apply, PiLp.proj_apply, e_apply, hij, hij.symm, hdi,
    hdj, sub_eq_add_neg]

end Spatial
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/TimeGlue.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def pulse (t : ℝ) : ℝ := deriv clock t

lemma pulse_smooth : ContDiff ℝ ∞ pulse := by
  exact ContDiff.deriv' (by simpa using clock_smooth)

lemma clock_hasDeriv (t : ℝ) : HasDerivAt clock (pulse t) t :=
  (clock_smooth.differentiable (by simp) t).hasDerivAt

lemma pulse_zero_left (t : ℝ) (ht : t ≤ 0) : pulse t = 0 := by
  have heq : clock =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds (by linarith : t < (1 : ℝ) / 4)] with u hu
    exact clock_zero u hu.le
  simpa [pulse] using heq.deriv_eq

lemma pulse_zero_right (t : ℝ) (ht : 1 ≤ t) : pulse t = 0 := by
  have heq : clock =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds (by linarith : (3 : ℝ) / 4 < t)] with u hu
    exact clock_one u hu.le
  simpa [pulse] using heq.deriv_eq

end Profiles

namespace TimeGlue

noncomputable def glue {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (W : ℕ → A → E) (t : ℝ) (x : A) : E :=
  ∑' k : ℕ, g (t - k) • W k x

lemma eq_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (W : ℕ → A → E)
    (t : ℝ) (x : A) (a : ℕ) (ht : t ≤ a) :
    glue g W t x = ∑ k ∈ Finset.range a, g (t - k) • W k x := by
  apply tsum_eq_sum
  intro k hk
  have hk' : a ≤ k := by simpa using hk
  have hka : (a : ℝ) ≤ k := by exact_mod_cast hk'
  rw [hg _ (by linarith), zero_smul]

lemma locally_eq_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace A] (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (W : ℕ → A → E)
    (z : ℝ × A) : ∃ a : ℕ,
      Function.uncurry (glue g W) =ᶠ[𝓝 z]
        (fun z : ℝ × A => ∑ k ∈ Finset.range a, g (z.1 - k) • W k z.2) := by
  obtain ⟨a, ha⟩ := exists_nat_gt z.1
  refine ⟨a, ?_⟩
  have hn : ∀ᶠ z' : ℝ × A in 𝓝 z, z'.1 < (a : ℝ) :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds ha
  filter_upwards [hn] with z' hz'
  exact eq_sum g hg W z'.1 z'.2 a hz'.le

lemma smooth {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (hs : ContDiff ℝ ∞ g)
    (W : ℕ → A → E) (hW : ∀ k, ContDiff ℝ ∞ (W k)) :
    ContDiff ℝ ∞ (Function.uncurry (glue g W)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨a, ha⟩ := locally_eq_sum g hg W z
  have hf : ContDiff ℝ ∞
      (fun z : ℝ × A => ∑ k ∈ Finset.range a, g (z.1 - k) • W k z.2) := by
    apply ContDiff.sum
    intro k _
    exact (hs.comp (contDiff_fst.sub contDiff_const)).smul ((hW k).comp contDiff_snd)
  exact hf.contDiffAt.congr_of_eventuallyEq ha

lemma hasDerivAt {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g g' : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (hg' : ∀ t, t ≤ 0 → g' t = 0)
    (hd : ∀ t, HasDerivAt g (g' t) t) (W : ℕ → A → E) (t : ℝ) (x : A) :
    HasDerivAt (fun u => glue g W u x) (glue g' W t x) t := by
  obtain ⟨a, ha⟩ := exists_nat_gt t
  rw [eq_sum g' hg' W t x a ha.le]
  have hf : HasDerivAt (fun u => ∑ k ∈ Finset.range a, g (u - k) • W k x)
      (∑ k ∈ Finset.range a, g' (t - k) • W k x) t := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk := ((hd (t - k)).comp t ((hasDerivAt_id t).sub_const (k : ℝ))).smul_const (W k x)
    simpa using hk
  apply hf.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ha] with u hu
  exact eq_sum g hg W u x a hu.le

lemma pulse_slot {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℕ → A → E) (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) (x : A) :
    glue Profiles.pulse W t x = Profiles.pulse (t - k) • W k x := by
  apply tsum_eq_single k
  intro j hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    rw [Profiles.pulse_zero_right _ (by linarith [ht.1]), zero_smul]
  · have hj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj
    rw [Profiles.pulse_zero_left _ (by linarith [ht.2]), zero_smul]

lemma clock_slot {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℕ → A → E) (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) (x : A) :
    glue Profiles.clock W t x = (∑ j ∈ Finset.range k, W j x) +
      Profiles.clock (t - k) • W k x := by
  rw [eq_sum Profiles.clock (fun u hu => Profiles.clock_zero u (by linarith)) W t x
    (k + 1) (by simpa using ht.2), Finset.sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast (Finset.mem_range.1 hj)
  rw [Profiles.clock_one _ (by linarith [ht.1]), one_smul]

end TimeGlue
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Construction.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Construction

def donorIndex (n : ℕ) : Fin 3 :=
  letI := neZeroThree
  if n % 2 = 0 then 1 else 2

def receiverIndex (n : ℕ) : Fin 3 :=
  letI := neZeroThree
  if n % 2 = 0 then 2 else 1

lemma indices_distinct (n : ℕ) : receiverIndex n ≠ 0 ∧ donorIndex n ≠ receiverIndex n ∧
    donorIndex n ≠ 0 := by
  unfold donorIndex receiverIndex
  split_ifs <;> decide

noncomputable def slot (M : Machine) (N n : ℕ) : Space → Space :=
  letI := neZeroThree
  Spatial.localizedShear (donorIndex n) (receiverIndex n) 0
    (LocalRule.write M N n) (LocalRule.signal M N n)

noncomputable def loading (M : Machine) (w : List ℕ) : Space → Space :=
  letI := neZeroThree
  Spatial.localizedShear 2 1 0
    (fun _ => Scales.ε M.base w.length 0 * M.recordedBlock w 0)
    (fun _ => 1 - Scales.ε M.base w.length 0)

noncomputable def piece (M : Machine) (w : List ℕ) : ℕ → Space → Space :=
  fun n => Nat.casesOn n (loading M w) (fun k => slot M w.length k)

noncomputable def velocity (M : Machine) (w : List ℕ) : Velocity :=
  TimeGlue.glue Profiles.pulse (piece M w)

lemma slot_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (slot M N n) :=
  Spatial.localizedShear_smooth _ _ _ _ _ (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n)

lemma loading_smooth (M : Machine) (w : List ℕ) : ContDiff ℝ ∞ (loading M w) :=
  Spatial.localizedShear_smooth _ _ _ _ _ contDiff_const contDiff_const

lemma piece_smooth (M : Machine) (w : List ℕ) (n : ℕ) : ContDiff ℝ ∞ (piece M w n) := by
  cases n with
  | zero => exact loading_smooth M w
  | succ n => exact slot_smooth M w.length n

lemma piece_support (M : Machine) (w : List ℕ) (n : ℕ) :
    tsupport (piece M w n) ⊆ Spatial.box := by
  cases n <;> exact Spatial.localizedShear_support _ _ _ _ _

lemma piece_div (M : Machine) (w : List ℕ) (n : ℕ) (x : Space) :
    (∑ i : Fin 3, Spatial.d i (piece M w n) x i) = 0 := by
  cases n with
  | zero => exact Spatial.localizedShear_div _ _ _ _ _ contDiff_const contDiff_const x
  | succ n =>
    exact Spatial.localizedShear_div _ _ _ _ _ (LocalRule.write_smooth M w.length n)
      (LocalRule.signal_smooth M w.length n) x

lemma velocity_smooth (M : Machine) (w : List ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (velocity M w)) :=
  TimeGlue.smooth Profiles.pulse Profiles.pulse_zero_left Profiles.pulse_smooth
    (piece M w) (piece_smooth M w)

lemma velocity_supported (M : Machine) (w : List ℕ) (t : ℝ) :
    Function.support (velocity M w t) ⊆ Spatial.box := by
  intro x hx
  by_contra hn
  have hz (k : ℕ) : piece M w k x = 0 := by
    by_contra hk
    exact hn (piece_support M w k (subset_closure hk))
  exact hx (by simp [velocity, TimeGlue.glue, hz])

lemma velocity_rest (M : Machine) (w : List ℕ) (x : Space) : velocity M w 0 x = 0 := by
  rw [velocity, TimeGlue.pulse_slot _ 0 0 (by norm_num) x]
  simp [Profiles.pulse_zero_left]

lemma velocity_div (M : Machine) (w : List ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    div (velocity M w) t x = 0 := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  have heq : velocity M w t = (fun x => Profiles.pulse (t - k) • piece M w k x) :=
    funext (TimeGlue.pulse_slot _ k t hk)
  unfold div dx
  rw [heq]
  have hd := (piece_smooth M w k).differentiable (by simp) x
  change (∑ i : Fin 3, (fderiv ℝ (Profiles.pulse (t - k) • piece M w k) x (e i)) i) = 0
  simp only [fderiv_const_smul hd, smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  change Profiles.pulse (t - k) * (∑ i : Fin 3, Spatial.d i (piece M w k) x i) = 0
  rw [piece_div, mul_zero]

lemma slot_plateau (M : Machine) (N n : ℕ) (x : Space) (hx : x ∈ Spatial.plateau) :
    slot M N n x = LocalRule.write M N n (x (donorIndex n)) • e (receiverIndex n) +
      LocalRule.signal M N n (x (donorIndex n)) • e 0 :=
  Spatial.localizedShear_plateau _ _ _ (indices_distinct n).1 (indices_distinct n).2.1
    (indices_distinct n).2.2 _ _ (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n) x hx

lemma loading_plateau (M : Machine) (w : List ℕ) (x : Space) (hx : x ∈ Spatial.plateau) :
    loading M w x = (Scales.ε M.base w.length 0 * M.recordedBlock w 0) • e 1 +
      (1 - Scales.ε M.base w.length 0) • e 0 :=
  Spatial.localizedShear_plateau 2 1 0 (by decide) (by decide) (by decide)
    _ _ contDiff_const contDiff_const x hx

end Construction
end AlternatingNS

namespace AlternatingNS
namespace Construction

lemma donorIndex_succ (n : ℕ) : donorIndex (n + 1) = receiverIndex n := by
  unfold donorIndex receiverIndex
  split_ifs <;> omega

lemma donorIndex_eq (j n : ℕ) : donorIndex j = donorIndex n ↔ j % 2 = n % 2 := by
  unfold donorIndex
  split_ifs <;> norm_num <;> omega

noncomputable def memory (M : Machine) (w : List ℕ) (n : ℕ) : Space :=
  ∑ j ∈ Finset.range (n + 1),
    (Scales.ε M.base w.length j * M.recordedBlock w j) • e (donorIndex j)

noncomputable def history (M : Machine) (w : List ℕ) (n : ℕ) : Space :=
  memory M w n + Detector.signal M.base w.length (fun j => M.isHalting (M.run w j)) n • e 0

noncomputable def displacement (M : Machine) (w : List ℕ) : ℕ → Space
  | 0 => (Scales.ε M.base w.length 0 * M.recordedBlock w 0) • e 1 +
      (1 - Scales.ε M.base w.length 0) • e 0
  | n + 1 => (Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1)) •
      e (receiverIndex n) +
      Detector.increment M.base w.length (fun j => M.isHalting (M.run w j)) n • e 0

noncomputable def node (M : Machine) (w : List ℕ) : ℕ → Space
  | 0 => observedParticle
  | n + 1 => history M w n

noncomputable def path (M : Machine) (w : List ℕ) (t : ℝ) : Space :=
  observedParticle + TimeGlue.glue Profiles.clock (fun k (_ : Unit) => displacement M w k) t ()

lemma memory_zero_coord (M : Machine) (w : List ℕ) (n : ℕ) : memory M w n 0 = 0 := by
  have h0 (j : ℕ) : (0 : Fin 3) ≠ donorIndex j := (indices_distinct j).2.2.symm
  simp [memory, WithLp.ofLp_sum, Finset.sum_apply, Spatial.e_apply, h0]

lemma memory_donor (M : Machine) (w : List ℕ) (n : ℕ) :
    memory M w n (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  simp only [memory, Encoding.donor, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Spatial.e_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [donorIndex_eq, eq_comm (a := n % 2) (b := j % 2), mul_ite, mul_one, mul_zero]

lemma memory_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    memory M w (n + 1) = memory M w n +
      (Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1)) • e (receiverIndex n) := by
  simp only [memory, Finset.sum_range_succ (n := n + 1), donorIndex_succ]

lemma history_zero_coord (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w n 0 = Detector.signal M.base w.length (fun j => M.isHalting (M.run w j)) n := by
  simp [history, PiLp.add_apply, memory_zero_coord, PiLp.smul_apply, Spatial.e_apply]

lemma history_donor (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w n (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  simp [history, PiLp.add_apply, memory_donor, PiLp.smul_apply, Spatial.e_apply, (indices_distinct n).2.2]

lemma history_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w (n + 1) = history M w n + displacement M w (n + 1) := by
  simp only [history, memory_succ, Detector.signal, displacement, add_smul]
  abel

lemma observedParticle_eq : observedParticle = -e 0 := by
  ext i
  fin_cases i <;> norm_num [observedParticle, e, PiLp.single_apply, PiLp.neg_apply,
    EuclideanSpace.single, EuclideanSpace.equiv]

lemma node_succ (M : Machine) (w : List ℕ) (k : ℕ) :
    node M w (k + 1) = node M w k + displacement M w k := by
  cases k with
  | zero =>
    simp only [node, history, memory, Nat.zero_add, Finset.sum_range_one, donorIndex, Nat.zero_mod,
      ite_true, Detector.signal, displacement, observedParticle_eq, sub_smul, one_smul, neg_smul]
    abel
  | succ n => exact history_succ M w n

lemma node_sum (M : Machine) (w : List ℕ) (k : ℕ) :
    node M w k = observedParticle + ∑ j ∈ Finset.range k, displacement M w j := by
  induction k with
  | zero => simp [node]
  | succ k ih => rw [node_succ, ih, Finset.sum_range_succ, add_assoc]

lemma path_slot (M : Machine) (w : List ℕ) (k : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) :
    path M w t = node M w k + Profiles.clock (t - k) • displacement M w k := by
  rw [path, TimeGlue.clock_slot _ k t ht (), ← add_assoc, ← node_sum]

lemma path_node (M : Machine) (w : List ℕ) (k : ℕ) : path M w k = node M w k := by
  rw [path_slot M w k k (by constructor <;> linarith)]
  simp [Profiles.clock_zero]

lemma memory_bound (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (n : ℕ) (i : Fin 3) : 0 ≤ memory M w n i ∧ memory M w n i < 1 / 4 := by
  have hb := M.base_ge_four
  have he (j : ℕ) := Scales.ε_nonneg M.base w.length j (by omega)
  have hC (j : ℕ) := M.recordedBlock_mem hM w hw j
  have hm := Encoding.tailMax_lt_one M.base (by omega)
  have hterm (j : ℕ) : 0 ≤ ((Scales.ε M.base w.length j * M.recordedBlock w j) •
      e (donorIndex j)) i ∧
      ((Scales.ε M.base w.length j * M.recordedBlock w j) • e (donorIndex j)) i ≤
        Scales.ε M.base w.length j := by
    simp only [PiLp.smul_apply, Spatial.e_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact ⟨mul_nonneg (he j) (hC j).1, mul_le_of_le_one_right (he j) ((hC j).2.trans hm.le)⟩
    · simp only [mul_zero]
      exact ⟨le_rfl, he j⟩
  simp only [memory, WithLp.ofLp_sum, Finset.sum_apply]
  refine ⟨Finset.sum_nonneg (fun j _ => (hterm j).1), ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), Scales.ε M.base w.length j :=
      Finset.sum_le_sum (fun j _ => (hterm j).2)
    _ ≤ ∑' j, Scales.ε M.base w.length j :=
      (Scales.summable_ε M.base w.length (by omega)).sum_le_tsum _ (fun j _ => he j)
    _ ≤ 2 * Scales.ε M.base w.length 0 := Scales.total_memory_le _ _ (by omega)
    _ < 1 / 4 := Scales.initial_memory_small _ _ hb

lemma node_plateau (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (k : ℕ) : node M w k ∈ Spatial.plateau := by
  have hb := M.base_ge_four
  intro i
  cases k with
  | zero =>
    simp only [node, observedParticle_eq, PiLp.neg_apply, Spatial.e_apply]
    split_ifs <;> norm_num
  | succ n =>
    change |history M w n i| < 2
    by_cases hi : i = 0
    · rw [hi, history_zero_coord]
      have hp := Detector.signal_in_plateau M.base w.length hb
        (fun j => M.isHalting (M.run w j)) n
      exact (abs_lt.2 hp).trans (by norm_num)
    · simp only [history, PiLp.add_apply, PiLp.smul_apply, Spatial.e_apply,
        ite_eq_right hi, smul_eq_mul, mul_zero, add_zero]
      rw [abs_of_nonneg (memory_bound M hM w hw n i).1]
      exact (memory_bound M hM w hw n i).2.trans (by norm_num)

lemma segment_plateau (a b : Space) (ha : a ∈ Spatial.plateau) (hb : b ∈ Spatial.plateau)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : (1 - θ) • a + θ • b ∈ Spatial.plateau := by
  intro i
  have hai := abs_lt.mp (ha i)
  have hbi := abs_lt.mp (hb i)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  apply abs_lt.mpr
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (le_of_lt (sub_pos.mpr hai.2)),
    mul_nonneg hθ.1 (le_of_lt (sub_pos.mpr hbi.2)),
    mul_nonneg (sub_nonneg.mpr hθ.2) (le_of_lt (sub_pos.mpr hai.1)),
    mul_nonneg hθ.1 (le_of_lt (sub_pos.mpr hbi.1))]

lemma path_plateau (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (t : ℝ) (ht : 0 ≤ t) : path M w t ∈ Spatial.plateau := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [path_slot M w k t hk]
  have heq : node M w k + Profiles.clock (t - k) • displacement M w k =
      (1 - Profiles.clock (t - k)) • node M w k + Profiles.clock (t - k) • node M w (k + 1) := by
    rw [node_succ, smul_add, sub_smul, one_smul]
    abel
  rw [heq]
  exact segment_plateau _ _ (node_plateau M hM w hw k) (node_plateau M hM w hw (k + 1))
    _ (Profiles.clock_mem _)

end Construction
end AlternatingNS

namespace AlternatingNS
namespace Construction

lemma path_donor (M : Machine) (w : List ℕ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc ((n : ℝ) + 1) (n + 1 + 1)) :
    path M w t (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  have ht' : t ∈ Set.Icc ((n + 1 : ℕ) : ℝ) ((n + 1 : ℕ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  rw [path_slot M w (n + 1) t ht']
  simp only [node, PiLp.add_apply, PiLp.smul_apply, history_donor, displacement,
    Spatial.e_apply, (indices_distinct n).2.1, (indices_distinct n).2.2,
    ite_false, smul_eq_mul, mul_zero, add_zero]

lemma piece_path (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) :
    piece M w k (path M w t) = displacement M w k := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg k) ht.1
  have hp := path_plateau M hM w hw t ht0
  cases k with
  | zero => exact loading_plateau M w _ hp
  | succ n =>
    change slot M w.length n (path M w t) = _
    rw [slot_plateau M w.length n _ hp,
      path_donor M w n t (by simpa only [Nat.cast_add, Nat.cast_one] using ht),
      LocalRule.write_run M hM w hw, LocalRule.signal_run M hM w hw]
    rfl

lemma velocity_path (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (t : ℝ) (ht : 0 ≤ t) :
    velocity M w t (path M w t) =
      TimeGlue.glue Profiles.pulse (fun k (_ : Unit) => displacement M w k) t () := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [velocity, TimeGlue.pulse_slot _ k t hk, TimeGlue.pulse_slot _ k t hk,
    piece_path M hM w hw k t hk]

theorem path_isTrajectory (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) :
    IsTrajectory (velocity M w) observedParticle (path M w) := by
  refine ⟨by simpa only [Nat.cast_zero, node] using path_node M w 0, ?_⟩
  intro t ht
  rw [velocity_path M hM w hw t ht]
  exact ((TimeGlue.hasDerivAt Profiles.clock Profiles.pulse
    (fun s hs => Profiles.clock_zero s (by linarith)) Profiles.pulse_zero_left
    Profiles.clock_hasDeriv (fun k (_ : Unit) => displacement M w k) t ()).const_add
      observedParticle).hasDerivWithinAt

lemma path_loading_coord (M : Machine) (w : List ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    path M w t 0 = Detector.loading M.base w.length (Profiles.clock t) := by
  rw [path_slot M w 0 t (by simpa using ht)]
  simp [node, observedParticle_eq, displacement, PiLp.add_apply, PiLp.smul_apply,
    PiLp.neg_apply, Spatial.e_apply, Detector.loading]

lemma path_slot_coord (M : Machine) (w : List ℕ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc ((n : ℝ) + 1) (n + 1 + 1)) :
    path M w t 0 = Detector.during M.base w.length (fun j => M.isHalting (M.run w j)) n
      (Profiles.clock (t - (n + 1))) := by
  rw [path_slot M w (n + 1) t (by simpa only [Nat.cast_add, Nat.cast_one] using ht)]
  simp [node, displacement, PiLp.add_apply, PiLp.smul_apply, Spatial.e_apply,
    (indices_distinct n).1.symm, Detector.during, history_zero_coord]

theorem path_reachability (M : Machine) (w : List ℕ) :
    (∃ t : ℝ, 0 ≤ t ∧ 0 < path M w t 0) ↔ M.Halts w := by
  have hb := M.base_ge_four
  constructor
  · rintro ⟨t, ht, hp⟩
    have hk : t ∈ Set.Icc (⌊t⌋₊ : ℝ) (⌊t⌋₊ + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
    generalize hfloor : ⌊t⌋₊ = k at hk
    cases k with
    | zero =>
      have ht' : t ∈ Set.Icc 0 1 := by simpa using hk
      rw [path_loading_coord M w t ht'] at hp
      exact False.elim ((Detector.loading_negative M.base w.length (by omega) _
        (Profiles.clock_mem t)).not_gt hp)
    | succ n =>
      rw [path_slot_coord M w n t (by simpa only [Nat.cast_add, Nat.cast_one] using hk)] at hp
      exact (Detector.machine_scalar_reachability M.base (by omega) M w).mp
        ⟨n, _, Profiles.clock_mem _, hp⟩
  · intro h
    let n := Nat.find h
    have hn : M.isHalting (M.run w n) = true := Nat.find_spec h
    have hprev : ∀ j < n, M.isHalting (M.run w j) = false :=
      fun j hj => Bool.eq_false_iff.2 (Nat.find_min h hj)
    refine ⟨((n + 1 + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [path_node]
    change 0 < history M w (n + 1) 0
    rw [history_zero_coord, Detector.signal_first_halt M.base w.length _ n hprev hn]
    exact Scales.ε_pos M.base w.length (n + 1) (by omega)

end Construction
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Analytic.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Analytic

lemma spatial_fderiv_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  exact (hF.comp ((contDiff_fst.fst).prodMk contDiff_snd)).fderiv contDiff_snd (by simp)

lemma dx_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Fin 3) :
    ContDiff ℝ ∞ (Function.uncurry (dx i F)) :=
  (spatial_fderiv_smooth F hF).clm_apply contDiff_const

noncomputable def fullDt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Field E := fun t x => fderiv ℝ (fun s => F s x) t 1

lemma fullDt_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (Function.uncurry (fullDt F)) := by
  exact ((hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv contDiff_fst (by simp)).clm_apply
    contDiff_const

lemma dt_eq_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    dt F t x = fullDt F t x := by
  unfold dt fullDt
  have hd : DifferentiableAt ℝ (fun s => F s x) t :=
    ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_Ici _ _ ht) hd]

lemma smooth_classical (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ClassicalRegularity U (fun _ _ => 0) := by
  refine ⟨fun x => ?_, fun t _ => ?_, fun t _ i => ?_, fun t _ => differentiable_const _, ?_⟩
  · exact ((hU.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableOn
  · exact (hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · exact ((dx_smooth U hU i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · intro T _
    refine ⟨hU.continuous.continuousOn, ?_, fun i => (dx_smooth U hU i).continuous.continuousOn,
      fun i j => (dx_smooth (dx j U) (dx_smooth U hU j) i).continuous.continuousOn,
      continuousOn_const, ?_⟩
    · apply (fullDt_smooth U hU).continuous.continuousOn.congr
      intro z hz
      exact dt_eq_full U hU z.1 hz.1.1 z.2
    · intro i
      change ContinuousOn (fun z : ℝ × Space => fderiv ℝ (fun _ : Space => (0 : ℝ)) z.2 (e i)) _
      simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × Space => (0 : ℝ))
        (timeCylinder T))

lemma residual_navierStokes (ν : ℝ) (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (h0 : ∀ x, U 0 x = 0) (hd : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    NavierStokes ν (residual ν U) U (fun _ _ => 0) := by
  refine ⟨smooth_classical U hU, h0, fun t ht x => ⟨hd t ht x, ?_⟩⟩
  have hp : grad (fun _ _ => 0) t x = 0 := by
    ext i
    simp [grad, dx, EuclideanSpace.equiv]
  rw [hp, residual]
  abel

lemma advection_smooth (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (Function.uncurry (advection U)) :=
  (spatial_fderiv_smooth U hU).clm_apply hU

lemma laplacian_smooth (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (Function.uncurry (laplacian U)) := by
  change ContDiff ℝ ∞ (fun z : ℝ × Space => ∑ i : Fin 3, dx i (dx i U) z.1 z.2)
  apply ContDiff.sum
  intro i _
  exact dx_smooth (dx i U) (dx_smooth U hU i) i

lemma residual_smooth (ν : ℝ) (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    Smooth (residual ν U) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space =>
      fullDt U z.1 z.2 + advection U z.1 z.2 - ν • laplacian U z.1 z.2) :=
    ((fullDt_smooth U hU).add (advection_smooth U hU)).sub
      ((laplacian_smooth U hU).const_smul ν)
  apply hf.contDiffOn.congr
  intro z hz
  simp only [Function.uncurry, residual, dt_eq_full U hU z.1 hz.1]

lemma dx_supported {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hF : ∀ t, Function.support (F t) ⊆ K) (i : Fin 3) :
    ∀ t, Function.support (dx i F t) ⊆ K := by
  intro t x hx
  exact (closure_minimal (hF t) hK) ((Spatial.d_tsupport i (F t)) (subset_closure hx))

lemma outside_dt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (K : Set Space) (hF : ∀ t, Function.support (F t) ⊆ K)
    (t : ℝ) (x : Space) (hx : x ∉ K) : dt F t x = 0 := by
  have he : (fun s => F s x) = fun _ => 0 := by
    funext s
    exact Function.notMem_support.1 (fun hx' => hx (hF s hx'))
  simp [dt, he]

lemma residual_supported (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsClosed K)
    (hU : ∀ t, Function.support (U t) ⊆ K) :
    ∀ t, Function.support (residual ν U t) ⊆ K := by
  intro t x hx
  by_contra hn
  have hUx : U t x = 0 := Function.notMem_support.1 (fun hx' => hn (hU t hx'))
  have hΔ : laplacian U t x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Function.notMem_support.1 (fun hx' => hn (dx_supported (dx i U) K hK
      (dx_supported U K hK hU i) i t hx'))
  exact hx (by simp [residual, outside_dt U K hU t x hn, advection, hUx, hΔ])

lemma finite_bound {E : Type*} [NormedAddCommGroup E]
    (F : Field E) (hF : Continuous (Function.uncurry F)) (K : Set Space) (hK : IsCompact K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (T : ℝ) :
    ∃ C : ℝ≥0, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖F t x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨⟨max 0 C, le_max_left _ _⟩, fun t ht x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_right _ _)
  · have hz : F t x = 0 := Function.notMem_support.1 (fun hx' => hx (hs t hx'))
    simp only [hz, norm_zero]
    exact le_max_left _ _

lemma finite_lipschitz (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) (T : ℝ) :
    ∃ C : ℝ≥0, ∀ t ∈ Set.Icc 0 T, LipschitzWith C (U t) := by
  have hder : ∀ t, Function.support (fderiv ℝ (U t)) ⊆ K :=
    fun t => (support_fderiv_subset ℝ).trans (closure_minimal (hs t) hK.isClosed)
  obtain ⟨C, hC⟩ := finite_bound (fun t x => fderiv ℝ (U t) x)
    (spatial_fderiv_smooth U hU).continuous K hK hder T
  refine ⟨C, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    ((hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast hC t ht x

end Analytic
end AlternatingNS

namespace AlternatingNS
namespace Analytic

lemma trajectory_unique (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) (γ δ : ℝ → Space) (hγ : IsTrajectory U a γ) (hδ : IsTrajectory U a δ)
    (T : ℝ) (hT : 0 ≤ T) : γ T = δ T := by
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  have hc (β : ℝ → Space) (hβ : IsTrajectory U a β) : ContinuousOn β (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn (fun t ht => (hβ.2 t ht.1).mono Set.Icc_subset_Ici_self)
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hC t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (hc γ hγ) (fun t ht => (hγ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun _ _ => Set.mem_univ _) (hc δ hδ)
    (fun t ht => (hδ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun _ _ => Set.mem_univ _) (hγ.1.trans hδ.1.symm) ⟨hT, le_rfl⟩

lemma finite_trajectory (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → Space, γ 0 = a ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (U t (γ t)) (Set.Icc 0 T) t := by
  obtain ⟨L, hL⟩ := finite_bound U hU.continuous K hK hs T
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hpl : IsPicardLindelof U t₀ a (L * ⟨T, hT⟩) 0 L C := by
    refine ⟨fun t ht => (hC t ht).lipschitzOnWith, fun x _ => ?_,
      fun t ht x _ => hL t ht x, ?_⟩
    · exact (hU.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · change (L : ℝ) * max (T - 0) (0 - 0) ≤ (L : ℝ) * T - 0
      simp [max_eq_left hT]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma finite_trajectory_unique (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (γ δ : ℝ → Space) (T : ℝ) (h0 : γ 0 = δ 0)
    (hγ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (U t (γ t)) (Set.Icc 0 T) t)
    (hδ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt δ (U t (δ t)) (Set.Icc 0 T) t) :
    Set.EqOn γ δ (Set.Icc 0 T) := by
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  have hd (β : ℝ → Space)
      (hβ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt β (U t (β t)) (Set.Icc 0 T) t) :
      ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt β (U t (β t)) (Set.Ici t) t := by
    intro t ht
    apply (hβ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (fun y hy => ⟨ht.1.trans hy.1, hy.2⟩)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hC t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hγ) (hd γ hγ) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hδ) (hd δ hδ) (fun _ _ => Set.mem_univ _) h0

lemma global_trajectory (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) : ∃ γ, IsTrajectory U a γ := by
  classical
  have hex (n : ℕ) := finite_trajectory U hU K hK hs a ((n : ℝ) + 1) (by positivity)
  choose α hα₀ hα using hex
  have coherent (n m : ℕ) (t : ℝ) (ht : 0 ≤ t) (hn : t ≤ (n : ℝ) + 1)
      (hm : t ≤ (m : ℝ) + 1) : α n t = α m t := by
    apply finite_trajectory_unique U hU K hK hs (α n) (α m) t
      ((hα₀ n).trans (hα₀ m).symm)
      (fun s hs => (hα n s ⟨hs.1, hs.2.trans hn⟩).mono
        (Set.Icc_subset_Icc le_rfl hn))
      (fun s hs => (hα m s ⟨hs.1, hs.2.trans hm⟩).mono
        (Set.Icc_subset_Icc le_rfl hm)) ⟨ht, le_rfl⟩
  let γ : ℝ → Space := fun t => α ⌈t⌉₊ t
  have agrees (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 ((n : ℝ) + 1)) : γ t = α n t :=
    coherent _ _ t ht.1 (by linarith [Nat.le_ceil t]) ht.2
  refine ⟨γ, ?_, fun t ht => ?_⟩
  · exact hα₀ _
  · obtain ⟨n, hn⟩ := exists_nat_gt t
    have htn : t < (n : ℝ) + 1 := by linarith
    have hmem : Set.Icc 0 ((n : ℝ) + 1) ∈ 𝓝[Set.Ici 0] t := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (Iio_mem_nhds htn))] with s hs hs'
      exact ⟨hs, hs'.le⟩
    have he := agrees n t ⟨ht, htn.le⟩
    rw [he]
    apply ((hα n t ⟨ht, htn.le⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
    · filter_upwards [hmem] with s hs
      exact agrees n s hs
    · exact he

theorem global_material_flow (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) :
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory U a (X a)) ∧
      (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) := by
  classical
  choose X hX using global_trajectory U hU K hK hs
  exact ⟨X, hX, fun a γ hγ t ht => trajectory_unique U hU K hK hs a γ (X a) hγ (hX a) t ht⟩

end Analytic
end AlternatingNS

namespace AlternatingNS
namespace Construction

noncomputable def force (ν : ℝ) (M : Machine) (w : List ℕ) : Velocity :=
  residual ν (velocity M w)

theorem smooth_forced_simulation (ν : ℝ) (M : Machine) (hM : M.WellFormed)
    (w : List ℕ) (hw : M.ValidInput w) :
    Smooth (force ν M w) ∧ Smooth (velocity M w) ∧
    SupportedIn (force ν M w) Spatial.box ∧ SupportedIn (velocity M w) Spatial.box ∧
    NavierStokes ν (force ν M w) (velocity M w) (fun _ _ => 0) ∧
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory (velocity M w) a (X a)) ∧
      (∀ a γ, IsTrajectory (velocity M w) a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
      ((∃ t : ℝ, 0 ≤ t ∧ 0 < X observedParticle t 0) ↔ M.Halts w) := by
  have hU := velocity_smooth M w
  have hK := Spatial.box_compact
  have hs := velocity_supported M w
  refine ⟨Analytic.residual_smooth ν _ hU, hU.contDiffOn,
    fun t _ => Analytic.residual_supported ν _ _ hK.isClosed hs t,
    fun t _ => hs t,
    Analytic.residual_navierStokes ν _ hU (velocity_rest M w) (velocity_div M w), ?_⟩
  obtain ⟨X, hX, hu⟩ := Analytic.global_material_flow _ hU _ hK hs
  refine ⟨X, hX, hu, ?_⟩
  have he : ∀ t, 0 ≤ t → path M w t = X observedParticle t :=
    hu _ _ (path_isTrajectory M hM w hw)
  rw [← path_reachability M w]
  exact ⟨fun ⟨t, ht, hp⟩ => ⟨t, ht, by rw [he t ht]; exact hp⟩,
    fun ⟨t, ht, hp⟩ => ⟨t, ht, by rw [← he t ht]; exact hp⟩⟩

end Construction
end AlternatingNS
namespace AlternatingNS
namespace Analytic

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def zeroExtend (K : Set Space) (g : C(K, E)) (x : Space) : E := by
  classical
  exact if hx : x ∈ K then g ⟨x, hx⟩ else 0

omit [NormedSpace ℝ E] in
lemma zeroExtend_memLp (K : Set Space) (hK : IsCompact K) (g : C(K, E)) :
    MemLp (zeroExtend K g) 2 (volume : Measure Space) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hm : StronglyMeasurable (zeroExtend K g) :=
    g.continuous.stronglyMeasurable.dite stronglyMeasurable_const hK.measurableSet
  have hs : HasCompactSupport (zeroExtend K g) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hx'
    exact hx (by simp [zeroExtend, hx'])
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖g‖
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · simpa [zeroExtend, hx] using g.norm_coe_le_norm ⟨x, hx⟩
  · simp [zeroExtend, hx]

def compactToL2 (K : Set Space) (hK : IsCompact K) [CompactSpace K] :
    C(K, E) →L[ℝ] Lp E 2 (volume : Measure Space) := by
  classical
  let A : C(K, E) →ₗ[ℝ] Lp E 2 (volume : Measure Space) :=
    { toFun := fun g => (zeroExtend_memLp K hK g).toLp (zeroExtend K g)
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [(zeroExtend_memLp K hK (g + h)).coeFn_toLp,
          Lp.coeFn_add ((zeroExtend_memLp K hK g).toLp _) ((zeroExtend_memLp K hK h).toLp _),
          (zeroExtend_memLp K hK g).coeFn_toLp, (zeroExtend_memLp K hK h).coeFn_toLp]
          with x hx hx' hg hh
        simp only [hx, hx', Pi.add_apply, hg, hh]
        by_cases hk : x ∈ K <;> simp [zeroExtend, hk]
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [(zeroExtend_memLp K hK (c • g)).coeFn_toLp,
          Lp.coeFn_smul c ((zeroExtend_memLp K hK g).toLp _),
          (zeroExtend_memLp K hK g).coeFn_toLp] with x hx hx' hg
        simp only [RingHom.id_apply, hx, hx', Pi.smul_apply, hg]
        by_cases hk : x ∈ K <;> simp [zeroExtend, hk] }
  let B : Lp ℝ 2 (volume : Measure Space) :=
    indicatorConstLp 2 hK.measurableSet hK.measure_ne_top 1
  apply A.mkContinuous ‖B‖
  intro g
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := B)
  filter_upwards [(zeroExtend_memLp K hK g).coeFn_toLp, indicatorConstLp_coeFn
    (p := 2) (hs := hK.measurableSet) (hμs := hK.measure_ne_top) (c := (1 : ℝ))] with x hx hb
  change ‖((zeroExtend_memLp K hK g).toLp _) x‖ ≤ _
  rw [hx, hb]
  by_cases hk : x ∈ K
  · simpa [zeroExtend, hk] using g.norm_coe_le_norm ⟨x, hk⟩
  · simp [zeroExtend, hk]

lemma compactToL2_coe (K : Set Space) (hK : IsCompact K) [CompactSpace K] (g : C(K, E)) :
    ∀ᵐ x ∂(volume : Measure Space), compactToL2 K hK g x = zeroExtend K g x :=
  (zeroExtend_memLp K hK g).coeFn_toLp

def onCompact (F : Field E) (hF : Continuous (Function.uncurry F)) (K : Set Space)
    (t : ℝ) : C(K, E) :=
  ⟨fun x => F t x, hF.comp (continuous_const.prodMk continuous_subtype_val)⟩

omit [NormedSpace ℝ E] in
lemma onCompact_continuous (F : Field E) (hF : Continuous (Function.uncurry F))
    (K : Set Space) : Continuous (onCompact F hF K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

lemma compactToL2_onCompact (F : Field E) (hF : Continuous (Function.uncurry F))
    (K : Set Space) (hK : IsCompact K) [CompactSpace K]
    (hs : ∀ t, Function.support (F t) ⊆ K) (t : ℝ) :
    ∀ᵐ x ∂(volume : Measure Space), compactToL2 K hK (onCompact F hF K t) x = F t x := by
  classical
  filter_upwards [compactToL2_coe K hK (onCompact F hF K t)] with x hx
  rw [hx]
  by_cases hk : x ∈ K
  · simp only [zeroExtend, dite_eq_left hk]
    rfl
  · have hz : F t x = 0 := Function.notMem_support.1 (fun hx => hk (hs t hx))
    simp [zeroExtend, hk, hz]

lemma onCompact_hasDerivAt [CompleteSpace E] (F : Field E)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set Space) [CompactSpace K] (t : ℝ) :
    HasDerivAt (onCompact F hF.continuous K)
      (onCompact (fullDt F) (fullDt_smooth F hF).continuous K t) t := by
  let H := onCompact F hF.continuous K
  let G := onCompact (fullDt F) (fullDt_smooth F hF).continuous K
  have hG : Continuous G := onCompact_continuous _ _ _
  have he (s : ℝ) : H s = H 0 + ∫ r in (0 : ℝ)..s, G r := by
    ext x
    change F s x = F 0 x + (ContinuousMap.evalCLM ℝ x) (∫ r in (0 : ℝ)..s, G r)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hG.intervalIntegrable 0 s)]
    have hd (r : ℝ) : HasDerivAt (fun t => F t x) (fullDt F r x) r :=
      ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) r).hasFDerivAt.hasDerivAt
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ Set.uIcc 0 s) => hd r)
      (((fullDt_smooth F hF).continuous.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable 0 s)
    change F s x = F 0 x + ∫ r in (0 : ℝ)..s, fullDt F r x
    rw [hi]
    abel
  have h : HasDerivAt (fun s => H 0 + ∫ r in (0 : ℝ)..s, G r) (G t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 t)
      (hG.stronglyMeasurableAtFilter volume (𝓝 t)) hG.continuousAt).const_add (H 0)
  rwa [← funext he] at h

lemma iterate_dx_smooth (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (i : Fin 3) (n : ℕ) : ContDiff ℝ ∞ (Function.uncurry ((dx i)^[n] F)) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dx_smooth _ ih i

lemma spatial_smooth (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (α : MultiIndex) : ContDiff ℝ ∞ (Function.uncurry (spatial α F)) :=
  iterate_dx_smooth _ (iterate_dx_smooth _ (iterate_dx_smooth F hF 2 _) 1 _) 0 _

lemma iterate_dx_supported (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (i : Fin 3) (n : ℕ) :
    ∀ t, Function.support ((dx i)^[n] F t) ⊆ K := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dx_supported _ K hK ih i

lemma spatial_supported (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (α : MultiIndex) :
    ∀ t, Function.support (spatial α F t) ⊆ K :=
  iterate_dx_supported _ K hK
    (iterate_dx_supported _ K hK (iterate_dx_supported F K hK hs 2 _) 1 _) 0 _

lemma fullDt_supported (F : Field E) (K : Set Space)
    (hs : ∀ t, Function.support (F t) ⊆ K) :
    ∀ t, Function.support (fullDt F t) ⊆ K := by
  intro t x hx
  by_contra hk
  have he : (fun s => F s x) = fun _ => 0 := by
    funext s
    exact Function.notMem_support.1 (fun hx' => hk (hs s hx'))
  exact hx (by simp [fullDt, he])

lemma smooth_continuousInH (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (F t) ⊆ K)
    (k : ℕ) (T : ℝ) : ContinuousInH k F T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro α _
  let hα := (spatial_smooth F hF α).continuous
  refine ⟨fun t => compactToL2 K hK (onCompact (spatial α F) hα K t), ?_, ?_⟩
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · intro t _
    exact compactToL2_onCompact _ hα K hK (spatial_supported F K hK.isClosed hs α) t

lemma smooth_C1InL2 (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (T : ℝ) : C1InL2 U T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let H := onCompact U hU.continuous K
  let G := onCompact (fullDt U) (fullDt_smooth U hU).continuous K
  refine ⟨fun t => compactToL2 K hK (H t), fun t => compactToL2 K hK (G t), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · intro t _
    exact ((compactToL2 K hK).hasFDerivAt.comp_hasDerivAt t
      (onCompact_hasDerivAt U hU K t)).hasDerivWithinAt
  · intro t _
    exact compactToL2_onCompact U hU.continuous K hK hs t
  · intro t ht
    filter_upwards [compactToL2_onCompact (fullDt U) (fullDt_smooth U hU).continuous
      K hK (fullDt_supported U K hs) t] with x hx
    rw [hx, dt_eq_full U hU t ht.1]

theorem smooth_energyClass (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) :
    EnergyClass U (fun _ _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro T _
    obtain ⟨C, hC⟩ := finite_bound U hU.continuous K hK hs T
    exact ⟨smooth_continuousInH U hU K hK hs 2 T, smooth_C1InL2 U hU K hK hs T,
      smooth_continuousInH (fun _ _ => (0 : ℝ)) contDiff_const K hK
        (fun _ => by simp) 1 T, C, hC⟩
  · intro T _
    obtain ⟨C, hC⟩ := finite_bound U hU.continuous K hK hs T
    obtain ⟨D, hD⟩ := finite_bound (fun t x => fderiv ℝ (U t) x)
      (spatial_fderiv_smooth U hU).continuous K hK
      (fun t => (support_fderiv_subset ℝ).trans (closure_minimal (hs t) hK.isClosed)) T
    exact ⟨C + D, fun t ht x => add_le_add (hC t ht x) (hD t ht x)⟩

end
end Analytic

namespace Construction

theorem velocity_energyClass (M : Machine) (w : List ℕ) :
    EnergyClass (velocity M w) (fun _ _ => 0) :=
  Analytic.smooth_energyClass _ (velocity_smooth M w) _ Spatial.box_compact (velocity_supported M w)

end Construction
end AlternatingNS

end OAI


