-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
-- name    : OAI_Analysis_BackwardIntertwiners_HaarBase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:58:21.277102+00:00
-- url     : https://prove2.me/theorems/2c8ee1e3-d0ac-4145-8f45-9f1181ac6431
-- title:
--   Haar measure on the 2-adic integers, the odometer and residues modulo $2^m$
-- statement:
--   This file sets up the probability space and the ergodic transformation on which the model operators are built: the 2-adic integers $\mathbb{Z}_2$ with Haar measure and the odometer $x\mapsto x+1$. The compact abelian group $\mathbb{Z}_2$ carries its Borel $\sigma$-algebra.
--
--   1. **Haar measure.** $\mu_0$ is the additive Haar measure on $\mathbb{Z}_2$ normalized by $\mu_0(\mathbb{Z}_2)=1$. It is a regular, translation-invariant probability measure, all points have the same measure, and every point has measure $0$.
--   2. **Odometer.** $\sigma(x)=x+1$ on $\mathbb{Z}_2$; it is ergodic for $\mu_0$.
--   3. **Residues.** For $m\in\mathbb{N}$, $\rho_m(x)\in\{0,1,\dots,2^m-1\}$ is the residue of $x$ modulo $2^m$, the natural number representing the image of $x$ under the reduction $\mathbb{Z}_2\to\mathbb{Z}/2^m\mathbb{Z}$. The reduction map is continuous (locally constant), and $\rho_m$ is measurable with $\rho_m(x)<2^m$.
--   4. **Completed base.** The base space $X$ is $\mathbb{Z}_2$ with the $\sigma$-algebra of $\mu_0$-null-measurable sets, and $\mu$ is the completion of $\mu_0$. Then $\mu$ is a probability measure, singletons are measurable and $\mu$-null, the odometer $\sigma:X\to X$ is ergodic for $\mu$, and each $\rho_m$ is measurable on $X$. Two general lemmas show that a measure-preserving (respectively ergodic) map stays measure-preserving (respectively ergodic) for the completed measure.
--   5. **Good points.** $X_{\mathrm{good}}=X\setminus\mathbb{Z}$, the complement of the image of the ordinary integers in $\mathbb{Z}_2$. It is measurable, and of full measure since its complement is countable.
--
--   The residues obey the following rules, recorded in the file: $\rho_m(x)=2^m-1$ if and only if $x\equiv-1\pmod{2^m}$; for every $x\in X_{\mathrm{good}}$ there is $M$ with $\rho_m(x)\ne2^m-1$ for all $m\ge M$; and for $m\ge1$ the odometer acts by the carry rule
--   $$\rho_m(x+1)=\begin{cases}0,&\rho_m(x)=2^m-1,\\\rho_m(x)+1,&\text{otherwise.}\end{cases}$$
--   Consequently, at a good point adding $1$ raises every sufficiently high residue by exactly $1$. The fiber weights of the model are built from the residues $\rho_m(x)$, and this controlled effect of the odometer on them is what allows a bounded backward operator intertwining the fibers over $x$ and $x+1$.
--
--   **Formalization Note** The Borel sigma-algebra on `PadicInt 2` is installed as an instance; `baseHaar` is `Measure.addHaarMeasure ⊤`, normalized on the whole compact group. `Base` is `NullMeasurableSpace (PadicInt 2) baseHaar` and `baseMeasure` is `baseHaar.completion`. `twoResidue m x` and `residue m x` are `ZMod.val` of `PadicInt.toZModPow m x`, and `goodBase` is the complement of the range of the cast from the integers. Further names: `odometerBorel`, `odometer`, `measurePreserving_completion`, `ergodic_completion`, `residue_exceptional_iff`, `goodBase_eventually_nonexceptional`, `residue_step`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/HaarBase.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/HaarBase.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

instance padicBorel : MeasurableSpace (PadicInt 2) := borel _
instance padicBorelSpace : BorelSpace (PadicInt 2) := ⟨rfl⟩

def baseHaar : Measure (PadicInt 2) := Measure.addHaarMeasure ⊤
instance baseHaar_probability : IsProbabilityMeasure baseHaar := by
  constructor
  exact Measure.addHaarMeasure_self
instance baseHaar_regular : baseHaar.Regular := inferInstanceAs ((Measure.addHaarMeasure ⊤).Regular)
instance baseHaar_addHaar : baseHaar.IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure ⊤).IsAddHaarMeasure)

def odometerBorel (x : PadicInt 2) : PadicInt 2 := x + 1
lemma odometerBorel_ergodic : Ergodic odometerBorel baseHaar := by
  have hd : DenseRange (fun n : ℤ => n • (1 : PadicInt 2)) := by
    simpa only [zsmul_one] using (PadicInt.denseRange_intCast (p := 2))
  have he : (fun x : PadicInt 2 => 1+x) = odometerBorel := funext fun x => add_comm 1 x
  rw [← he]
  exact ergodic_add_left_of_denseRange_zsmul hd baseHaar

lemma continuous_twoResidue (m : ℕ) : Continuous (PadicInt.toZModPow (p := 2) m) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : 0 < (2:ℝ)^(-(m:ℤ)) := zpow_pos (by norm_num) _
  filter_upwards [Metric.ball_mem_nhds x hp] with y hy
  have hnorm : ‖y-x‖ ≤ (2:ℝ)^(-(m:ℤ)) := (by simpa [dist_eq_norm] using hy : ‖y-x‖ < _).le
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (y-x) m).mp hnorm
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  exact hmem

def twoResidue (m : ℕ) (x : PadicInt 2) : ℕ := (PadicInt.toZModPow m x).val
lemma twoResidue_lt (m : ℕ) (x : PadicInt 2) : twoResidue m x < 2^m := ZMod.val_lt _
lemma measurable_twoResidue (m : ℕ) : Measurable (twoResidue m) :=
  (measurable_of_countable (f := ZMod.val)).comp (continuous_twoResidue m).measurable

lemma baseHaar_singleton_eq (x y : PadicInt 2) : baseHaar {x} = baseHaar {y} := by
  have he : (fun z : PadicInt 2 => (y-x)+z) ⁻¹' {y} = {x} := by
    ext z
    change (y-x)+z = y ↔ z = x
    constructor
    · intro h
      have hh := congrArg (fun v : PadicInt 2 => v-(y-x)) h
      abel_nf at hh
      exact hh
    · rintro rfl
      abel
  rw [← he]
  exact measure_preimage_add baseHaar (y-x) {y}

instance baseHaar_nullSingleton : NullSingletonClass baseHaar := by
  constructor
  intro x
  by_contra hx
  have hd : Pairwise (fun i j : ℕ => Disjoint ({(i:PadicInt 2)} : Set (PadicInt 2)) {(j:PadicInt 2)}) := by
    intro i j hij
    apply Set.disjoint_singleton.mpr
    exact_mod_cast hij
  have hs : (∑' _n : ℕ, baseHaar {x}) ≤ 1 := calc
    _ = ∑' n : ℕ, baseHaar {(n:PadicInt 2)} := tsum_congr fun n => baseHaar_singleton_eq _ _
    _ = baseHaar (⋃ n : ℕ, {(n:PadicInt 2)}) := (measure_iUnion hd (fun _ => measurableSet_singleton _)).symm
    _ ≤ 1 := by simpa using (measure_mono (Set.subset_univ _) : baseHaar _ ≤ baseHaar Set.univ)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hx] at hs
  exact (not_le_of_gt ENNReal.one_lt_top) hs

lemma measurePreserving_completion {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → α} (hf : MeasurePreserving f μ μ) :
    @MeasurePreserving (NullMeasurableSpace α μ) (NullMeasurableSpace α μ) _ _
      f μ.completion μ.completion := by
  have hm : @Measurable (NullMeasurableSpace α μ) (NullMeasurableSpace α μ) _ _ f := by
    intro s hs
    change NullMeasurableSet (f ⁻¹' s) μ
    exact NullMeasurableSet.preimage (μb := μ) (show NullMeasurableSet (show Set α from s) μ from hs) hf.quasiMeasurePreserving
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs]
  exact hf.measure_preimage hs

lemma ergodic_completion {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → α} (hf : Ergodic f μ) :
    @Ergodic (NullMeasurableSpace α μ) _ f μ.completion := by
  refine ⟨measurePreserving_completion hf.toMeasurePreserving, ?_⟩
  constructor
  intro s hs he
  exact hf.quasiErgodic.aeconst_set₀ hs (Filter.EventuallyEq.of_eq he)

abbrev Base := NullMeasurableSpace (PadicInt 2) baseHaar
abbrev baseMeasure : Measure Base := baseHaar.completion
instance base_probability : IsProbabilityMeasure baseMeasure := ⟨measure_univ (μ := baseHaar)⟩
instance base_nullSingleton : NullSingletonClass baseMeasure := by
  constructor
  intro x
  change baseHaar { (show PadicInt 2 from x) } = 0
  exact measure_singleton _
instance base_measurableSingleton : MeasurableSingletonClass Base := by
  constructor
  intro x
  exact measurableSet_of_null (μ := baseMeasure) (measure_singleton x)

def odometer : Base → Base := odometerBorel
lemma odometer_ergodic : Ergodic odometer baseMeasure := by
  change @Ergodic (NullMeasurableSpace (PadicInt 2) baseHaar) _ odometerBorel baseHaar.completion
  exact ergodic_completion (α := PadicInt 2) odometerBorel_ergodic

def residue (m : ℕ) (x : Base) : ℕ := twoResidue m x
lemma residue_lt (m : ℕ) (x : Base) : residue m x < 2^m := twoResidue_lt m x
lemma measurable_residue (m : ℕ) : Measurable (residue m) :=
  (measurable_twoResidue m).nullMeasurable.measurable'

def goodBase : Set Base := (Set.range (fun n : ℤ => (show Base from (n : PadicInt 2))))ᶜ
lemma measurableSet_goodBase : MeasurableSet goodBase := by
  apply MeasurableSet.compl
  exact (Set.countable_range _).measurableSet
lemma zmod_val_neg_one {N : ℕ} (hN : 0 < N) : (-1 : ZMod N).val = N-1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp [ZMod.val_neg_one]

lemma residue_exceptional_iff (m : ℕ) (x : Base) :
    residue m x = 2^m-1 ↔ PadicInt.toZModPow m x = (-1 : ZMod (2^m)) := by
  change (PadicInt.toZModPow m x).val = _ ↔ _
  rw [← zmod_val_neg_one (pow_pos (by norm_num : 0 < 2) m)]
  exact (ZMod.val_injective (2^m)).eq_iff

lemma goodBase_eventually_nonexceptional {x : Base} (hx : x ∈ goodBase) :
    ∃ M : ℕ, ∀ m ≥ M, residue m x ≠ 2^m-1 := by
  have hx' : (show PadicInt 2 from x) ≠ -1 := by
    intro h
    apply hx
    refine ⟨-1, ?_⟩
    change ((-1:ℤ):PadicInt 2) = (show PadicInt 2 from x)
    simpa using h.symm
  have hex : ∃ M, PadicInt.toZModPow M x ≠ PadicInt.toZModPow M (-1:PadicInt 2) := by
    by_contra! h
    exact hx' (PadicInt.ext_of_toZModPow.mp h)
  obtain ⟨M, hM⟩ := hex
  refine ⟨M, fun m hm he => hM ?_⟩
  have heq := (residue_exceptional_iff m x).mp he
  have hc := congrArg (ZMod.castHom (pow_dvd_pow 2 hm) (ZMod (2^M))) heq
  change ZMod.cast (PadicInt.toZModPow m (show PadicInt 2 from x)) = _ at hc
  rw [PadicInt.cast_toZModPow M m hm] at hc
  simpa only [map_neg, map_one] using hc

lemma residue_step {m : ℕ} (hm : 1 ≤ m) (x : Base) :
    residue m (odometer x) = if residue m x = 2^m-1 then 0 else residue m x + 1 := by
  have hN' : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
  have hN : 1 < 2^m := by omega
  have : Fact (1 < 2^m) := ⟨hN⟩
  change ((PadicInt.toZModPow m) ((show PadicInt 2 from x)+1)).val = _
  rw [map_add, map_one, ZMod.val_add, ZMod.val_one]
  change (residue m x + 1) % 2^m = _
  have hr := residue_lt m x
  split_ifs with h
  · have he : residue m x+1 = 2^m := by omega
    simp [he]
  · exact Nat.mod_eq_of_lt (by omega)

end
end BackwardIntertwiners

end OAI


