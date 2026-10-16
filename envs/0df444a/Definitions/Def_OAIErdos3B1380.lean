-- Prove2me | Definitions.Def_OAIErdos3B1380
-- name    : OAIErdos3B1380
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T04:01:15.848957+00:00
-- url     : https://prove2.me/theorems/c0a84745-76b8-474c-8f4c-7d749e595504
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1381 of 1394
-- statement:
--   Definitions bundle 1381 of 1394 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1379`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1381 available.
--
--   Modules: `OAI.Erdos3.WeightedParameterPatch.value_mem_Icc`, `OAI.Erdos3.booleanSamplerMap_formula`, `OAI.Erdos3.crtInput_reduce`, `OAI.Erdos3.jointBooleanSampler_formula`, `OAI.Erdos3.jointBooleanSampler_measurable_comp`, `OAI.Erdos3.jointBooleanSampler_measurable_frozen`, `OAI.Erdos3.monomialArrayPolynomial_rescale`, `OAI.Erdos3.normalizedMonomialTerm`, `OAI.Erdos3.polynomialMassC2Budget_le_exp`, `OAI.Erdos3.polynomialMassC2Budget_nonneg`, `OAI.Erdos3.principalTupleFlatten_apply`, `OAI.Erdos3.residueLatticeImage_index_le_period`, `OAI.Erdos3.scalarCubeDomainDensity_le_exp`, `OAI.Erdos3.scalarCubeDomainDensity_le_power`, `OAI.Erdos3.scalarCubeDomainDensity_pos`, `OAI.Erdos3.scalarCubeInnerBox_subset`, `OAI.Erdos3.scalarCubeInnerBox_volume`, `OAI.Erdos3.scalarCubeValue_sub_bound`, `OAI.Erdos3.tensorCutoffWeight_compact`, `OAI.Erdos3.tensorCutoffWeight_tsupport`, `OAI.Erdos3.uniformPMF_map_hom_index`, `OAI.Erdos3.uniformResidueMatrix_density_bound`, `OAI.Erdos3.uniformResidueSmallPeriodDensity_bounds`, `OAI.Erdos3.uniform_mean_surjective_hom_fiber`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B209
import Definitions.Def_OAIErdos3B1372
import Definitions.Def_OAIErdos3B1379

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

omit [DecidableEq B] [DecidableEq F] in
theorem booleanSamplerMap_formula (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) :
    booleanSamplerMap c sets a o = booleanCoefficient
      (fun t => ∑ b : B, c b * ∏ k : F, ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, k, r)) (sets o) := by
  simp only [booleanSamplerMap, booleanSamplerPolynomial, booleanCoefficient_map, map_sum,
    map_mul, MvPolynomial.eval_C, booleanBlockPolynomial, map_prod, booleanAffinePolynomial_eval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

theorem polynomialMassC2Budget_nonneg (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialMassC2Budget N d C := by unfold polynomialMassC2Budget; positivity

theorem polynomialMassC2Budget_le_exp (N d : ℕ) {C P Q : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hN : (N : ℝ) ≤ Real.exp P) (hCQ : C ≤ Real.exp Q) :
    polynomialMassC2Budget N d C ≤ Real.exp (2 * P + 2 * d + Q + 2) := by
  have hN1 := one_add_le_exp_succ hP hN
  have hd1 : (d : ℝ) + 1 ≤ Real.exp d := Real.add_one_le_exp _
  have hb : 1 + (N : ℝ) * d ≤ Real.exp (P + d + 1) := by
    calc
      _ ≤ (1 + (N : ℝ)) * ((d : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) d]
      _ ≤ Real.exp (P + 1) * Real.exp d := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp (P + d + 1))^2 * Real.exp Q := by
      unfold polynomialMassC2Budget
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem normalizedMonomialTerm {K : Type*} (m : K →₀ ℕ) (scale value : K → ℝ)
    (Q b : ℝ) (hQ : Q ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    ((Q * b / (∏ k ∈ m.support, scale k ^ m k)) *
      (∏ k ∈ m.support, (scale k * value k) ^ m k)) / Q =
        b * ∏ k ∈ m.support, value k ^ m k := by
  classical
  have hs : (∏ k ∈ m.support, scale k ^ m k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hscale k))
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeInnerBox_subset (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeInnerBox I ⊆ scalarCubeDomain I := by
  intro x hx t
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have hn : ‖x-scalarCubeCenter I‖ ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |x i-scalarCubeCenter I i| ≤ _
    exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
  have hb := scalarCubeValue_sub_bound x (scalarCubeCenter I) hr hn t
  rw [scalarCubeValue_center] at hb
  have he : ((Fintype.card I : ℝ)+1)*(1/(4*((Fintype.card I : ℝ)+1))) = 1/4 := by
    field_simp
  rw [he] at hb
  have ha := abs_le.mp hb
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

theorem scalarCubeInnerBox_volume (I : Type*) [Fintype I] :
    volume.real (scalarCubeInnerBox I) = (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have ho : (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) ≤
      (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))) := fun i => by linarith
  have he (i : Option I) : scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))-
      (scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) = 1/(2*((Fintype.card I : ℝ)+1)) := by
    field_simp
    ring
  simp only [measureReal_def, scalarCubeInnerBox, Real.volume_Icc_pi_toReal ho, he,
    Finset.prod_const, Finset.card_univ, Fintype.card_option]

theorem scalarCubeDomainDensity_le_power (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by
  have hv := measureReal_mono (scalarCubeInnerBox_subset I) (scalarCubeDomain_volume_lt_top I).ne
  rw [scalarCubeInnerBox_volume] at hv
  have hp : 0 < (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by positivity
  have hi := one_div_le_one_div_of_le hp hv
  simpa only [scalarCubeDomainDensity, one_div, inv_pow, inv_inv] using hi

theorem scalarCubeDomainDensity_le_exp (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ Real.exp (((Fintype.card I : ℝ)+1)^2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hb : 2*((Fintype.card I : ℝ)+1) ≤ Real.exp ((Fintype.card I : ℝ)+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp (Fintype.card I) := by gcongr; exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_add, add_comm]
  calc
    _ ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := scalarCubeDomainDensity_le_power I
    _ ≤ (Real.exp ((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialArrayJet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem monomialArrayPolynomial_rescale {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (scale x : K → ℝ) (H : ℝ)
    (hH : H ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    MvPolynomial.eval (fun k => scale k*x k)
      (monomialArrayPolynomial e (fun j => H*a j/monomialScale scale (e j)))/H =
      MvPolynomial.eval x (monomialArrayPolynomial e a) := by
  rw [monomialArrayPolynomial_eval, monomialArrayPolynomial_eval, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => normalizedMonomialTerm (e j) scale x H (a j) hH hscale)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanSamplerMeasurability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointBooleanSampler_formula {D α : Type*} [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    jointBooleanSampler h c sets x o = booleanCoefficient
      (fun t => ∑ b : B o.1, c o.1 b * ∏ v : Fin (h o.1),
        ∑ r : Option α, (booleanFeature r t : ℝ) * x ⟨o.1, (b, v, r)⟩) (sets o.1 o.2) := by
  apply booleanSamplerMap_formula

theorem jointBooleanSampler_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun ω => c ω d b))
    (x : Ω → JointBlockParameter B h α → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => jointBooleanSampler h (c ω) sets (x ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  simp_rw [jointBooleanSampler_formula, booleanCoefficient]
  fun_prop

theorem jointBooleanSampler_measurable_frozen {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b)) :
    Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      jointBooleanSampler h (c p.1) sets p.2) :=
  jointBooleanSampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets
    (fun p => c p.1) (fun d b => (hc d b).comp measurable_fst)
    (fun p => p.2) (fun i => (measurable_pi_apply i).comp measurable_snd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem principalTupleFlatten_apply {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) (z : JointBlockParameter B h α) :
    principalTupleFlatten B h α x z = x ⟨z.1, z.2.1, z.2.2.1⟩ z.2.2.2 := rfl

end Erdos3

namespace Erdos3

open MeasureTheory

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem residueLatticeImage_index_le_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (d m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L d).toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have hcard := residueLatticeImage_card_mul_index L m hperiod
  have hn : L.toAddSubgroup.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    exact pow_ne_zero _ (NeZero.ne m) hcard.symm
  have hd := L.toAddSubgroup.index_map_dvd (f := (integerResidueMap I d).toAddMonoidHom)
    (integerResidueMap_surjective I d)
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans
    (residueLatticeImage_index_le L m hperiod)

theorem uniformResidueMatrix_density_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d m : ℕ) [NeZero d] [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (r : I → ZMod d) :
    (d : ℝ) ^ Fintype.card I *
      (((PMF.uniformOfFintype (J → ZMod d)).map
        (fun x => integerResidueMatrix A d *ᵥ x)) r).toReal ≤ (m : ℝ) ^ Fintype.card I := by
  let f := (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
  have hr : f.range = (residueLatticeImage A.mulVecLin.range d).toAddSubgroup := by
    ext y
    exact (integerMatrixResidue_mem A d y).symm
  have hi : (f.range.index : ℝ) ≤ (m : ℝ) ^ Fintype.card I := by
    rw [hr]
    exact_mod_cast residueLatticeImage_index_le_period A.mulVecLin.range d m hperiod
  have hc : (Fintype.card (I → ZMod d) : ℝ) = (d : ℝ) ^ Fintype.card I := by
    simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  have hc0 : (Fintype.card (I → ZMod d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (d : ℝ) ^ Fintype.card I * (((PMF.uniformOfFintype (J → ZMod d)).map f) r).toReal ≤ _
  rw [uniformPMF_map_hom_index, ← hc]
  by_cases h : r ∈ f.range
  · simp only [h, ite_true]
    convert hi using 1
    field_simp
  · simp only [h, ite_false, zero_div, mul_zero]
    positivity

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformResidueSmallPeriodDensity_bounds {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range) (r : I → ZMod period) :
    0 ≤ uniformResidueSmallPeriodDensity A d period r ∧
      uniformResidueSmallPeriodDensity A d period r ≤ (period : ℝ) ^ Fintype.card I := by
  constructor
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg
  · exact uniformResidueMatrix_density_bound A d period hperiod _

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d : ℕ} {w : Fin d → ℕ}

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace SlotInterleaving

end SlotInterleaving

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

end WeightedParameterSlots

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {s d : ℕ}

end WeightedParameterPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

theorem crtInput_reduce (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : ∀ l : L, V → ZMod (q l)) (l : L) (v : V) :
    ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ l)) (ZMod (q l))
      (crtInput q hq x v) = x l v := by
  rw [← ZMod.prodEquivPi_apply q hq]
  exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => x l v)) l

end Erdos3

end

end OAI

end


