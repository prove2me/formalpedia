-- Prove2me | Definitions.Def_OAIQWSQN001
-- name    : OAIQWSQN001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:55:16.759993+00:00
-- url     : https://prove2.me/theorems/907c8e84-a431-43be-a891-416a7c86e255
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN001
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   The construction chooses its thinned windows with the infinite Ramsey theorem. The bundle does not prove it: it imports the published statement `OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset` of this split, which has its own proof.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It imports no other bundle of this split.
--
--   Modules: `BlockApproximation`, `BlockEstimates`, `BoundedCompleteness`, `BranchPaths`, `BranchReduction`, `Complexification`, `CoordinateDual`, `EvaluationCriterion`, `FiniteNormers`, `MarkedEstimates`, `PathConvergence`, `PathStabilization`, `PerturbationOperator`, `PrefixNormers`, `ProductQuotients`, `QuotientPerturbation`, `RamseyThinning`, `RealCoefficients`, `StrictSingularity`, `WindowCharges`, `WindowThinning`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib
import Theorems.Thm_OAI_SeparableQuotient_InfiniteRamsey_homogeneous_subset

section
-- module Solutions.OAIQW_SeparableQuotient.QuotientPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient

open MeasureTheory Cardinal

universe u

section Perturbation

variable {𝕜 : Type} [RCLike 𝕜]
variable {M : Type u} [NormedAddCommGroup M] [NormedSpace 𝕜 M]

/-- A quotient lift with norm bounded by 11/10 times the quotient norm. -/
theorem quotient_lift (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)] (w : M ⧸ Y) :
    ∃ y : M, Y.mkQL y = w ∧ ‖y‖ ≤ (11 / 10 : ℝ) * ‖w‖ := by
  by_cases hw : w = 0
  · subst w
    exact ⟨0, map_zero _, by simp⟩
  · have hp : 0 < ‖w‖ / 10 := div_pos (norm_pos_iff.mpr hw) (by norm_num)
    obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt w hp
    refine ⟨y, hy, ?_⟩
    linarith

noncomputable def quotientRightInverse (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)] :
    Y.mkQL.NonlinearRightInverse where
  toFun w := (quotient_lift Y w).choose
  nnnorm := 11 / 10
  bound' w := by
    simpa using (quotient_lift Y w).choose_spec.2
  right_inv' w := (quotient_lift Y w).choose_spec.1

/-- Quantitative lift constant for a perturbed quotient map. -/
noncomputable def liftConstant (b : ℝ) : ℝ := (11 / 10) / (1 - (11 / 10) * b)

theorem liftConstant_properties {b : ℝ} (_hb0 : 0 ≤ b) (hb : b ≤ 1 / 10) :
    0 < liftConstant b ∧ liftConstant b * b < 1 ∧
      ((11 / 10 : ℝ)⁻¹ - b) * liftConstant b = 1 := by
  have hd : 0 < 1 - (11 / 10 : ℝ) * b := by linarith
  dsimp [liftConstant]
  refine ⟨div_pos (by norm_num) hd, ?_, ?_⟩
  · apply (div_mul_eq_mul_div _ _ _).trans_lt
    apply (div_lt_one hd).mpr
    linarith
  · have hh : 10 - b * 11 ≠ 0 := by linarith
    have he : ((11 / 10 : ℝ)⁻¹ - b) * (11 / 10) = 1 - (11 / 10) * b := by
      norm_num
      ring
    rw [← mul_div_assoc, he, div_self hd.ne']

/-- A 1/10 perturbation of a quotient map is onto, with a quantitative nonlinear lift bound. -/
theorem perturbed_quotient_lift [CompleteSpace M]
    (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)]
    (B : M →L[𝕜] M ⧸ Y) (hB : ‖B‖ ≤ 1 / 10) (w : M ⧸ Y) :
    ∃ y : M, (Y.mkQL - B) y = w ∧ ‖y‖ ≤ liftConstant ‖B‖ * ‖w‖ := by
  have hc := liftConstant_properties (norm_nonneg B) hB
  have ha : ApproximatesLinearOn (Y.mkQL - B) Y.mkQL Set.univ ‖B‖₊ := by
    intro x _ y _
    have he : (Y.mkQL - B) x - (Y.mkQL - B) y - Y.mkQL (x - y) = -(B (x - y)) := by
      simp only [sub_apply, map_sub]
      abel
    rw [he, norm_neg]
    exact B.le_opNorm (x - y)
  have hs := ha.surjOn_closedBall_of_nonlinearRightInverse (quotientRightInverse Y)
    (b := 0) (ε := liftConstant ‖B‖ * ‖w‖)
    (mul_nonneg hc.1.le (norm_nonneg w)) (Set.subset_univ _)
  have hw : w ∈ Metric.closedBall ((Y.mkQL - B) 0)
      ((((quotientRightInverse Y).nnnorm : ℝ)⁻¹ - (‖B‖₊ : ℝ)) *
        (liftConstant ‖B‖ * ‖w‖)) := by
    simp only [map_zero, Metric.mem_closedBall, dist_zero_right]
    change ‖w‖ ≤ ((11 / 10 : ℝ)⁻¹ - ‖B‖) * (liftConstant ‖B‖ * ‖w‖)
    rw [← mul_assoc, hc.2.2, one_mul]
  obtain ⟨y, hy, he⟩ := hs hw
  exact ⟨y, he, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy⟩

/-- The image of the perturbed kernel is dense in the closure of the image of the original kernel. -/
theorem perturbed_quotient_dense [CompleteSpace M]
    (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)]
    (B : M →L[𝕜] M ⧸ Y) (hB : ‖B‖ ≤ 1 / 10)
    (hBV : ∀ y : M, B y ∈ (Y.map B.toLinearMap).topologicalClosure) :
    ((Y.mkQL - B).ker.map B.toLinearMap).topologicalClosure =
      (Y.map B.toLinearMap).topologicalClosure := by
  let V := (Y.map B.toLinearMap).topologicalClosure
  let G := ((Y.mkQL - B).ker.map B.toLinearMap).topologicalClosure
  have hGV : G ≤ V := by
    apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
    rintro w ⟨x, hx, rfl⟩
    exact hBV x
  have hG : IsClosed (G : Set (M ⧸ Y)) := Submodule.isClosed_topologicalClosure _
  let := hG
  have hsmall : (‖B‖ * liftConstant ‖B‖) * (11 / 10) < 1 := by
    have hd : 0 < 1 - (11/10:ℝ)*‖B‖ := by linarith
    dsimp [liftConstant]
    calc
      ‖B‖ * (11 / 10 / (1 - 11 / 10 * ‖B‖)) * (11 / 10) =
          (‖B‖ * (11 / 10) * (11 / 10)) / (1 - 11 / 10 * ‖B‖) := by ring
      _ < 1 := (div_lt_one hd).mpr (by nlinarith [norm_nonneg B])
  have hVbound : ∀ v ∈ V, ‖G.mkQL v‖ ≤ (‖B‖ * liftConstant ‖B‖) * ‖v‖ := by
    apply closure_minimal ?_ (isClosed_le (G.mkQL.continuous.norm)
      (continuous_const.mul continuous_norm))
    rintro v ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hnx⟩ := perturbed_quotient_lift Y B hB (B y)
    have hQy : Y.mkQL y = 0 := (Submodule.Quotient.mk_eq_zero Y).mpr hy
    have hyx : y + x ∈ (Y.mkQL - B).ker := by
      change (Y.mkQL - B) (y + x) = 0
      rw [map_add, hx]
      simp [hQy]
    have hg : B (y + x) ∈ G :=
      Submodule.le_topologicalClosure _ ⟨y + x, hyx, rfl⟩
    have hzero : G.mkQL (B (y + x)) = 0 :=
      (Submodule.Quotient.mk_eq_zero G).mpr hg
    have he : G.mkQL (B y) = -G.mkQL (B x) := by
      simpa only [map_add, eq_neg_iff_add_eq_zero] using hzero
    change ‖G.mkQL (B y)‖ ≤ (‖B‖ * liftConstant ‖B‖) * ‖B y‖
    rw [he, norm_neg]
    calc
      ‖G.mkQL (B x)‖ ≤ ‖B x‖ := Submodule.Quotient.norm_mk_le G (B x)
      _ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
      _ ≤ ‖B‖ * (liftConstant ‖B‖ * ‖B y‖) :=
        mul_le_mul_of_nonneg_left hnx (norm_nonneg B)
      _ = (‖B‖ * liftConstant ‖B‖) * ‖B y‖ := (mul_assoc _ _ _).symm
  apply le_antisymm hGV
  intro v hv
  obtain ⟨z, hz, hnz⟩ := quotient_lift G (G.mkQL v)
  have hvz : v - z ∈ G := (Submodule.Quotient.eq G).mp hz.symm
  have hzV : z ∈ V := by
    have := V.sub_mem hv (hGV hvz)
    simpa using this
  have hn := hVbound z hzV
  rw [hz] at hn
  have hg0 := (liftConstant_properties (norm_nonneg B) hB).1.le
  have hnn : ‖G.mkQL v‖ ≤ (‖B‖ * liftConstant ‖B‖ * (11 / 10)) * ‖G.mkQL v‖ := by
    calc
      ‖G.mkQL v‖ ≤ (‖B‖ * liftConstant ‖B‖) * ‖z‖ := hn
      _ ≤ (‖B‖ * liftConstant ‖B‖) * ((11 / 10) * ‖G.mkQL v‖) :=
        mul_le_mul_of_nonneg_left hnz (mul_nonneg (norm_nonneg B) hg0)
      _ = _ := (mul_assoc _ _ _).symm
  have hzq : G.mkQL v = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (G.mkQL v)]
  exact (Submodule.Quotient.mk_eq_zero G).mp hzq

end Perturbation

noncomputable def equivOfBijective {𝕜 : Type} [RCLike 𝕜]
    {M N : Type u} [NormedAddCommGroup M] [NormedSpace 𝕜 M] [CompleteSpace M]
    [NormedAddCommGroup N] [NormedSpace 𝕜 N] [CompleteSpace N]
    (f : M →L[𝕜] N) (hf : Function.Bijective f) : M ≃L[𝕜] N :=
  (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuous f.continuous

section Predual

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[reducible] noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 E) := inferInstance
@[reducible] noncomputable local instance dualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 E) := inferInstance

/-- Restriction of the canonical evaluation embedding to a subspace of the dual. -/
noncomputable def evalOn (Y : Submodule 𝕜 (StrongDual 𝕜 E)) :
    E →L[𝕜] StrongDual 𝕜 Y :=
  (ContinuousLinearMap.precomp 𝕜 Y.subtypeL).comp (NormedSpace.inclusionInDoubleDual 𝕜 E)

@[simp] theorem evalOn_apply (Y : Submodule 𝕜 (StrongDual 𝕜 E)) (e : E) (y : Y) :
    evalOn Y e y = (y : StrongDual 𝕜 E) e := rfl

/-- Surjectivity from the adjoint-range hypothesis and Hahn–Banach,
using a quotient lift of the graph map. -/
theorem twisted_eval_surjective
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hY : Function.Surjective (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y)
    (hBadj : ∀ w : StrongDual 𝕜 ((StrongDual 𝕜 E) ⧸ Y),
      ∃ e : E, w.comp B = NormedSpace.inclusionInDoubleDual 𝕜 E e) :
    Function.Surjective (evalOn (Y.mkQL - B).ker) := by
  intro f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (Y.mkQL - B).ker f
  obtain ⟨e₀, he₀⟩ := hY (g.comp Y.subtypeL)
  let z := g - NormedSpace.inclusionInDoubleDual 𝕜 E e₀
  have hz : Y ≤ z.ker := by
    intro y hy
    change g y - y e₀ = 0
    have he := DFunLike.congr_fun he₀ (⟨y, hy⟩ : Y)
    exact sub_eq_zero.mpr he.symm
  let w := Y.liftQL z hz
  obtain ⟨e₁, he₁⟩ := hBadj w
  refine ⟨e₀ + e₁, ?_⟩
  ext x
  have hx : Y.mkQL (x : StrongDual 𝕜 E) = B x := by
    have := x.property
    change Y.mkQL (x : StrongDual 𝕜 E) - B x = 0 at this
    exact sub_eq_zero.mp this
  have hw : w (Y.mkQL (x : StrongDual 𝕜 E)) = g x - (x : StrongDual 𝕜 E) e₀ := rfl
  have he := DFunLike.congr_fun he₁ (x : StrongDual 𝕜 E)
  change w (B x) = (x : StrongDual 𝕜 E) e₁ at he
  rw [hx, he] at hw
  change (x : StrongDual 𝕜 E) (e₀ + e₁) = f x
  rw [map_add, hw, ← hg x]
  abel

/-- The small quotient perturbation preserves injectivity of evaluation. -/
theorem twisted_eval_injective
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hY : Isometry (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y) (hB : ‖B‖ ≤ 1 / 10) :
    Function.Injective (evalOn (Y.mkQL - B).ker) := by
  apply (injective_iff_map_eq_zero (evalOn (Y.mkQL - B).ker)).mpr
  intro e he
  have hc := liftConstant_properties (norm_nonneg B) hB
  have hbnd : ‖evalOn Y e‖ ≤ (liftConstant ‖B‖ * ‖B‖) * ‖e‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hc.1.le (norm_nonneg B)) (norm_nonneg e))
    intro y
    obtain ⟨t, ht, hnt⟩ := perturbed_quotient_lift Y B hB (B y)
    have hQy : Y.mkQL (y : StrongDual 𝕜 E) = 0 :=
      (Submodule.Quotient.mk_eq_zero Y).mpr y.property
    have hyt : (y : StrongDual 𝕜 E) + t ∈ (Y.mkQL - B).ker := by
      change (Y.mkQL - B) ((y : StrongDual 𝕜 E) + t) = 0
      rw [map_add, ht]
      simp [hQy]
    have heyt := DFunLike.congr_fun he
      (⟨(y : StrongDual 𝕜 E) + t, hyt⟩ : (Y.mkQL - B).ker)
    change (y : StrongDual 𝕜 E) e + t e = 0 at heyt
    have hye : (y : StrongDual 𝕜 E) e = -t e := eq_neg_of_add_eq_zero_left heyt
    rw [evalOn_apply, hye, norm_neg]
    calc
      ‖t e‖ ≤ ‖t‖ * ‖e‖ := t.le_opNorm e
      _ ≤ (liftConstant ‖B‖ * ‖B y‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right hnt (norm_nonneg e)
      _ ≤ (liftConstant ‖B‖ * (‖B‖ * ‖y‖)) * ‖e‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (B.le_opNorm y) hc.1.le) (norm_nonneg e)
      _ = ((liftConstant ‖B‖ * ‖B‖) * ‖e‖) * ‖y‖ := by ring
  have hn : ‖evalOn Y e‖ = ‖e‖ :=
    Isometry.norm_map_of_map_zero (f := fun x => evalOn Y x) hY (map_zero (evalOn Y)) e
  rw [hn] at hbnd
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg e]

noncomputable def twisted_eval_equiv [CompleteSpace E]
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hYiso : Isometry (evalOn Y)) (hYsurj : Function.Surjective (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y) (hB : ‖B‖ ≤ 1 / 10)
    (hBadj : ∀ w : StrongDual 𝕜 ((StrongDual 𝕜 E) ⧸ Y),
      ∃ e : E, w.comp B = NormedSpace.inclusionInDoubleDual 𝕜 E e) :
    E ≃L[𝕜] StrongDual 𝕜 (Y.mkQL - B).ker := by
  have hi : Function.Injective (evalOn (Y.mkQL - B).ker) :=
    twisted_eval_injective Y hYiso B hB
  have hs : Function.Surjective (evalOn (Y.mkQL - B).ker) :=
    twisted_eval_surjective Y hYsurj B hBadj
  exact equivOfBijective (𝕜 := 𝕜) (M := E) (N := StrongDual 𝕜 (Y.mkQL - B).ker)
    (evalOn (Y.mkQL - B).ker) ⟨hi, hs⟩

/-- A small perturbation of a quotient map produces an isomorphic dual of the perturbed kernel. -/
theorem twist [CompleteSpace E]
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hYiso : Isometry (evalOn Y)) (hYsurj : Function.Surjective (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y) (hB : ‖B‖ ≤ 1 / 10)
    (hBadj : ∀ w : StrongDual 𝕜 ((StrongDual 𝕜 E) ⧸ Y),
      ∃ e : E, w.comp B = NormedSpace.inclusionInDoubleDual 𝕜 E e)
    (hBrange : B.range ≤ (Y.map B.toLinearMap).topologicalClosure) :
    CompleteSpace (Y.mkQL - B).ker ∧
      (∃ T : E ≃L[𝕜] StrongDual 𝕜 (Y.mkQL - B).ker,
        ∀ (e : E) (x : (Y.mkQL - B).ker), T e x = (x : StrongDual 𝕜 E) e) ∧
      (((Y.mkQL - B).ker).map B.toLinearMap).topologicalClosure =
        (Y.map B.toLinearMap).topologicalClosure := by
  have : IsClosed ((Y.mkQL - B).ker : Set (StrongDual 𝕜 E)) :=
    (Y.mkQL - B).isClosed_ker
  refine ⟨inferInstance, ?_, perturbed_quotient_dense Y B hB (fun y => hBrange ⟨y, rfl⟩)⟩
  let T := twisted_eval_equiv Y hYiso hYsurj B hB hBadj
  exact ⟨T, fun _ _ => rfl⟩

end Predual

end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PrefixNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance prefixDualNormedGroup_r4cbc83_1 :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance prefixDualNormedSpace_r4cbc83_1 :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
/-- Finite prefix normers for a zero-based sequence. The existential formulation is equivalent to a maximum over the finite set. -/
structure PrefixNormers (f : ℕ → StrongDual 𝕜 X) where
  D : ℕ → Finset X
  unit : ∀ m, ∀ d ∈ D m, ‖d‖ ≤ 1
  norming : ∀ m, 0 < m → ∀ c : ℕ → 𝕜, ∃ d ∈ D m,
    ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖(∑ i ∈ Finset.range m, c i • f i) d‖
  vanish : ∀ m n, m ≤ n → ∀ d ∈ D m, f n d = 0

namespace PrefixNormers

@[reducible] noncomputable local instance prefixDualNormedGroup_r4cbc83_2 :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance prefixDualNormedSpace_r4cbc83_2 :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

theorem prefix_evaluation (c : ℕ → 𝕜) {m N : ℕ} (hmN : m ≤ N)
    {d : X} (hd : d ∈ H.D m) :
    (∑ i ∈ Finset.range N, c i • f i) d = (∑ i ∈ Finset.range m, c i • f i) d := by
  simp only [sum_apply, smul_apply]
  symm
  apply Finset.sum_subset (Finset.range_mono hmN)
  intro i hiN him
  have hmi : m ≤ i := by simpa using him
  rw [H.vanish m i hmi d hd, smul_zero]

include H

theorem prefix_bound (c : ℕ → 𝕜) {m N : ℕ} (hmN : m ≤ N) :
    ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  by_cases hm : m = 0
  · subst m; simp
  obtain ⟨d, hd, hb⟩ := H.norming m (Nat.pos_of_ne_zero hm) c
  rw [← H.prefix_evaluation c hmN hd] at hb
  apply hb.trans
  gcongr
  exact ((∑ i ∈ Finset.range N, c i • f i).le_opNorm d).trans
    (by
      simpa using mul_le_mul_of_nonneg_left (H.unit m d hd)
        (norm_nonneg (∑ i ∈ Finset.range N, c i • f i)))

theorem term_bound (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n • f n‖ ≤ 4 * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  have hp := H.prefix_bound c (Nat.succ_le_of_lt hn)
  have hq := H.prefix_bound c hn.le
  have he : c n • f n =
      (∑ i ∈ Finset.range (n + 1), c i • f i) - (∑ i ∈ Finset.range n, c i • f i) := by
    rw [Finset.sum_range_succ, add_sub_cancel_left]
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.FiniteNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance selectionDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance selectionDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

/-- Finite half-normers in the unit ball. -/
theorem exists_finite_normers (F : Submodule 𝕜 (StrongDual 𝕜 X))
    [FiniteDimensional 𝕜 F] :
    ∃ D : Finset X, (∀ d ∈ D, ‖d‖ ≤ 1) ∧
      ∀ v : F, ∃ d ∈ D, ‖v‖ ≤ 2 * ‖(v : StrongDual 𝕜 X) d‖ := by
  classical
  let U (d : closedBall (0 : X) 1) : Set F :=
    {v | (1 / 2 : ℝ) < ‖(v : StrongDual 𝕜 X) d‖}
  have hU : ∀ d, IsOpen (U d) := by
    intro d
    exact isOpen_lt continuous_const
      (((NormedSpace.inclusionInDoubleDual 𝕜 X d).comp F.subtypeL).continuous.norm)
  have hcover : sphere (0 : F) 1 ⊆ ⋃ d, U d := by
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hv
    obtain ⟨d, hd, he⟩ := (v : StrongDual 𝕜 X).exists_lt_apply_of_lt_opNorm
      (by change (1 / 2 : ℝ) < ‖v‖; rw [hn]; norm_num)
    exact Set.mem_iUnion.mpr ⟨⟨d, by simpa only [mem_closedBall, dist_zero_right] using hd.le⟩, he⟩
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : F) 1).elim_finite_subcover U hU hcover
  refine ⟨insert 0 (t.image Subtype.val), ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
      simpa only [mem_closedBall, dist_zero_right] using e.property
  · intro v
    by_cases hv : v = 0
    · subst v; exact ⟨0, Finset.mem_insert_self _ _, by simp⟩
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : F := (↑‖v‖ : 𝕜)⁻¹ • v
    have hw : w ∈ sphere (0 : F) 1 := by
      simp only [w, mem_sphere, dist_zero_right, norm_smul, norm_inv,
        RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hn]
    obtain ⟨d, hd, he⟩ := Set.mem_iUnion₂.mp (ht hw)
    refine ⟨d, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d, hd, rfl⟩), ?_⟩
    change (1 / 2 : ℝ) < ‖((↑‖v‖ : 𝕜)⁻¹ • (v : StrongDual 𝕜 X)) d‖ at he
    simp only [smul_apply, norm_smul, norm_inv,
      RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v)] at he
    have hm := (mul_lt_mul_of_pos_left he hp)
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at hm
    linarith

/-- Finite annihilation conditions leave a unit functional in every infinite-dimensional
subspace. -/
theorem exists_unit_annihilator (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (A : Finset X) :
    ∃ f : F, ‖f‖ = 1 ∧ ∀ x ∈ A, (f : StrongDual 𝕜 X) x = 0 := by
  classical
  let T : F →ₗ[𝕜] (A → 𝕜) :=
    { toFun := fun f x => (f : StrongDual 𝕜 X) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hex : ∃ f : F, f ≠ 0 ∧ ∀ x ∈ A, (f : StrongDual 𝕜 X) x = 0 := by
    by_contra! hn
    apply hF (FiniteDimensional.of_injective T ?_)
    intro a b hab
    apply sub_eq_zero.mp
    by_contra h
    obtain ⟨x, hx, hne⟩ := hn (a - b) h
    apply hne
    have he := congrFun hab ⟨x, hx⟩
    exact sub_eq_zero.mpr he
  obtain ⟨f, hf, hzero⟩ := hex
  refine ⟨(↑‖f‖ : 𝕜)⁻¹ • f, ?_, ?_⟩
  · simp only [norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg f), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hf)]
  · intro x hx
    simp [hzero x hx]

/-- One finite stage of the normer construction. -/
structure NormerStep (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (A : Finset X) (S : Finset (StrongDual 𝕜 X)) where
  f : F
  D : Finset X
  norm_f : ‖f‖ = 1
  vanish : ∀ x ∈ A, (f : StrongDual 𝕜 X) x = 0
  unit : ∀ d ∈ D, ‖d‖ ≤ 1
  norming : ∀ v ∈ Submodule.span 𝕜 (insert (f : StrongDual 𝕜 X) (S : Set _)),
    ∃ d ∈ D, ‖v‖ ≤ 2 * ‖v d‖

noncomputable def chooseNormerStep (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (A : Finset X) (S : Finset (StrongDual 𝕜 X)) :
    NormerStep F A S := Classical.choice <| by
  classical
  obtain ⟨f, hf, hv⟩ := exists_unit_annihilator F hF A
  let G := Submodule.span 𝕜 (insert (f : StrongDual 𝕜 X) (S : Set _))
  let : FiniteDimensional 𝕜 G := FiniteDimensional.span_of_finite 𝕜 (S.finite_toSet.insert _)
  obtain ⟨D, hD, hn⟩ := exists_finite_normers G
  exact ⟨⟨f, D, hf, hv, hD, fun v hv => hn ⟨v, hv⟩⟩⟩

namespace NormerStep
noncomputable local instance instDecidableEq : DecidableEq X := Classical.decEq X
noncomputable local instance instDecidableEqStrongDual : DecidableEq (StrongDual 𝕜 X) := Classical.decEq _
variable (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F)
variable (xs : ℕ → X)

/-- Accumulated annihilation constraints and preceding functionals. -/
noncomputable def state : ℕ → Finset X × Finset (StrongDual 𝕜 X)
  | 0 => (∅, ∅)
  | n + 1 =>
    let p := state n
    let q := chooseNormerStep F hF (insert (xs n) p.1) p.2
    (insert (xs n) (p.1 ∪ q.D), insert (q.f : StrongDual 𝕜 X) p.2)

noncomputable def stage (n : ℕ) :=
  chooseNormerStep F hF (insert (xs n) (state F hF xs n).1) (state F hF xs n).2

noncomputable def seq (n : ℕ) : StrongDual 𝕜 X := (stage F hF xs n).f

lemma state_succ (n : ℕ) :
    state F hF xs (n + 1) =
      (insert (xs n) ((state F hF xs n).1 ∪ (stage F hF xs n).D),
       insert (seq F hF xs n) (state F hF xs n).2) := rfl

lemma state_monotone : Monotone (fun n => (state F hF xs n).1) := by
  classical
  apply monotone_nat_of_le_succ
  intro n d hd
  rw [state_succ]
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hd)

lemma state_vectors (n : ℕ) :
    (state F hF xs n).2 = (Finset.range n).image (seq F hF xs) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih => simp only [state_succ, Finset.range_add_one, Finset.image_insert, ih]

lemma seq_norm (n : ℕ) : ‖seq F hF xs n‖ = 1 := (stage F hF xs n).norm_f

lemma seq_vanish_D {m n : ℕ} (hmn : m < n) {d : X}
    (hd : d ∈ (stage F hF xs m).D) : seq F hF xs n d = 0 := by
  classical
  apply (stage F hF xs n).vanish
  apply Finset.mem_insert_of_mem
  apply state_monotone F hF xs (Nat.succ_le_of_lt hmn)
  change d ∈ (state F hF xs (m + 1)).1
  rw [state_succ]
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hd)

lemma stage_norms_prefix (m : ℕ) (c : ℕ → 𝕜) :
    ∃ d ∈ (stage F hF xs m).D,
      ‖∑ i ∈ Finset.range (m + 1), c i • seq F hF xs i‖ ≤
        2 * ‖(∑ i ∈ Finset.range (m + 1), c i • seq F hF xs i) d‖ := by
  classical
  apply (stage F hF xs m).norming
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hs := state_vectors F hF xs (m + 1)
  rw [state_succ] at hs
  dsimp only at hs
  have : seq F hF xs i ∈ insert (seq F hF xs m) (state F hF xs m).2 := by
    rw [hs]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact (Finset.mem_insert.mp this).elim (fun h => Or.inl h) (fun h => Or.inr h)

end NormerStep

end SeparableQuotient

namespace SeparableQuotient
open Set Metric
open scoped Topology BigOperators
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
@[reducible] noncomputable local instance criterionDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance criterionDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

namespace NormerStep
variable (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F)
variable (xs : ℕ → X)

/-- The recursive choices satisfy exactly the prefix hypotheses. -/
noncomputable def prefixNormers : PrefixNormers (seq F hF xs) where
  D := fun n => match n with
    | 0 => {0}
    | m + 1 => (stage F hF xs m).D
  unit := by
    intro m d hd
    cases m with
    | zero => have he : d = 0 := Finset.mem_singleton.mp hd
              subst d; simp
    | succ m => exact (stage F hF xs m).unit d hd
  norming := by
    intro m hm c
    cases m with
    | zero => omega
    | succ m => exact stage_norms_prefix F hF xs m c
  vanish := by
    intro m n hmn d hd
    cases m with
    | zero => have he : d = 0 := Finset.mem_singleton.mp hd
              subst d; simp
    | succ m => exact seq_vanish_D F hF xs (Nat.lt_of_succ_le hmn) hd

end NormerStep

/-- The actual evaluation operator on a dual subspace. -/
noncomputable def subspaceEvaluation (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    X →L[𝕜] StrongDual 𝕜 F :=
  (ContinuousLinearMap.precomp 𝕜 F.subtypeL).comp (NormedSpace.inclusionInDoubleDual 𝕜 X)

@[simp] lemma subspaceEvaluation_apply (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (x : X) (f : F) : subspaceEvaluation F x f = (f : StrongDual 𝕜 X) x := rfl

@[reducible] noncomputable local instance criterionSubspaceDualNormedGroup
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedAddCommGroup (StrongDual 𝕜 F) := inferInstance
@[reducible] noncomputable local instance criterionSubspaceDualNormedSpace
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedSpace 𝕜 (StrongDual 𝕜 F) := inferInstance

end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.EvaluationCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology BigOperators
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
@[reducible] noncomputable local instance evaluationCriterionDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance evaluationCriterionDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

@[reducible] noncomputable local instance evaluationCriterionSubspaceDualNormedGroup
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedAddCommGroup (StrongDual 𝕜 F) := inferInstance
@[reducible] noncomputable local instance evaluationCriterionSubspaceDualNormedSpace
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedSpace 𝕜 (StrongDual 𝕜 F) := inferInstance

end SeparableQuotient

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
@[reducible] noncomputable local instance necessityDualGroup (E : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : NormedAddCommGroup (StrongDual 𝕜 E) :=
  inferInstance
@[reducible] noncomputable local instance necessityDualSpace (E : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : NormedSpace 𝕜 (StrongDual 𝕜 E) :=
  inferInstance

end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinateDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction
open scoped Classical
universe u

lemma absConvex_abs_le {V : Type u} [AddCommGroup V] [Module ℚ V]
    (L : V →ₗ[ℚ] ℝ) (r : ℝ) (hr : 0 ≤ r) : AbsConvex ℚ {x | |L x| ≤ r} := by
  constructor
  · intro a ha
    rintro _ ⟨x, hx, rfl⟩
    change |L (a • x)| ≤ r
    rw [L.map_smul, Rat.smul_def, abs_mul, ← Real.norm_eq_abs (a : ℝ), Rat.norm_cast_real]
    calc
      _ ≤ ‖a‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg a)
      _ ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hr
  · intro x hx y hy a b ha hb hab
    change |L (a • x + b • y)| ≤ r
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
    calc
      _ = |(a : ℝ) * L x + (b : ℝ) * L y| := by
        simp only [L.map_add, L.map_smul, Rat.smul_def]
      _ ≤ |(a : ℝ) * L x| + |(b : ℝ) * L y| := abs_add_le _ _
      _ = (a : ℝ) * |L x| + (b : ℝ) * |L y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha', abs_of_nonneg hb']
      _ ≤ (a : ℝ) * r + (b : ℝ) * r := add_le_add
        (mul_le_mul_of_nonneg_left hx ha') (mul_le_mul_of_nonneg_left hy hb')
      _ = r := by rw [← add_mul, hab', one_mul]

end SeparableQuotient.NormConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BoundedCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.OrderedCauchy
open Filter
open scoped Classical
universe u v
variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable {Z : Type v} [PseudoMetricSpace Z]

/-- Failure of the Cauchy condition on a linearly ordered directed set yields
successive separated pairs. This applies equally to countable ordinal prefixes
and to an uncountable limit; no countable cofinality is assumed. -/
lemma separated_pairs_of_not_cauchy (u : ι → Z) (hu : ¬ CauchySeq u) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ a b : ℕ → ι,
      (∀ i, a i < b i) ∧ (∀ i j, i < j → b i ≤ a j) ∧
      ∀ i, ε ≤ dist (u (b i)) (u (a i)) := by
  rw [Metric.cauchySeq_iff] at hu
  push Not at hu
  obtain ⟨ε, hε, hu⟩ := hu
  have hex : ∀ N : ι, ∃ a b : ι, N ≤ a ∧ a < b ∧ ε ≤ dist (u b) (u a) := by
    intro N
    obtain ⟨m, hm, n, hn, hmn⟩ := hu N
    by_cases h : m ≤ n
    · refine ⟨m, n, hm, lt_of_le_of_ne h ?_, ?_⟩
      · intro heq
        rw [heq, dist_self] at hmn
        exact (not_le_of_gt hε) hmn
      · simpa only [dist_comm] using hmn
    · exact ⟨n, m, hn, lt_of_not_ge h, hmn⟩
  choose a b hab hlt hdist using hex
  let p : ℕ → ι × ι := fun n => Nat.rec
    (a (Classical.arbitrary ι), b (Classical.arbitrary ι))
    (fun _ prev => (a prev.2, b prev.2)) n
  have hp0 : ∀ n, (p n).1 < (p n).2 := by
    intro n
    cases n with
    | zero => exact hlt _
    | succ n => exact hlt _
  have hp1 : ∀ n, (p n).2 ≤ (p (n+1)).1 := fun n => hab _
  have hp2 : Monotone (fun n => (p n).2) := monotone_nat_of_le_succ fun n =>
    (hp1 n).trans (hp0 (n+1)).le
  refine ⟨ε, hε, (fun n => (p n).1), (fun n => (p n).2), hp0, ?_, ?_⟩
  · intro i j hij
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (hp2 (by omega : i ≤ l)).trans (hp1 l)
  · intro n
    cases n <;> exact hdist _

end SeparableQuotient.OrderedCauchy

namespace SeparableQuotient.OrderedCauchy
open Filter
open scoped Classical Topology
universe u
variable {Z : Type u} [SeminormedAddCommGroup Z]

lemma norm_large_subsequence (v : ℕ → Z) (hv : ¬ Tendsto v atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ε ≤ ‖v (φ i)‖ := by
  rw [Metric.tendsto_atTop] at hv
  push Not at hv
  obtain ⟨ε, hε, hv⟩ := hv
  obtain ⟨φ, hφ, hlarge⟩ := Nat.exists_strictMono_subsequence (P := fun i => ε ≤ ‖v i‖) (by
    intro N
    obtain ⟨n, hn, hdist⟩ := hv (N+1)
    exact ⟨n, by omega, by simpa only [dist_zero_right] using hdist⟩)
  exact ⟨ε, hε, φ, hφ, hlarge⟩

end SeparableQuotient.OrderedCauchy

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.RealCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.RealCoefficients

def signChoice (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma abs_signChoice (x : ℝ) : |signChoice x| = 1 := by
  unfold signChoice
  split_ifs <;> norm_num

lemma signChoice_mul (x : ℝ) : signChoice x * x = |x| := by
  unfold signChoice
  split_ifs with h
  · simp only [one_mul, abs_of_nonneg h]
  · simp only [neg_one_mul, abs_of_neg (lt_of_not_ge h)]

end SeparableQuotient.RealCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology Classical
universe u

/-- A finite threshold selection procedure for quantitative overlap bounds. -/
lemma threshold_selection {Λ : Type u} (f : Λ → ℕ → ℝ) (M δ : ℝ)
    (hM : ∀ a n, |f a n| ≤ M) (N : ℕ)
    (hcap : ∀ (s : Finset Λ) (φ : ℕ → ℕ), StrictMono φ →
      (∀ a ∈ s, ∀ n, δ < |f a (φ n)|) → s.card ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ a, CauchySeq (fun n => f a (φ n)) ∨ ∀ᶠ n in atTop, |f a (φ n)| ≤ δ := by
  let Attain : ℕ → Prop := fun k => ∃ (s : Finset Λ) (φ : ℕ → ℕ),
    s.card = k ∧ StrictMono φ ∧ ∀ a ∈ s,
      CauchySeq (fun n => f a (φ n)) ∧ ∀ n, δ < |f a (φ n)|
  have hzero : Attain 0 := ⟨∅, id, by simp, strictMono_id, by simp⟩
  let k := Nat.findGreatest Attain N
  obtain ⟨s, φ, hcard, hφ, hs⟩ := Nat.findGreatest_spec (P := Attain) (Nat.zero_le N) hzero
  refine ⟨φ, hφ, fun a => ?_⟩
  by_cases has : a ∈ s
  · exact Or.inl (hs a has).1
  · by_contra! bad
    have hfreq : ∃ᶠ n in atTop, δ < |f a (φ n)| := by
      simpa only [not_le] using bad.2
    obtain ⟨ψ, hψ, hψδ⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨y, _, χ, hχ, htχ⟩ := isCompact_Icc.tendsto_subseq
      (s := Set.Icc (-M) M) (x := fun n => f a (φ (ψ n)))
      (fun n => abs_le.mp (hM a (φ (ψ n))))
    let η : ℕ → ℕ := φ ∘ ψ ∘ χ
    have hη : StrictMono η := hφ.comp (hψ.comp hχ)
    have hnew : Attain (k+1) := by
      refine ⟨insert a s, η, ?_, hη, ?_⟩
      · rw [Finset.card_insert_of_notMem has, hcard]
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ⟨htχ.cauchySeq, fun n => hψδ (χ n)⟩
        · exact ⟨(hs b hb).1.comp_tendsto ((hψ.comp hχ).tendsto_atTop),
            fun n => (hs b hb).2 (ψ (χ n))⟩
    have hbound : k+1 ≤ N := by
      obtain ⟨t, η, ht, hη, hh⟩ := hnew
      rw [← ht]
      exact hcap t η hη (fun b hb => (hh b hb).2)
    have := Nat.le_findGreatest (P := Attain) hbound hnew
    change k+1 ≤ k at this
    omega

end SeparableQuotient.PathSelection

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology Classical

/-- A genuinely nested sequence of subsequences, with the usual diagonal map. -/
structure Nested where
  seq : ℕ → ℕ → ℕ
  mono : ∀ k, StrictMono (seq k)
  nested : ∀ k, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ seq (k+1) = seq k ∘ ψ

def Nested.diag (A : Nested) : ℕ → ℕ := fun n => A.seq n n

lemma Nested.represent (A : Nested) {k n : ℕ} (hn : k ≤ n) (i : ℕ) :
    ∃ j ≥ i, A.seq n i = A.seq k j := by
  induction hn generalizing i with
  | refl => exact ⟨i, le_rfl, rfl⟩
  | @step n hn ih =>
    obtain ⟨ψ, hψ, he⟩ := A.nested n
    obtain ⟨j, hj, hij⟩ := ih (ψ i)
    exact ⟨j, (hψ.id_le i).trans hj, by simpa only [he, Function.comp_apply] using hij⟩

lemma Nested.diag_strictMono (A : Nested) : StrictMono A.diag := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨ψ, hψ, he⟩ := A.nested n
  change A.seq n n < A.seq (n+1) (n+1)
  rw [he, Function.comp_apply]
  exact (A.mono n) ((Nat.lt_succ_self n).trans_le (hψ.id_le (n+1)))

lemma Nested.eventually_diag (A : Nested) {P : ℕ → Prop} (k : ℕ)
    (h : ∀ᶠ i in atTop, P (A.seq k i)) : ∀ᶠ n in atTop, P (A.diag n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (max k N)] with n hn
  obtain ⟨j, hj, he⟩ := A.represent ((le_max_left k N).trans hn) n
  change P (A.seq n n)
  rw [he]
  exact hN j ((le_max_right k N).trans (hn.trans hj))

lemma Nested.cauchy_diag {X : Type*} [PseudoMetricSpace X] (A : Nested) (f : ℕ → X)
    (k : ℕ) (h : CauchySeq (f ∘ A.seq k)) : CauchySeq (f ∘ A.diag) := by
  rw [Metric.cauchySeq_iff] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨max k N, fun m hm n hn => ?_⟩
  obtain ⟨i, hi, he⟩ := A.represent ((le_max_left k N).trans hm) m
  obtain ⟨j, hj, hf⟩ := A.represent ((le_max_left k N).trans hn) n
  change dist (f (A.seq m m)) (f (A.seq n n)) < ε
  rw [he, hf]
  exact hN i ((le_max_right k N).trans (hm.trans hi)) j ((le_max_right k N).trans (hn.trans hj))

end SeparableQuotient.PathSelection

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology Classical
universe u

/-- Simultaneous convergence on an arbitrary, possibly uncountable, path family.
Only finite quantitative overlap bounds are required. -/
lemma simultaneous_cauchy {Λ : Type u} (f : Λ → ℕ → ℝ) (M : ℝ)
    (hM : ∀ a n, |f a n| ≤ M)
    (hcap : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ (s : Finset Λ) (φ : ℕ → ℕ), StrictMono φ →
        (∀ a ∈ s, ∀ n, δ < |f a (φ n)|) → s.card ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a, CauchySeq (fun n => f a (φ n)) := by
  let δ : ℕ → ℝ := fun n => 1/((n+1 : ℕ) : ℝ)
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  let Subseq := {φ : ℕ → ℕ // StrictMono φ}
  have hex : ∀ n (u : Subseq), ∃ v : Subseq,
      (∀ a, CauchySeq (fun i => f a (v.val i)) ∨
        ∀ᶠ i in atTop, |f a (v.val i)| ≤ δ n) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ v.val = u.val ∘ ψ := by
    intro n u
    obtain ⟨N, hN⟩ := hcap (δ n) (hδ n)
    obtain ⟨ψ, hψ, hgood⟩ := threshold_selection (fun a i => f a (u.val i)) M (δ n)
      (fun a i => hM a (u.val i)) N
      (fun s φ hφ hh => hN s (u.val ∘ φ) (u.property.comp hφ) hh)
    exact ⟨⟨u.val ∘ ψ, u.property.comp hψ⟩, hgood, ψ, hψ, rfl⟩
  choose next hnext using hex
  let U : ℕ → Subseq := Nat.rec ⟨id, strictMono_id⟩ (fun n u => next n u)
  let A : Nested := {
    seq := fun n => (U n).val
    mono := fun n => (U n).property
    nested := fun n => (hnext n (U n)).2 }
  refine ⟨A.diag, A.diag_strictMono, fun a => ?_⟩
  by_cases hex : ∃ k, CauchySeq (fun n => f a (A.seq k n))
  · obtain ⟨k, hk⟩ := hex
    exact A.cauchy_diag (f a) k hk
  · have hsmall (k : ℕ) : ∀ᶠ n in atTop, |f a (A.diag n)| ≤ δ k := by
      apply A.eventually_diag (P := fun i => |f a i| ≤ δ k) (k+1)
      exact ((hnext k (U k)).1 a).resolve_left (fun h => hex ⟨k+1, h⟩)
    have ht : Tendsto (fun n => f a (A.diag n)) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hδ0 : Tendsto δ atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
      obtain ⟨k, hk⟩ := (hδ0.eventually (gt_mem_nhds hε)).exists
      filter_upwards [hsmall k] with n hn
      simpa only [Real.dist_eq, sub_zero] using hn.trans_lt hk
    exact ht.cauchySeq

end SeparableQuotient.PathSelection

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology

lemma power_cap (r M δ : ℝ) (hr : r < 1) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, δ * n ≤ M * (n : ℝ)^r → n ≤ N := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(1-r)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1-r)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop (M/δ)))
  refine ⟨N, fun n hn => ?_⟩
  by_contra hbad
  have hnN : N < n := Nat.lt_of_not_ge hbad
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < (n : ℝ)^r := Real.rpow_pos_of_pos hn0 _
  have hm : M < δ * (n : ℝ)^(1-r) := (div_lt_iff₀ hδ).mp (hN n hnN.le)
    |>.trans_eq (mul_comm _ _)
  have he : (n : ℝ)^r * (n : ℝ)^(1-r) = n := by
    rw [← Real.rpow_add hn0, add_sub_cancel, Real.rpow_one]
  have := mul_lt_mul_of_pos_left hm hp
  rw [mul_left_comm, he] at this
  nlinarith

end SeparableQuotient.PathSelection

namespace SeparableQuotient.DenseZero
open Filter
open scoped Topology
universe u
variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma tendsto_zero_of_dense (g : ℕ → StrongDual ℝ Z) (M : ℝ)
    (hM : ∀ n, ‖g n‖ ≤ M) (D : Set Z) (hD : Dense D)
    (h : ∀ z ∈ D, Tendsto (fun n => g n z) atTop (𝓝 0)) (z : Z) :
    Tendsto (fun n => g n z) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp (hD z) (ε/(2*(M+1))) (by positivity)
  have he := (Metric.tendsto_nhds.mp (h w hw) (ε/2) (by linarith))
  filter_upwards [he] with n hn
  have hdist : dist (g n z) (g n w) ≤ M * dist z w := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((g n).le_opNorm (z-w)).trans
      (mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _))
  have hsmall : M * dist z w < ε/2 := by
    have hd : dist z w < ε/(2*(M+1)) := by simpa only [dist_comm] using hzw
    have hdm : (M+1) * dist z w < ε/2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hd
      nlinarith
    have hle : M * dist z w ≤ (M+1) * dist z w :=
      mul_le_mul_of_nonneg_right (by linarith) (dist_nonneg : 0 ≤ dist z w)
    exact hle.trans_lt hdm
  exact (dist_triangle (g n z) (g n w) 0).trans_lt (by linarith)

end SeparableQuotient.DenseZero

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathStabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.DiscreteDiagonal
open Filter
open scoped Topology Classical

/-- Countably many yes/no tests can be made eventually constant by one
subsequence. The index set is arbitrary countable, not just natural numbers. -/
lemma exists_stabilizing_subsequence {ι : Type*} [Countable ι] (p : ℕ → ι → Prop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ b : Prop,
      ∀ᶠ n in atTop, p (φ n) i ↔ b := by
  let x : ℕ → ι → Bool := fun n i => decide (p n i)
  obtain ⟨y, _, φ, hφ, hy⟩ := isCompact_univ.tendsto_subseq
    (x := x) (fun _ => Set.mem_univ _)
  refine ⟨φ, hφ, fun i => ⟨y i = true, ?_⟩⟩
  have ht := (tendsto_pi_nhds.mp hy) i
  have he : ∀ᶠ n in atTop, x (φ n) i = y i :=
    (by simpa only [nhds_discrete, tendsto_pure, Function.comp_apply] using ht)
  filter_upwards [he] with n hn
  change decide (p (φ n) i) = y i at hn
  rw [← hn, decide_eq_true_eq]

end SeparableQuotient.DiscreteDiagonal

namespace SeparableQuotient.IncreasingLists
open Filter
open scoped Classical

/-- Pointwise stabilization of membership in increasing finite lists, with an
infinite limiting set, stabilizes every list position. -/
lemma positions_stabilize (len : ℕ → ℕ) (v : ℕ → ℕ → ℕ)
    (hv : ∀ n, StrictMono (fun i : Fin (len n) => v n i)) (W : Set ℕ)
    (hW : W.Infinite)
    (hmem : ∀ w, ∀ᶠ n in atTop, (∃ i < len n, v n i = w) ↔ w ∈ W) :
    ∀ i, ∀ᶠ n in atTop, i < len n ∧ v n i = Nat.nth (· ∈ W) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    let w := Nat.nth (· ∈ W) i
    have hwi : w ∈ W := Nat.nth_mem_of_infinite hW i
    have hsmall : ∀ᶠ n in atTop, ∀ u ≤ w,
        (∃ k < len n, v n k = u) ↔ u ∈ W := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (eventually_all_finset (I := Finset.range (w+1))).mpr (fun u _ => hmem u)
    have hprev : ∀ᶠ n in atTop, ∀ j < i,
        j < len n ∧ v n j = Nat.nth (· ∈ W) j := by
      simpa only [Finset.mem_range] using
        (eventually_all_finset (I := Finset.range i)).mpr (fun j hj => ih j (Finset.mem_range.mp hj))
    filter_upwards [hsmall, hprev] with n hn hp
    obtain ⟨k, hk, hkw⟩ := (hn w le_rfl).mpr hwi
    have hki : k = i := by
      rcases lt_trichotomy k i with h | h | h
      · have he := (hp k h).2.symm.trans hkw
        exact ((Nat.nth_injective hW he).not_lt h).elim
      · exact h
      · have hi : i < len n := h.trans hk
        have hiv : v n i < w := (hv n (show (⟨i, hi⟩ : Fin (len n)) < ⟨k, hk⟩ from h)).trans_eq hkw
        have hiW : v n i ∈ W := (hn (v n i) hiv.le).mp ⟨i, hi, rfl⟩
        obtain ⟨j, hj⟩ := Nat.subset_range_nth hiW
        have hji : j < i := (Nat.nth_lt_nth hW).mp (hj ▸ hiv)
        have hvi : v n j = v n i := (hp j hji).2.trans hj
        exact ((hv n (show (⟨j, (hp j hji).1⟩ : Fin (len n)) < ⟨i, hi⟩ from hji)).ne hvi).elim
    subst k
    exact ⟨hk, hkw⟩

/-- Bounded windows of arbitrarily high eventual hits force the limiting
membership set to be infinite. The upper window endpoints are essential. -/
lemma infinite_of_windows (len : ℕ → ℕ) (v : ℕ → ℕ → ℕ) (W : Set ℕ)
    (hmem : ∀ w, ∀ᶠ n in atTop, (∃ i < len n, v n i = w) ↔ w ∈ W)
    (hwin : ∀ B, ∃ T, ∀ᶠ n in atTop, ∃ i < len n, B < v n i ∧ v n i ≤ T) :
    W.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨T, hT⟩ := hwin B
  have hsmall : ∀ᶠ n in atTop, ∀ u ≤ T,
      (∃ k < len n, v n k = u) ↔ u ∈ W := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      (eventually_all_finset (I := Finset.range (T+1))).mpr (fun u _ => hmem u)
  obtain ⟨n, hn, i, hi, hBi, hiT⟩ := (hsmall.and hT).exists
  exact ⟨v n i, (hn (v n i) hiT).mp ⟨i, hi, rfl⟩, hBi⟩

end SeparableQuotient.IncreasingLists

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.RamseyThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.InfiniteRamsey
open Filter
open scoped Classical

variable {χ : Type*} [Finite χ]

lemma eventually_constant (U : Ultrafilter ℕ) (f : ℕ → χ) :
    ∃ b, ∀ᶠ m in U, f m = b :=
  U.eventually_exists_iff.mp (Eventually.of_forall (fun m => ⟨f m, rfl⟩))

def limitColor (U : Ultrafilter ℕ) (c : Finset ℕ → χ) : ℕ → Finset ℕ → χ
  | 0, s => c s
  | k+1, s => (eventually_constant U (fun m => limitColor U c k (insert m s))).choose

lemma limitColor_eventually (U : Ultrafilter ℕ) (c : Finset ℕ → χ)
    (k : ℕ) (s : Finset ℕ) :
    ∀ᶠ m in U, limitColor U c k (insert m s) = limitColor U c (k+1) s :=
  (eventually_constant U (fun m => limitColor U c k (insert m s))).choose_spec

/-- The finite-set form of the infinite Ramsey theorem, proved by iterated
ultrafilter colors. Used only for the four-hit thinning in exact-pairs. -/
theorem homogeneous (n : ℕ) (c : Finset ℕ → χ) :
    ∃ (M : Set ℕ) (b : χ), M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let b := limitColor U c n ∅
  let Good : Finset ℕ → Prop := fun S => ∀ s ⊆ S, s.card ≤ n → limitColor U c (n-s.card) s = b
  have hempty : Good ∅ := by
    intro s hs _
    have he : s = ∅ := Finset.subset_empty.mp hs
    subst s
    rfl
  have hstep (S : Finset ℕ) (hS : Good S) : ∃ m > S.sup id, Good (insert m S) := by
    have hev (s : Finset ℕ) (hs : s ⊆ S) : ∀ᶠ m in U,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b := by
      by_cases hlt : s.card < n
      · have he : n-s.card-1+1 = n-s.card := by omega
        exact (limitColor_eventually U c (n-s.card-1) s).mono
          (fun _ h _ => h.trans (by rw [he]; exact hS s hs hlt.le))
      · exact Eventually.of_forall (fun _ h => (hlt h).elim)
    have hall : ∀ᶠ m in U, ∀ s ∈ S.powerset,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b :=
      (eventually_all_finset S.powerset).mpr (fun s hs => hev s (Finset.mem_powerset.mp hs))
    have hlarge : ∀ᶠ m in U, S.sup id < m :=
      (eventually_gt_atTop (S.sup id)).filter_mono (Ultrafilter.of_le atTop)
    obtain ⟨m, hm, hall⟩ := (hlarge.and hall).exists
    have hmS : m ∉ S := by
      intro h
      exact (not_le_of_gt hm) (Finset.le_sup (f := id) h)
    refine ⟨m, hm, fun s hs hcard => ?_⟩
    by_cases hms : m ∈ s
    · let t := s.erase m
      have hts : t ⊆ S := by
        intro a ha
        have hh := Finset.mem_of_subset hs (Finset.mem_of_mem_erase ha)
        exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase ha)
      have htc : t.card+1 = s.card := by
        exact Finset.card_erase_add_one hms
      have he : insert m t = s := Finset.insert_erase hms
      have hh := hall t (Finset.mem_powerset.mpr hts) (by omega)
      simpa only [he, show n-t.card-1 = n-s.card by omega] using hh
    · have hss : s ⊆ S := by
        intro a ha
        exact (Finset.mem_insert.mp (hs ha)).resolve_left (fun h => hms (h ▸ ha))
      exact hS s hss hcard
  let next (S : {S : Finset ℕ // Good S}) : ℕ := (hstep S.val S.property).choose
  have hn (S : {S : Finset ℕ // Good S}) : S.val.sup id < next S ∧ Good (insert (next S) S.val) :=
    (hstep S.val S.property).choose_spec
  let seq : ℕ → {S : Finset ℕ // Good S} := Nat.rec ⟨∅, hempty⟩
    (fun _ S => ⟨insert (next S) S.val, (hn S).2⟩)
  have hseq (i : ℕ) : (seq (i+1)).val = insert (next (seq i)) (seq i).val := rfl
  have hmono : Monotone (fun i => (seq i).val) := monotone_nat_of_le_succ
    (fun i => by rw [hseq]; exact Finset.subset_insert _ _)
  let v : ℕ → ℕ := fun i => next (seq i)
  have hvmem (i : ℕ) : v i ∈ (seq (i+1)).val := by rw [hseq]; exact Finset.mem_insert_self _ _
  have hv : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact (Finset.le_sup (f := id) (hvmem i)).trans_lt (hn (seq (i+1))).1
  let M : Set ℕ := ⋃ i, ↑(seq i).val
  have hM : M.Infinite := (Set.infinite_range_of_injective hv.injective).mono (by
    rintro _ ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i+1, hvmem i⟩)
  refine ⟨M, b, hM, fun s hs hcard => ?_⟩
  have hex : ∀ a : s, ∃ i, a.val ∈ (seq i).val :=
    fun a => Set.mem_iUnion.mp (hs a.property)
  choose k hk using hex
  let N := Finset.univ.sup k
  have hsub : s ⊆ (seq N).val := by
    intro a ha
    exact hmono (Finset.le_sup (f := k) (Finset.mem_univ ⟨a, ha⟩)) (hk ⟨a, ha⟩)
  have hh := (seq N).property s hsub hcard.le
  simpa only [hcard, Nat.sub_self, limitColor] using hh

end SeparableQuotient.InfiniteRamsey

namespace SeparableQuotient.ActualSpace
open NormConstruction Filter
open scoped Classical Topology

lemma four_distinct_finset (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ({a,b,c,d} : Finset ℕ).card = 4 := by
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt had, ne_of_lt hbc, ne_of_lt hbd, ne_of_lt hcd]

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BlockEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.RecordGrowth
open Filter
open scoped Topology

/-- The logarithmic parameter limit implies unboundedness above every smaller power. -/
lemma div_rpow_tendsto_atTop {a b : ℕ → ℝ} {p e : ℝ}
    (ha : ∀ n, 1 < a n) (hb : ∀ n, 0 < b n)
    (hA : Tendsto a atTop atTop)
    (hlog : Tendsto (fun n => Real.log (b n) / Real.log (a n)) atTop (𝓝 p))
    (he : e < p) : Tendsto (fun n => b n / (a n)^e) atTop atTop := by
  let δ := (p-e)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hep : e+δ < p := by dsimp [δ]; linarith
  have hev := hlog.eventually (eventually_gt_nhds hep)
  refine tendsto_atTop_mono' atTop (f₁ := fun n => (a n)^δ) ?_
    ((tendsto_rpow_atTop hδ).comp hA)
  filter_upwards [hev] with n hn
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith [ha n]) e)).mpr
  rw [← Real.rpow_add (by linarith [ha n])]
  apply (Real.rpow_le_iff_le_log (by linarith [ha n]) (hb n)).mpr
  have := (lt_div_iff₀ (Real.log_pos (ha n))).mp hn
  nlinarith

/-- A record ratio over a finite initial segment, with a prescribed large
value of a(k), precisely as in the partition-block argument. -/
lemma exists_record (a : ℕ → ℝ) (e M : ℝ) (he : 0 ≤ e) (hM : 0 ≤ M)
    (hunbounded : ∀ R : ℝ, ∃ k : ℕ, 1 ≤ k ∧ R < a k / (k : ℝ)^e) :
    ∃ k : ℕ, 1 ≤ k ∧ M ≤ a k ∧
      ∀ l : ℕ, 1 ≤ l → l ≤ k → a l ≤ a k * ((l : ℝ)/(k : ℝ))^e := by
  obtain ⟨n, hn, hAn⟩ := hunbounded M
  obtain ⟨k, hk, hmax⟩ := (Finset.Icc 1 n).exists_max_image
    (fun l => a l / (l : ℝ)^e) ⟨n, Finset.mem_Icc.mpr ⟨hn, le_rfl⟩⟩
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hpow : 1 ≤ (k : ℝ)^e := Real.one_le_rpow (by exact_mod_cast hk1) he
  have hAk : M < a k / (k : ℝ)^e :=
    hAn.trans_le (hmax n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))
  have hMk : M ≤ a k := by
    have hmul := (lt_div_iff₀ (Real.rpow_pos_of_pos hk0 e)).mp hAk
    exact (le_mul_of_one_le_right hM hpow).trans hmul.le
  refine ⟨k, hk1, hMk, ?_⟩
  intro l hl hlk
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hrat := hmax l (Finset.mem_Icc.mpr ⟨hl, hlk.trans hkn⟩)
  rw [Real.div_rpow hl0.le hk0.le]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hl0 e)).mp hrat |>.trans_eq
  ring

/-- A slightly smaller reciprocal exponent can be chosen uniformly for all
of the finitely many partition sizes under consideration. -/
lemma choose_exponent (s N : ℝ) (hs : 1 < s) (hN : 1 ≤ N) :
    ∃ e : ℝ, 0 < e ∧ e < 1/s ∧
      ∀ d : ℝ, 1 ≤ d → d ≤ N → d^(1-e) ≤ 2*d^(1-1/s) := by
  let δ := min (1/(2*s)) (Real.log 2 / (Real.log N+1))
  have hs0 : 0 < s := by linarith
  have hln : 0 ≤ Real.log N := Real.log_nonneg hN
  have hδ : 0 < δ := lt_min (by positivity) (by positivity [Real.log_pos (by norm_num : (1:ℝ)<2)])
  have hδs : δ ≤ 1/(2*s) := min_le_left _ _
  have hδN : δ ≤ Real.log 2 / (Real.log N+1) := min_le_right _ _
  have hs2 : 1/(2*s) = (1/s)/2 := by ring
  have hinv : 0 < 1/s := one_div_pos.mpr hs0
  refine ⟨1/s-δ, by linarith, by linarith, ?_⟩
  intro d hd hdN
  have hd0 : 0 < d := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hdδ : d^δ ≤ 2 := by
    apply (Real.rpow_le_iff_le_log hd0 (by norm_num)).mpr
    have hm := (le_div_iff₀ (by linarith : 0 < Real.log N+1)).mp hδN
    have hmn := mul_le_mul_of_nonneg_left (Real.log_le_log hd0 hdN) hδ.le
    nlinarith
  calc
    d^(1-(1/s-δ)) = d^δ * d^(1-1/s) := by
      rw [← Real.rpow_add hd0]; congr 1; ring
    _ ≤ 2*d^(1-1/s) := mul_le_mul_of_nonneg_right hdδ (Real.rpow_nonneg hd0.le _)

/-- The finite concave power bound (Hölder) in the unit-block partition proof. -/
lemma sum_rpow_le_card {ι : Type*} [Fintype ι] (w : ι → ℝ) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1) :
    ∑ i, (w i)^e ≤ (Fintype.card ι : ℝ)^(1-e) := by
  have hpq : Real.HolderConjugate (1/e) (1/(1-e)) := {
    inv_add_inv_eq_inv := by simp
    left_pos := by positivity
    right_pos := by positivity }
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := fun i => (w i)^e)
    (g := fun _ => (1 : ℝ)) hpq (fun i _ => Real.rpow_nonneg (hw i) e) (fun _ _ => zero_le_one)
  have hpow (i : ι) : ((w i)^e)^(1/e) = w i := by
    rw [← Real.rpow_mul (hw i), mul_one_div_cancel he.ne', Real.rpow_one]
  simp only [mul_one, hpow, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, one_div_one_div] at hh
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hle : (∑ i, w i)^e ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hs0 hs he.le
  exact hh.trans ((mul_le_mul_of_nonneg_right hle
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq (one_mul _))

end SeparableQuotient.RecordGrowth

namespace SeparableQuotient.IntervalIncidence
open scoped Classical

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Only the first and last members of a successive finite family can partly
intersect one order-convex interval. -/
lemma partial_intersections_le_two (s : Finset α) (F : α → Finset β)
    (hF : ∀ i j, i < j → ∀ a ∈ F i, ∀ b ∈ F j, a < b)
    (I : Set β) (hI : Set.OrdConnected I) :
    (s.filter (fun i => (∃ a ∈ F i, a ∈ I) ∧ ¬ (↑(F i) : Set β) ⊆ I)).card ≤ 2 := by
  let t := s.filter (fun i => (∃ a ∈ F i, a ∈ I) ∧ ¬ (↑(F i) : Set β) ⊆ I)
  change t.card ≤ 2
  by_cases ht : t.Nonempty
  · have hsub : t ⊆ {t.min' ht, t.max' ht} := by
      intro i hi
      by_cases hmin : i = t.min' ht
      · simp [hmin]
      by_cases hmax : i = t.max' ht
      · simp [hmax]
      have h1 : t.min' ht < i := lt_of_le_of_ne (t.min'_le i hi) (Ne.symm hmin)
      have h2 : i < t.max' ht := lt_of_le_of_ne (t.le_max' i hi) hmax
      obtain ⟨a, ha, haI⟩ := (Finset.mem_filter.mp (t.min'_mem ht)).2.1
      obtain ⟨b, hb, hbI⟩ := (Finset.mem_filter.mp (t.max'_mem ht)).2.1
      have hn := (Finset.mem_filter.mp hi).2.2
      exact (hn (fun c hc => hI.out haI hbI ⟨(hF _ _ h1 a ha c hc).le, (hF _ _ h2 c hc b hb).le⟩)).elim
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · simp [Finset.not_nonempty_iff_eq_empty.mp ht]

/-- A noncrossing incidence matrix has at most two multichild rows incident to each fixed child. -/
lemma noncrossing_multichild_column_le_two (s : Finset α) (t : Finset β) (R : α → β → Prop)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i < j → ∀ a ∈ t, ∀ b ∈ t, R i a → R j b → a ≤ b)
    (a : β) (ha : a ∈ t) :
    (s.filter (fun i => R i a ∧ 2 ≤ (t.filter (R i)).card)).card ≤ 2 := by
  let v := s.filter (fun i => R i a ∧ 2 ≤ (t.filter (R i)).card)
  change v.card ≤ 2
  by_cases hv : v.Nonempty
  · have hsub : v ⊆ {v.min' hv, v.max' hv} := by
      intro i hi
      by_cases hmin : i = v.min' hv
      · simp [hmin]
      by_cases hmax : i = v.max' hv
      · simp [hmax]
      have h1 : v.min' hv < i := lt_of_le_of_ne (v.min'_le i hi) (Ne.symm hmin)
      have h2 : i < v.max' hv := lt_of_le_of_ne (v.le_max' i hi) hmax
      have hi' := Finset.mem_filter.mp hi
      have hm := Finset.mem_filter.mp (v.min'_mem hv)
      have hx := Finset.mem_filter.mp (v.max'_mem hv)
      have hs : t.filter (R i) ⊆ {a} := by
        intro b hb
        have hb' := Finset.mem_filter.mp hb
        exact Finset.mem_singleton.mpr (le_antisymm
          (hR _ hi'.1 _ hx.1 h2 b hb'.1 a ha hb'.2 hx.2.1)
          (hR _ hm.1 _ hi'.1 h1 a ha b hb'.1 hm.2.1 hb'.2))
      have hc : (t.filter (R i)).card ≤ 1 := (Finset.card_le_card hs).trans (by simp)
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hv]

lemma noncrossing_boundary_incidence (s : Finset α) (t : Finset β) (R : α → β → Prop)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i < j → ∀ a ∈ t, ∀ b ∈ t, R i a → R j b → a ≤ b) :
    ∑ i ∈ s.filter (fun i => 2 ≤ (t.filter (R i)).card), (t.filter (R i)).card ≤ 2 * t.card := by
  calc
    _ = ∑ i ∈ s, ∑ a ∈ t, if R i a ∧ 2 ≤ (t.filter (R i)).card then 1 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 2 ≤ (t.filter (R i)).card
      · simp only [hi, ↓reduceIte, and_true]
        rw [Finset.card_filter]
      · simp only [hi, ↓reduceIte, and_false, Finset.sum_const_zero]
    _ = ∑ a ∈ t, (s.filter (fun i => R i a ∧ 2 ≤ (t.filter (R i)).card)).card := by
      rw [Finset.sum_comm]
      simp only [Finset.card_filter]
    _ ≤ ∑ a ∈ t, 2 := Finset.sum_le_sum (fun a ha => noncrossing_multichild_column_le_two s t R hR a ha)
    _ = _ := by simp; omega

end SeparableQuotient.IntervalIncidence

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.AdaptiveThinning
open scoped Classical

variable (R : ℕ → ℕ → Set ℕ → Prop)
variable (hR : ∀ n i (N : Set ℕ), N.Infinite → ∃ W ⊆ N, W.Infinite ∧ R n i W)

structure State (n : ℕ) where
  index : ℕ
  rest : Set ℕ
  infinite : rest.Infinite
  later : ∀ i ∈ rest, index < i
  good : R n index rest

end SeparableQuotient.AdaptiveThinning

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open NormConstruction Filter
open scoped Classical Topology

noncomputable def firstNonzero (s : Finset ℕ) (t : ℕ → ℝ) : ℕ :=
  if h : (s.filter (fun i => t i ≠ 0)).Nonempty then (s.filter (fun i => t i ≠ 0)).min' h else 0

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open NormConstruction Filter
open scoped Classical Topology

lemma geometric_charge_le (ε : ℝ) (hε : 0 ≤ ε) (i : ℕ) :
    (∑ n ∈ Finset.range i, ε*(1/2 : ℝ)^(n+1)) ≤ ε := by
  have he : ∀ i, (∑ n ∈ Finset.range i, ε*(1/2 : ℝ)^(n+1)) = ε*(1-(1/2 : ℝ)^i) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) i]

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.MarkedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u
variable {ι : Type u} [Fintype ι]

lemma sum_rpow_larger (v : ι → ℝ) (p r K : ℝ) (hp : 0 < p) (hpr : p ≤ r) (hK : 0 ≤ K)
    (hv : ∑ i, |v i|^p ≤ K^p) : ∑ i, |v i|^r ≤ K^r := by
  have hi (i : ι) : |v i| ≤ K := by
    apply (Real.rpow_le_rpow_iff (abs_nonneg _) hK hp).mp
    exact (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (v j)) p) (Finset.mem_univ i)).trans hv
  calc
    _ = ∑ i, |v i|^p * |v i|^(r-p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.rpow_add' (abs_nonneg _) (by linarith : p+(r-p) ≠ 0)]
      congr 1
      ring
    _ ≤ ∑ i, |v i|^p * K^(r-p) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hi i) (sub_nonneg.mpr hpr)) (Real.rpow_nonneg (abs_nonneg _) _))
    _ = (∑ i, |v i|^p) * K^(r-p) := (Finset.sum_mul ..).symm
    _ ≤ K^p * K^(r-p) := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hK _)
    _ = K^r := by
      rw [← Real.rpow_add' hK (by linarith : p+(r-p) ≠ 0)]
      congr 1
      ring

end SeparableQuotient.FiniteVectors

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.BinaryNodes

def child (n : ℕ) (b : Bool) : ℕ := 2*n+1+b.toNat

def ancestors : ℕ → List ℕ
  | 0 => [0]
  | n+1 => ancestors (n/2) ++ [n+1]
termination_by n => n

def branch (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => child (branch b n) (b n)

lemma child_pos (n : ℕ) (b : Bool) : 0 < child n b := by simp only [child]; omega
lemma lt_child (n : ℕ) (b : Bool) : n < child n b := by simp only [child]; omega
lemma child_parent (n : ℕ) (b : Bool) : (child n b-1)/2 = n := by
  cases b <;> simp only [child,Bool.toNat_false,Bool.toNat_true] <;> omega

lemma ancestors_child (n : ℕ) (b : Bool) : ancestors (child n b) = ancestors n ++ [child n b] := by
  have hpos := child_pos n b
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hk,ancestors]
  congr 2
  have hp := child_parent n b
  rw [hk] at hp
  omega

lemma ancestors_nonempty (n : ℕ) : ancestors n ≠ [] := by
  cases n with
  | zero => simp [ancestors]
  | succ n => simp [ancestors]

lemma ancestors_mem_le (n k : ℕ) (hk : k ∈ ancestors n) : k ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [ancestors] using hk
    | succ n =>
      simp only [ancestors,List.mem_append,List.mem_singleton] at hk
      rcases hk with hk | rfl
      · exact (ih (n/2) (by omega) hk).trans (by omega)
      · exact le_rfl

lemma ancestors_branch (b : ℕ → Bool) (n : ℕ) :
    ancestors (branch b n) = List.ofFn (fun i : Fin (n+1) => branch b i) := by
  induction n with
  | zero => simp [branch,ancestors]
  | succ n ih =>
    rw [branch,ancestors_child,ih]
    rw [List.ofFn_succ_last (f := fun i : Fin (n+2) => branch b i)]
    simp only [Fin.val_castSucc,Fin.val_last]
    rfl

lemma branch_strict (b : ℕ → Bool) : StrictMono (branch b) :=
  strictMono_nat_of_lt_succ (fun _n => lt_child _ _)

end SeparableQuotient.BinaryNodes

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.StrictSingularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set Metric
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A strictly singular operator is not bounded below on any closed infinite-dimensional subspace. -/
def StrictlySingular (T : Y →L[𝕜] Z) : Prop :=
  ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) → ¬ FiniteDimensional 𝕜 M →
    ∀ c : ℝ, 0 < c → ∃ x : M, ‖T x‖ < c*‖x‖

lemma finiteDimensional_of_ker [FiniteDimensional 𝕜 Z] (T : Y →ₗ[𝕜] Z)
    [FiniteDimensional 𝕜 T.ker] : FiniteDimensional 𝕜 Y := by
  have h : FiniteDimensional 𝕜 (Submodule.comap T (⊤ : Submodule 𝕜 Z)) := inferInstance
  rw [Submodule.comap_top] at h
  exact FiniteDimensional.of_injective (Submodule.topEquiv : (⊤ : Submodule 𝕜 Y) ≃ₗ[𝕜] Y).symm.toLinearMap
    (Submodule.topEquiv.symm.injective)

lemma exists_finite_vector_normers (F : Submodule 𝕜 Y) [FiniteDimensional 𝕜 F] :
    ∃ D : Finset (StrongDual 𝕜 Y), (∀ d ∈ D, ‖d‖ ≤ 1) ∧
      ∀ v : F, ∃ d ∈ D, ‖v‖ ≤ 2*‖d v‖ := by
  let U (d : closedBall (0 : StrongDual 𝕜 Y) 1) : Set F := {v | (1/2 : ℝ) < ‖d.1 v‖}
  have hU : ∀ d, IsOpen (U d) := fun d =>
    isOpen_lt continuous_const ((d.1.comp F.subtypeL).continuous.norm)
  have hc : sphere (0 : F) 1 ⊆ ⋃ d, U d := by
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    obtain ⟨d,hd,he⟩ := exists_dual_vector'' 𝕜 (v : Y)
    refine Set.mem_iUnion.mpr ⟨⟨d,by simpa only [mem_closedBall,dist_zero_right] using hd⟩,?_⟩
    change (1/2 : ℝ) < ‖d v‖
    rw [he,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    change (1/2 : ℝ) < ‖v‖
    rw [hn]; norm_num
  obtain ⟨t,ht⟩ := (isCompact_sphere (0 : F) 1).elim_finite_subcover U hU hc
  refine ⟨insert 0 (t.image Subtype.val),?_,?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hd
      simpa only [mem_closedBall,dist_zero_right] using d.property
  · intro v
    by_cases hv : v = 0
    · subst v; exact ⟨0,Finset.mem_insert_self _ _,by simp⟩
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : F := (↑‖v‖ : 𝕜)⁻¹ • v
    have hw : w ∈ sphere (0 : F) 1 := by
      simp only [w,mem_sphere,dist_zero_right,norm_smul,norm_inv,RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hp.ne']
    obtain ⟨d,hd,he⟩ := Set.mem_iUnion₂.mp (ht hw)
    refine ⟨d,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩),?_⟩
    change (1/2 : ℝ) < ‖d.1 ((↑‖v‖ : 𝕜)⁻¹ • (v : Y))‖ at he
    rw [map_smul,norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg v)] at he
    have hm := mul_lt_mul_of_pos_left he hp
    rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul] at hm
    linarith

lemma StrictlySingular.exists_unit_small (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) : ∃ x : M, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  obtain ⟨x,hx⟩ := hT M hM hI ε hε
  have hx0 : 0 < ‖x‖ := by
    by_contra hh
    have hz : ‖x‖ = 0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hz,mul_zero] at hx
    exact (not_lt_of_ge (norm_nonneg _)) hx
  refine ⟨(↑‖x‖ : 𝕜)⁻¹ • x,?_,?_⟩
  · simp only [norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hx0.ne']
  · change ‖T ((↑‖x‖ : 𝕜)⁻¹ • (x : Y))‖ < ε
    rw [map_smul,norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    exact (inv_mul_lt_iff₀ hx0).mpr (by nlinarith [hx])

end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

structure VectorNormers (u : ℕ → Y) where
  D : ℕ → Finset (StrongDual 𝕜 Y)
  unit : ∀ m, ∀ d ∈ D m, ‖d‖ ≤ 1
  norming : ∀ m, ∀ c : ℕ → 𝕜, ∃ d ∈ D m,
    ‖∑ i ∈ Finset.range m, c i • u i‖ ≤ 2 * ‖d (∑ i ∈ Finset.range m, c i • u i)‖
  vanish : ∀ m n, m ≤ n → ∀ d ∈ D m, d (u n) = 0

namespace VectorNormers
variable {u : ℕ → Y} (H : VectorNormers (𝕜 := 𝕜) u)
lemma prefix_eval (c : ℕ → 𝕜) {m N : ℕ} (hm : m ≤ N) {d : StrongDual 𝕜 Y} (hd : d ∈ H.D m) :
    d (∑ i ∈ Finset.range N, c i • u i) = d (∑ i ∈ Finset.range m, c i • u i) := by
  simp only [map_sum,map_smul]
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i _ hi
  rw [H.vanish m i (by simpa using hi) d hd,smul_zero]

include H in
lemma prefix_bound (c : ℕ → 𝕜) {m N : ℕ} (hm : m ≤ N) :
    ‖∑ i ∈ Finset.range m, c i • u i‖ ≤ 2*‖∑ i ∈ Finset.range N, c i • u i‖ := by
  obtain ⟨d,hd,hb⟩ := H.norming m c
  rw [← H.prefix_eval c hm hd] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left ((d.le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (H.unit m d hd) (norm_nonneg _))) (by norm_num))

include H in
lemma coefficient_bound (hu : ∀ n, ‖u n‖ = 1) (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n‖ ≤ 4*‖∑ i ∈ Finset.range N, c i • u i‖ := by
  have hp := H.prefix_bound c (Nat.succ_le_of_lt hn)
  have hq := H.prefix_bound c hn.le
  have he : c n • u n = (∑ i ∈ Finset.range (n+1), c i • u i) - (∑ i ∈ Finset.range n, c i • u i) := by
    rw [Finset.sum_range_succ,add_sub_cancel_left]
  have hh := norm_sub_le (∑ i ∈ Finset.range (n+1), c i • u i) (∑ i ∈ Finset.range n, c i • u i)
  rw [← he,norm_smul,hu,mul_one] at hh
  linarith

lemma linearCombination_eq_range (c : ℕ →₀ 𝕜) {N : ℕ} (hN : c.support ⊆ Finset.range N) :
    Finsupp.linearCombination 𝕜 u c = ∑ i ∈ Finset.range N, c i • u i := by
  change (∑ i ∈ c.support, c i • u i) = _
  apply Finset.sum_subset hN
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi,zero_smul]

include H in
lemma finsupp_bound (hu : ∀ n, ‖u n‖ = 1) (c : ℕ →₀ 𝕜) (n : ℕ) :
    ‖c n‖ ≤ 4*‖Finsupp.linearCombination 𝕜 u c‖ := by
  obtain ⟨N,hN⟩ := (insert n c.support).exists_nat_subset_range
  rw [linearCombination_eq_range c (fun i hi => hN (Finset.mem_insert_of_mem hi))]
  exact H.coefficient_bound hu c (Finset.mem_range.mp (hN (Finset.mem_insert_self _ _)))

include H in
lemma linearIndependent (hu : ∀ n, ‖u n‖ = 1) : LinearIndependent 𝕜 u := by
  rw [linearIndependent_iff]
  intro c hc
  ext n
  have hb := H.finsupp_bound hu c n
  rw [hc,norm_zero,mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
end VectorNormers

namespace SmallRestriction

def listSpan (l : List Y) : Submodule 𝕜 Y := Submodule.span 𝕜 (l.toFinset : Set Y)
instance instFiniteDimensionalSubtypeMemSubmoduleListSpan (l : List Y) : FiniteDimensional 𝕜 (listSpan (𝕜 := 𝕜) l) := FiniteDimensional.span_finset 𝕜 _

def listNormers (l : List Y) : Finset (StrongDual 𝕜 Y) :=
  (exists_finite_vector_normers (listSpan (𝕜 := 𝕜) l)).choose
lemma listNormers_spec (l : List Y) : (∀ d ∈ listNormers (𝕜 := 𝕜) l, ‖d‖ ≤ 1) ∧
    ∀ x ∈ listSpan (𝕜 := 𝕜) l, ∃ d ∈ listNormers (𝕜 := 𝕜) l, ‖x‖ ≤ 2*‖d x‖ := by
  have hh := (exists_finite_vector_normers (listSpan (𝕜 := 𝕜) l)).choose_spec
  exact ⟨hh.1,fun x hx => hh.2 ⟨x,hx⟩⟩

structure State (𝕜 Y : Type*) [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  vectors : List Y
  normers : Finset (StrongDual 𝕜 Y)

end SmallRestriction
end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma VectorNormers.norm_small {u : ℕ → Y} (H : VectorNormers (𝕜 := 𝕜) u)
    (hu : ∀ n, ‖u n‖ = 1) (T : Y →L[𝕜] Z) (ε : ℝ) (hε : 0 ≤ ε)
    (hT : ∀ n, ‖T (u n)‖ ≤ ε*(1/2 : ℝ)^(n+3)) (c : ℕ →₀ 𝕜) :
    ‖T (Finsupp.linearCombination 𝕜 u c)‖ ≤ ε*‖Finsupp.linearCombination 𝕜 u c‖ := by
  let x := Finsupp.linearCombination 𝕜 u c
  have hc (n : ℕ) := H.finsupp_bound hu c n
  have hgeo : (∑ i ∈ c.support, (1/2 : ℝ)^i) ≤ 2 := by
    simpa only [tsum_geometric_two] using summable_geometric_two.sum_le_tsum c.support (fun i _ => by positivity)
  calc
    ‖T x‖ ≤ ∑ i ∈ c.support, ‖c i‖*‖T (u i)‖ := by
      change ‖T (∑ i ∈ c.support, c i • u i)‖ ≤ _
      rw [map_sum]
      simpa only [map_smul,norm_smul] using norm_sum_le c.support (fun i => T (c i • u i))
    _ ≤ ∑ i ∈ c.support, (4*‖x‖)*(ε*(1/2 : ℝ)^(i+3)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (hT i) (norm_nonneg _) (by positivity)
    _ = (4*‖x‖*ε*(1/2 : ℝ)^3)*(∑ i ∈ c.support, (1/2 : ℝ)^i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]; ring
    _ ≤ (4*‖x‖*ε*(1/2 : ℝ)^3)*2 := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = ε*‖x‖ := by ring

end SeparableQuotient.Singular

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
lemma top_infinite {𝕜 Y : Type*} [Field 𝕜] [AddCommGroup Y] [Module 𝕜 Y]
    (hI : ¬ FiniteDimensional 𝕜 Y) : ¬ FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 Y) := by
  intro hh
  let : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 Y) := hh
  let e : (⊤ : Submodule 𝕜 Y) ≃ₗ[𝕜] Y := Submodule.topEquiv
  exact hI (FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective)
end SeparableQuotient.Singular

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BlockApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set
lemma exists_unit {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (hI : ¬ FiniteDimensional 𝕜 Y) : ∃ x : Y, ‖x‖ = 1 := by
  let : Nontrivial Y := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let : Subsingleton Y := hs
    exact hI inferInstance)
  obtain ⟨x,hx⟩ := exists_ne (0 : Y)
  refine ⟨(↑‖x‖ : 𝕜)⁻¹ • x,?_⟩
  simp only [norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg x),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
end SeparableQuotient.Singular

namespace SeparableQuotient.ActualSpace
open Singular Set
open scoped Classical
namespace BlockApprox

def error (n : ℕ) : ℝ := (1/64000)*(1/2)^n
lemma error_pos (n : ℕ) : 0 < error n := by unfold error; positivity
lemma error_le (n : ℕ) : error n ≤ 1/2 := by
  have h : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold error
  nlinarith

end BlockApprox
end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PerturbationOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace

lemma cachedNormedT2 (Y : Type*) [NormedAddCommGroup Y] : T2Space Y := inferInstance
open NormConstruction Filter
open scoped Classical Topology

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

def tau (n : ℕ) : ℝ := (1/32)*(1/2)^n
lemma tau_pos (n : ℕ) : 0 < tau n := by unfold tau; positivity
lemma tau_hasSum : HasSum tau (1/16) := by
  have h := (hasSum_geometric_of_norm_lt_one (ξ := (1/2:ℝ)) (by norm_num)).mul_left (1/32:ℝ)
  norm_num at h
  exact h
lemma tau_summable : Summable tau := tau_hasSum.summable

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Complexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Complexification by real-linear maps from ℂ with the operator norm and real coordinates f(1), f(i). -/
namespace SeparableQuotient
open scoped Classical
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

def Complexify := ℂ →L[ℝ] X
namespace Complexify
def toCLM (f : Complexify X) : ℂ →L[ℝ] X := f
instance instCoeFunForallComplex : CoeFun (Complexify X) (fun _ => ℂ → X) := ⟨fun f => toCLM X f⟩

end Complexify
end SeparableQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ProductQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace Singular
open scoped Classical
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

@[reducible] local instance fsDualGroup (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    NormedAddCommGroup (StrongDual 𝕜 Z) := inferInstance
@[reducible] local instance fsDualSpace (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    NormedSpace 𝕜 (StrongDual 𝕜 Z) := inferInstance

end SeparableQuotient

end

end OAI
end


