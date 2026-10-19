-- Prove2me | Definitions.Def_OAIQWSQN002
-- name    : OAIQWSQN002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:59:20.804617+00:00
-- url     : https://prove2.me/theorems/711a33f3-f9ec-4b3f-8b4f-5ade2265f101
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN002
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   The block approximation chooses its blocks with the small-restriction lemma for strictly singular operators. The bundle does not prove it: it imports the published statement `OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction` of this split, which has its own proof.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It also imports the bundles `OAIQWSQN000`, `OAIQWSQN001` of this split.
--
--   Modules: `BlockApproximation`, `BoundedCompleteness`, `BranchReduction`, `CoordinatePredual`, `LpDuality`, `NormCompletion`, `NormingBounds`, `Parameters`, `PathConvergence`, `PathOperators`, `PathRigidity`, `PerturbationOperator`, `PrefixNormers`, `StrictSingularity`, `TreeBounds`, `WindowThinning`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib
import Theorems.Thm_OAI_SeparableQuotient_Singular_StrictlySingular_exists_small_restriction
import Definitions.Def_OAIQWSQN000
import Definitions.Def_OAIQWSQN001

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

namespace PrefixNormers

attribute [local instance] OAI.SeparableQuotient.prefixDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.prefixDualNormedSpace
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

include H

theorem coefficient_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n‖ ≤ (4 / a) * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  have hb := H.term_bound c hn
  rw [norm_smul] at hb
  have hmul := mul_le_mul_of_nonneg_left (hf n) (norm_nonneg (c n))
  have he : 4 * ‖∑ i ∈ Finset.range N, c i • f i‖ / a =
      (4 / a) * ‖∑ i ∈ Finset.range N, c i • f i‖ := by ring
  rw [← he]
  exact (le_div_iff₀ ha).mpr (hmul.trans hb)

theorem finsupp_coefficient_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (c : ℕ →₀ 𝕜) (n : ℕ) :
    ‖c n‖ ≤ (4 / a) * ‖Finsupp.linearCombination 𝕜 f c‖ := by
  classical
  obtain ⟨N, hN⟩ := (insert n c.support).exists_nat_subset_range
  have hsum : (∑ i ∈ Finset.range N, c i • f i) =
      Finsupp.linearCombination 𝕜 f c := by
    change (∑ i ∈ Finset.range N, c i • f i) = ∑ i ∈ c.support, c i • f i
    symm
    apply Finset.sum_subset (fun i hi => hN (Finset.mem_insert_of_mem hi))
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
  rw [← hsum]
  exact H.coefficient_bound a ha hf c (Finset.mem_range.mp (hN (Finset.mem_insert_self _ _)))

theorem linearIndependent (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    LinearIndependent 𝕜 f := by
  rw [linearIndependent_iff]
  intro c hc
  ext n
  have h := H.finsupp_coefficient_bound a ha hf c n
  rw [hc, norm_zero, mul_zero] at h
  simpa using norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Admissible parameters for the pure s = k + 2 families and mixed s = 2 family, with q = (s + 1) / s. Integer powers avoid rounding noninteger powers. -/
namespace SeparableQuotient.Parameters

open Filter Topology

lemma L_pos (s n : ℕ) : 0 < L s n := pow_pos (by omega) _

end SeparableQuotient.Parameters

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- The completion of c₀₀ under a bounded rational norming set. -/

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology ENNReal Classical
open Filter
universe u
variable {Γ : Type u} (K : NormingSet Γ)

variable (A : Set Γ) (hA : K.CropStable A)

lemma norm_projection_le : ‖K.projection A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖K.cropAmbient A hA x.val‖ ≤ 1 * ‖x.val‖
  rw [one_mul]
  exact lp.norm_le_of_forall_le (norm_nonneg x.val)
    (fun f => lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x.val
      (K.cropNormer A hA f))

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinatePredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

lemma coordinate_ext (x y : E) (h : ∀ a, coordinate a x = coordinate a y) : x = y :=
  norming.coordinate_ext h

lemma norm_projection_le (A : Crop) (x : E) : ‖projection A x‖ ≤ ‖x‖ :=
  ((norming.projection (A.set .mixed) (cropStable A)).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norming.norm_projection_le (A.set .mixed) (cropStable A)) (norm_nonneg x))

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

abbrev coordinate₀ (a : Γ) : X₀ := norming.predualCoordinate a

end SeparableQuotient.ActualSpace

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

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace4
lemma projection_colorsBelow_sum (n : ℕ) (x : E) :
    projection (Crop.colorsBelow n) x = ∑ k ∈ Finset.range n, projection (Crop.oneColor k) x := by
  apply coordinate_ext
  intro a
  simp only [coordinate_projection, Crop.colorsBelow_set, Set.mem_ofPred_eq, map_sum,
    Crop.oneColor_set, colorSet]
  simp [eq_comm]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace7
lemma coordinate_e (a b : Γ) : coordinate a (e b) = if a = b then 1 else 0 := by
  simp [coordinate, e, NormingSet.generator, Finsupp.single_apply, eq_comm]

end SeparableQuotient.ActualSpace

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

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

/-- Bounded blocks are null on the coordinate predual. This intermediate
property is stated separately so that the path argument works for any such
sequence, not just a chosen block representation. -/
def PredualNull (x : ℕ → E) : Prop :=
  ∀ y : X₀, Tendsto (fun n => y.val (x n)) atTop (𝓝 0)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace11
def BlockSequence.embed {f : Family} (x : BlockSequence f) (n : ℕ) : E :=
  norming.includeFinite (x.vector n)

lemma BlockSequence.coordinate_eventually_zero {f : Family} (x : BlockSequence f) (a : Γ) :
    ∀ᶠ n in atTop, coordinate a (x.embed n) = 0 := by
  by_cases hex : ∃ n, x.vector n a ≠ 0
  · obtain ⟨i, hi⟩ := hex
    filter_upwards [eventually_ge_atTop (i+1)] with n hn
    change norming.coordinate a (norming.includeFinite (x.vector n)) = 0
    rw [norming.coordinate_includeFinite]
    by_contra h
    exact (lt_irrefl a) (x.successive i n (by omega) a (Finsupp.mem_support_iff.mpr hi)
      a (Finsupp.mem_support_iff.mpr h)).1
  · push Not at hex
    apply Eventually.of_forall
    intro n
    exact (norming.coordinate_includeFinite a (x.vector n)).trans (hex n)

lemma pathFunctional_eq_of_raw {f : Family} {P Q : InfinitePath f} (h : P.raw = Q.raw) :
    pathFunctional P = pathFunctional Q := by
  ext x
  apply tendsto_nhds_unique (pathPartial_tendsto P x)
  apply (pathPartial_tendsto Q x).congr'
  apply Eventually.of_forall
  intro n
  simp only [pathPartial, ← norming.evaluateArray_eq_functional]
  congr 1
  change (∑ i : Fin (n+1), Q.raw.piece i) = ∑ i : Fin (n+1), P.raw.piece i
  rw [h]

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

def FinitePath.window {f : Family} (P : FinitePath f) (J T : ℕ) : Array :=
  ∑ i : Fin P.length, if J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T then P.raw.piece i else 0

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- A finite path with its original finite-stage children. -/
def LegalFinitePath (f : Family) := {P : FinitePath f // ∀ i j, (P.piece i).child j ∈ f.norming}

def WindowHit {f : Family} (P : LegalFinitePath f) (x : Γ →₀ ℝ) (J T : ℕ) (δ : ℝ) : Prop :=
  δ < |norming.evaluateArray (norming.includeFinite x) (P.val.window J T)|

end SeparableQuotient.ActualSpace

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

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Window blocks with partition estimates, pathwise nullity, and coherent support bounds. -/
structure WindowBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (a : ℕ) where
  blocks : BlockSequence f
  lower : ℕ → ℕ
  upper : ℕ → ℕ
  mem_tail : ∀ n, blocks.vector n ∈ z.tailSpan a
  lower_norm : ∀ n, 1 ≤ ‖blocks.embed n‖
  upper_norm : ∀ n, ‖blocks.embed n‖ ≤ 2
  prescribed : ∀ n, J < lower n
  order : ∀ n, lower n ≤ upper n
  separated : ∀ i j, i < j → upper i < lower j
  coherence : ∀ i j k, j < i → k < i → ∀ α ∈ (blocks.vector j).support,
    ∀ β ∈ (blocks.vector k).support, rho (min α β) (max α β) < lower i
  partition : ∀ n, PartitionBound (blocks.embed n) (f.L (lower n)) 16 f.r
  tail_small : ∀ n, vectorL1 (blocks.vector n) * tail (fun j => 1/(f.m j : ℝ)) (upper n+1) ≤ ε
  tail_vanish : Tendsto (fun n => vectorL1 (blocks.vector n) * tail (fun j => 1/(f.m j : ℝ)) (upper n+1)) atTop (𝓝 0)
  path_null : ∀ P : InfinitePath f, Tendsto (fun n => pathFunctional P (blocks.embed n)) atTop (𝓝 0)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Successively thinned windows. The threshold indexed by n is used strictly after n. -/
structure ThinnedWindows {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (a : ℕ)
    extends WindowBlocks z J ε a where
  threshold : ℕ → ℝ
  threshold_pos : ∀ n, 0 < threshold n
  threshold_charge_succ : ∀ n, (upper n+1 : ℝ) * threshold n = ε * (1/2 : ℝ)^(n+1)
  threshold_charge : ∀ n, (upper n : ℝ) * threshold n ≤ ε * (1/2 : ℝ)^(n+1)
  four_hits_after : ∀ n (S : Finset ℕ), (∀ i ∈ S, n < i) → S.card = 4 →
    ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S,
      WindowHit P (blocks.vector i) (lower i) (upper i) (threshold n)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

noncomputable def ThinnedWindows.evalVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (i : s) : ℝ :=
  if i ∈ I then |norming.evaluateArray (w.blocks.embed i) g| else 0

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def smallBudget (f : Family) (J d : ℕ) : ℝ :=
  (1552/7)*f.theta J+64*(1/8)^d
noncomputable def largeUnit (f : Family) (J : ℕ) (s : Finset ℕ) : ℝ :=
  16*(1+(Parameters.B f.s (J-1) : ℝ)+(s.card : ℝ)^(1-1/f.q))
noncomputable def largeBudget (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : ℝ :=
  largeUnit f J s*(1+(Parameters.B f.s (J-1) : ℝ))^d

structure DepthMajorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (d : ℕ) where
  small : s → ℝ
  large : s → ℝ
  small_nonneg : ∀ i, 0 ≤ small i
  large_nonneg : ∀ i, 0 ≤ large i
  small_support : ∀ i, i ∉ I → small i = 0
  large_support : ∀ i, i ∉ I → large i = 0
  majorizes : ∀ i, w.evalVector s I g i ≤ small i+large i
  norm_small : ‖vec f.exponent small‖ ≤ smallBudget f J d
  sum_large : (∑ i : s, large i) ≤ largeBudget f J s d

end SeparableQuotient.ActualSpace

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

/-- Finitely many exact annihilation conditions preserve infinite dimension. -/
lemma finite_annihilator (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y))
    (hI : ¬ FiniteDimensional 𝕜 M) (D : Finset (StrongDual 𝕜 Y)) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ x ∈ N, ∀ d ∈ D, d x = 0 := by
  let A : Y →L[𝕜] (D → 𝕜) := ContinuousLinearMap.pi (fun d => d.1)
  let N := M ⊓ A.ker
  refine ⟨N,inf_le_left,hM.inter A.isClosed_ker,?_,?_⟩
  · intro hn
    let : FiniteDimensional 𝕜 N := hn
    let B := A.comp M.subtypeL
    have hker : FiniteDimensional 𝕜 B.ker := by
      let L : B.ker →ₗ[𝕜] N := {
        toFun := fun x => ⟨x.1.1,⟨x.1.2,x.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      exact FiniteDimensional.of_injective L (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun y : N => (y : Y)) h)))
    exact hI (finiteDimensional_of_ker B.toLinearMap)
  · intro x hx d hd
    have he : A x = 0 := hx.2
    exact congrFun he ⟨d,hd⟩

end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

namespace SmallRestriction

variable (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
  (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
  (ε : ℝ) (hε : 0 < ε)

include hT hM hI hε in
lemma exists_next (s : State 𝕜 Y) : ∃ y : Y, y ∈ M ∧ ‖y‖ = 1 ∧
    ‖T y‖ < ε*(1/2 : ℝ)^(s.vectors.length+3) ∧ ∀ d ∈ s.normers, d y = 0 := by
  obtain ⟨N,hNM,hNc,hNi,hNd⟩ := finite_annihilator M hM hI s.normers
  obtain ⟨y,hy,hTy⟩ := StrictlySingular.exists_unit_small T hT N hNc hNi
    (ε*(1/2 : ℝ)^(s.vectors.length+3)) (by positivity)
  exact ⟨y,hNM y.property,hy,hTy,hNd y y.property⟩

def nextVector (s : State 𝕜 Y) : Y := (exists_next T hT M hM hI ε hε s).choose
lemma nextVector_spec (s : State 𝕜 Y) : nextVector T hT M hM hI ε hε s ∈ M ∧
    ‖nextVector T hT M hM hI ε hε s‖ = 1 ∧
    ‖T (nextVector T hT M hM hI ε hε s)‖ < ε*(1/2 : ℝ)^(s.vectors.length+3) ∧
    ∀ d ∈ s.normers, d (nextVector T hT M hM hI ε hε s) = 0 :=
  (exists_next T hT M hM hI ε hε s).choose_spec

def step (s : State 𝕜 Y) : State 𝕜 Y :=
  let l := s.vectors ++ [nextVector T hT M hM hI ε hε s]
  ⟨l,s.normers ∪ listNormers l⟩

def state : ℕ → State 𝕜 Y
  | 0 => ⟨[],listNormers []⟩
  | n+1 => step T hT M hM hI ε hε (state n)

def seq (n : ℕ) : Y := nextVector T hT M hM hI ε hε (state T hT M hM hI ε hε n)

local notation "s" => state T hT M hM hI ε hε
local notation "u" => seq T hT M hM hI ε hε
lemma vectors_state (n : ℕ) : (s n).vectors = List.ofFn (fun i : Fin n => u i) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change (s n).vectors ++ [u n] = _
    rw [ih,List.ofFn_succ_last (f := fun i : Fin (n+1) => u i)]
    rfl

lemma state_length (n : ℕ) : (s n).vectors.length = n := by rw [vectors_state,List.length_ofFn]
lemma seq_spec (n : ℕ) : u n ∈ M ∧ ‖u n‖ = 1 ∧ ‖T (u n)‖ < ε*(1/2 : ℝ)^(n+3) := by
  have hh := nextVector_spec T hT M hM hI ε hε (s n)
  rw [state_length] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

lemma normers_mono : Monotone (fun n => (s n).normers) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

lemma normers_unit (n : ℕ) : ∀ d ∈ (s n).normers, ‖d‖ ≤ 1 := by
  induction n with
  | zero => exact (listNormers_spec []).1
  | succ n ih =>
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact ih d hd
    · exact (listNormers_spec _).1 d hd

lemma listNormers_subset (n : ℕ) : listNormers (s n).vectors ⊆ (s n).normers := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact Finset.subset_union_right

def normers : VectorNormers (𝕜 := 𝕜) u where
  D := fun n => (s n).normers
  unit := normers_unit T hT M hM hI ε hε
  norming := by
    intro m c
    have hx : (∑ i ∈ Finset.range m, c i • u i) ∈ listSpan (𝕜 := 𝕜) (s m).vectors := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      apply Submodule.subset_span
      rw [Finset.mem_coe,List.mem_toFinset,vectors_state]
      exact List.mem_ofFn.mpr ⟨⟨i,Finset.mem_range.mp hi⟩,rfl⟩
    obtain ⟨d,hd,hb⟩ := (listNormers_spec (s m).vectors).2 _ hx
    exact ⟨d,listNormers_subset T hT M hM hI ε hε m hd,hb⟩
  vanish := by
    intro m n hmn d hd
    exact (nextVector_spec T hT M hM hI ε hε (s n)).2.2.2 d
      (normers_mono T hT M hM hI ε hε hmn hd)

end SmallRestriction
end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Finitely many strictly singular operators admit a common closed
infinite-dimensional small restriction, including the original ambient subspace. -/
theorem exists_small_restriction_finite (D : Finset (Y →L[𝕜] Z))
    (hD : ∀ T ∈ D, StrictlySingular T)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ T ∈ D, ∀ x ∈ N, ‖T x‖ ≤ ε*‖x‖ := by
  induction D using Finset.induction_on generalizing M with
  | empty => exact ⟨M,le_rfl,hM,hI,by simp⟩
  | @insert T D hTD ih =>
    obtain ⟨N,hNM,hNc,hNi,hNd⟩ := ih (fun S hS => hD S (Finset.mem_insert_of_mem hS)) M hM hI
    obtain ⟨N',hN'N,hN'c,hN'i,hN'T⟩ := StrictlySingular.exists_small_restriction T
      (hD T (Finset.mem_insert_self _ _)) N hNc hNi ε hε
    refine ⟨N',hN'N.trans hNM,hN'c,hN'i,?_⟩
    intro S hS x hx
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact hN'T x hx
    · exact hNd S hS x (hN'N hx)

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

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical Topology

lemma initialP_initialP {β γ : Cut} (h : β ≤ γ) (x : E) :
    initialP β (initialP γ x) = initialP β x := by
  apply norming.coordinate_ext
  intro a
  by_cases ha : (a : Cut) < β
  · simp [ha,lt_of_lt_of_le ha h]
  · simp [ha]

lemma initialP_colorP (γ : Cut) (k : ℕ) (x : E) :
    initialP γ (colorP k x) = colorP k (initialP γ x) := by
  apply norming.coordinate_ext
  intro a
  simp only [coordinate_initialP,coordinate_colorP]
  split_ifs <;> rfl

lemma colorP_colorP (k : ℕ) (x : E) : colorP k (colorP k x) = colorP k x := by
  apply norming.coordinate_ext
  intro a
  simp only [coordinate_colorP]
  split_ifs <;> rfl

def familyP (γ : Cut) : Family → E →L[ℝ] E
  | .pure k => (colorP k).comp (initialP γ)
  | .mixed => initialP γ

structure BranchReduction (F : Submodule ℝ E) where
  cut : Cut
  family : Family
  H : Submodule ℝ E
  closed : IsClosed (H : Set E)
  infinite : ¬ FiniteDimensional ℝ H
  noLast : ∀ a : Γ, (a : Cut) < cut → ∃ b : Γ, a < b ∧ (b : Cut) < cut
  earlier : ∀ β < cut, StrictlySingular ((initialP β).comp H.subtypeL)
  mixed : family = .mixed → ∀ k, StrictlySingular ((colorP k).comp H.subtypeL)
  U : H →L[ℝ] F
  lift : ∀ x : H, familyP cut family (U x) = x

end SeparableQuotient.ActualSpace

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

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical Topology

lemma familyP_initial (γ : Cut) (f : Family) (x : E) :
    initialP γ (familyP γ f x) = familyP γ f x := by
  cases f with
  | mixed => exact initialP_initialP le_rfl x
  | pure k =>
    change initialP γ (colorP k (initialP γ x)) = colorP k (initialP γ x)
    rw [initialP_colorP,initialP_initialP le_rfl]

lemma familyP_color (γ : Cut) (k : ℕ) (x : E) :
    colorP k (familyP γ (.pure k) x) = familyP γ (.pure k) x :=
  colorP_colorP k _

variable {F : Submodule ℝ E} (R : BranchReduction F)

lemma BranchReduction.initial_fixed (x : R.H) : initialP R.cut (x : E) = x := by
  simpa only [R.lift] using familyP_initial R.cut R.family (R.U x)

lemma BranchReduction.color_fixed (k : ℕ) (hk : R.family = .pure k) (x : R.H) :
    colorP k (x : E) = x := by
  have hl : familyP R.cut (.pure k) (R.U x) = x := by simpa only [hk] using R.lift x
  simpa only [hl] using familyP_color R.cut k (R.U x)

lemma BranchReduction.coordinate_zero_of_cut (x : R.H) (a : Γ) (ha : ¬ (a : Cut) < R.cut) :
    coordinate a (x : E) = 0 := by
  have h := congrArg (coordinate a) (R.initial_fixed x)
  simpa only [coordinate_initialP,ha,ite_false,eq_comm] using h

lemma BranchReduction.coordinate_zero_of_color (k : ℕ) (hk : R.family = .pure k)
    (x : R.H) (a : Γ) (ha : Colors.color a ≠ k) : coordinate a (x : E) = 0 := by
  have h := congrArg (coordinate a) (R.color_fixed k hk x)
  simpa only [coordinate_colorP,ha,ite_false,eq_comm] using h

lemma BranchReduction.cut_nonempty : ∃ a : Γ, (a : Cut) < R.cut := by
  obtain ⟨x,hx⟩ := Singular.exists_unit R.infinite
  have hn : (x : E) ≠ 0 := by
    intro hh
    have hh0 : ‖x‖ = 0 := by
      change ‖(x : E)‖ = 0
      rw [hh,norm_zero]
    linarith
  have he : ∃ a : Γ, coordinate a (x : E) ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn
    exact norming.coordinate_ext (fun a => (hh a).trans (map_zero _).symm)
  obtain ⟨a,ha⟩ := he
  exact ⟨a,by by_contra hh; exact ha (R.coordinate_zero_of_cut x a hh)⟩

lemma BranchReduction.beyond_finite (s : Finset Γ) (hs : ∀ a ∈ s, (a : Cut) < R.cut) :
    ∃ β : Γ, (β : Cut) < R.cut ∧ ∀ a ∈ s, a < β := by
  by_cases hn : s.Nonempty
  · obtain ⟨β,hβ,hβc⟩ := R.noLast (s.max' hn) (hs _ (s.max'_mem hn))
    exact ⟨β,hβc,fun a ha => (s.le_max' a ha).trans_lt hβ⟩
  · obtain ⟨a,ha⟩ := R.cut_nonempty
    exact ⟨a,ha,by simp only [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.notMem_empty,false_implies,implies_true]⟩

def blockCrop (γ : Cut) (f : Family) (β : Γ) (l : ℕ) : Crop where
  ordinal := initialSet γ ∩ Set.Ici β
  ordinal_convex := (initialSet_connected γ).inter Set.ordConnected_Ici
  colors := match f with | .pure k => {k} | .mixed => Set.Ici l
  colors_convex := by cases f <;> first | exact Set.ordConnected_singleton | exact Set.ordConnected_Ici

lemma blockCrop_mem (γ : Cut) (f : Family) (β a : Γ) (l : ℕ) :
    a ∈ (blockCrop γ f β l).set .mixed ↔ (a : Cut) < γ ∧ β ≤ a ∧
      (match f with | .pure k => Colors.color a = k | .mixed => l ≤ Colors.color a) := by
  cases f <;> simp only [blockCrop,Crop.set,Set.mem_inter_iff,initialSet,Set.mem_ofPred_eq,
    Set.mem_Ici,Set.mem_preimage,Set.mem_singleton_iff,and_assoc]

lemma BranchReduction.crop_difference_pure (k : ℕ) (hk : R.family = .pure k)
    (β : Γ) (l : ℕ) (x : R.H) :
    (x : E)-projection (blockCrop R.cut R.family β l) x = initialP (β : Cut) x := by
  apply norming.coordinate_ext
  intro a
  by_cases hg : (a : Cut) < R.cut
  · by_cases hb : β ≤ a
    · by_cases hc : Colors.color a = k
      · simp only [map_sub,coordinate_projection,blockCrop_mem,hg,hb,hk,hc,and_self,
          ite_true,sub_self,coordinate_initialP,WithTop.coe_lt_coe,not_lt_of_ge hb,ite_false]
      · have hz := R.coordinate_zero_of_color k hk x a hc
        simp only [map_sub,coordinate_projection,blockCrop_mem,hg,hb,hk,hc,and_false,
          sub_zero,coordinate_initialP,hz,ite_self]
    · have hab : a < β := lt_of_not_ge hb
      simp only [map_sub,coordinate_projection,blockCrop_mem,hb,and_false,false_and,
        ite_false,sub_zero,coordinate_initialP,WithTop.coe_lt_coe,hab,ite_true]
  · have hz := R.coordinate_zero_of_cut x a hg
    simp only [map_sub,coordinate_projection,blockCrop_mem,hg,false_and,sub_zero,
      coordinate_initialP,hz,ite_self]

lemma BranchReduction.crop_difference_mixed (hm : R.family = .mixed)
    (β : Γ) (l : ℕ) (x : R.H) :
    (x : E)-projection (blockCrop R.cut R.family β l) x = initialP (β : Cut) x +
      intervalProjection (Set.Ici β) Set.ordConnected_Ici (projection (Crop.colorsBelow l) x) := by
  apply norming.coordinate_ext
  intro a
  have hz : ¬ (a : Cut) < R.cut → coordinate a (x : E) = 0 := R.coordinate_zero_of_cut x a
  simp only [map_sub,map_add,coordinate_projection,blockCrop_mem,hm,coordinate_initialP,
    intervalProjection,Crop.ordinalSet_set,Crop.colorsBelow_set,Set.mem_ofPred_eq,Set.mem_Ici,
    WithTop.coe_lt_coe]
  by_cases hg : (a : Cut) < R.cut <;> by_cases hb : β ≤ a <;> by_cases hc : l ≤ Colors.color a
  all_goals simp only [hg,hb,hc,lt_iff_not_ge,not_true_eq_false,not_false_eq_true,
    and_self,and_true,and_false,ite_true,ite_false]
  all_goals try abel_nf
  all_goals exact hz hg

lemma exists_crop_approx (A : Crop) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Γ →₀ ℝ, (∀ a ∈ v.support, a ∈ A.set .mixed) ∧
      ‖projection A x-norming.includeFinite v‖ < ε := by
  obtain ⟨w,hw⟩ := norming.denseRange_includeFinite.exists_dist_lt x hε
  refine ⟨w.filter (· ∈ A.set .mixed),?_,?_⟩
  · intro a ha
    exact (Finsupp.mem_support_iff.mp ha |> fun h => of_not_not (fun hn => h (by simp [hn])))
  · have he : norming.includeFinite (w.filter (· ∈ A.set .mixed)) = projection A (norming.includeFinite w) :=
      (norming.projection_includeFinite (A.set .mixed) (cropStable A) w).symm
    rw [he,← map_sub]
    exact (norm_projection_le A _).trans_lt (by simpa only [dist_eq_norm] using hw)

lemma BranchReduction.exists_tail_small (β : Γ) (hβ : (β : Cut) < R.cut)
    (l : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : R.H, ‖x‖ = 1 ∧ ‖initialP (β : Cut) (x : E)‖ ≤ δ ∧
      (R.family = .mixed → ∑ k ∈ Finset.range l, ‖colorP k (x : E)‖ ≤ (l : ℝ)*δ) := by
  let D : Finset (R.H →L[ℝ] E) := insert ((initialP (β : Cut)).comp R.H.subtypeL)
    (if R.family = .mixed then (Finset.range l).image (fun k => (colorP k).comp R.H.subtypeL) else ∅)
  have hD : ∀ T ∈ D, StrictlySingular T := by
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact R.earlier _ hβ
    · by_cases hm : R.family = .mixed
      · rw [ite_eq_left hm] at hT
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hT
        exact R.mixed hm k
      · simp only [ite_eq_right hm,Finset.notMem_empty] at hT
  obtain ⟨N,_,hNc,hNi,hN⟩ := exists_small_restriction_finite D hD ⊤ isClosed_univ
    (Singular.top_infinite R.infinite) δ hδ
  obtain ⟨u,hu⟩ := Singular.exists_unit hNi
  let x : R.H := u
  have hxn : ‖x‖ = 1 := hu
  have hi : ‖initialP (β : Cut) (x : E)‖ ≤ δ := by
    have h := hN _ (Finset.mem_insert_self _ _) x u.property
    change ‖initialP (β : Cut) (x : E)‖ ≤ δ*‖x‖ at h
    rwa [hxn,mul_one] at h
  have hcolor (hm : R.family = .mixed) : ∑ k ∈ Finset.range l, ‖colorP k (x : E)‖ ≤ (l : ℝ)*δ := by
    calc
      _ ≤ ∑ _k ∈ Finset.range l, δ := by
        apply Finset.sum_le_sum
        intro k hk
        have hmem : (colorP k).comp R.H.subtypeL ∈ D := Finset.mem_insert_of_mem (by
          rw [ite_eq_left hm]; exact Finset.mem_image.mpr ⟨k,hk,rfl⟩)
        have h := hN _ hmem x u.property
        change ‖colorP k (x : E)‖ ≤ δ*‖x‖ at h
        rwa [hxn,mul_one] at h
      _ = _ := by simp
  exact ⟨x,hxn,hi,hcolor⟩

lemma BranchReduction.crop_error_bound (β : Γ) (l : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (x : R.H) (hi : ‖initialP (β : Cut) (x : E)‖ ≤ δ)
    (hc : R.family = .mixed → ∑ k ∈ Finset.range l, ‖colorP k (x : E)‖ ≤ (l : ℝ)*δ) :
    ‖(x : E)-projection (blockCrop R.cut R.family β l) x‖ ≤ (1+(l : ℝ))*δ := by
  cases hf : R.family with
  | pure k =>
    rw [← hf,R.crop_difference_pure k hf]
    exact hi.trans (by nlinarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)])
  | mixed =>
    rw [← hf,R.crop_difference_mixed hf]
    calc
      _ ≤ ‖initialP (β : Cut) (x : E)‖ +
          ‖intervalProjection (Set.Ici β) Set.ordConnected_Ici (projection (Crop.colorsBelow l) x)‖ := norm_add_le _ _
      _ ≤ δ + ‖projection (Crop.colorsBelow l) x‖ := add_le_add hi (norm_projection_le _ _)
      _ ≤ δ + (l : ℝ)*δ := by
        apply add_le_add_right
        rw [projection_colorsBelow_sum]
        exact (norm_sum_le _ _).trans (hc hf)
      _ = _ := by ring

/-- A unit vector in the reduced subspace can be approximated in any prescribed ordinal and color tail. -/
lemma BranchReduction.exists_next_block (β : Γ) (hβ : (β : Cut) < R.cut)
    (l : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ (x : R.H) (v : Γ →₀ ℝ), ‖x‖ = 1 ∧ v ≠ 0 ∧
      (∀ a ∈ v.support, a ∈ (blockCrop R.cut R.family β l).set .mixed) ∧
      ‖(x : E)-norming.includeFinite v‖ < ε := by
  let δ := ε/(6*((l : ℝ)+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨x,hxn,hi,hc⟩ := R.exists_tail_small β hβ l δ hδ
  have hδb : (1+(l : ℝ))*δ ≤ ε/3 := by
    dsimp only [δ]
    field_simp
    nlinarith [hε]
  have herr := (R.crop_error_bound β l δ hδ.le x hi hc).trans hδb
  obtain ⟨v,hv,herr'⟩ := exists_crop_approx (blockCrop R.cut R.family β l) x (ε/3) (by positivity)
  have he : ‖(x : E)-norming.includeFinite v‖ < ε := by
    have ht := norm_sub_le_norm_sub_add_norm_sub ((x : E)) (projection (blockCrop R.cut R.family β l) x) (norming.includeFinite v)
    linarith
  refine ⟨x,v,hxn,?_,hv,he⟩
  intro hv0
  have hh : ‖(x : E)-norming.includeFinite v‖ = 1 := by rw [hv0,map_zero,sub_zero]; exact hxn
  rw [hh] at he
  linarith

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical
variable {F : Submodule ℝ E} (R : BranchReduction F)
namespace BlockApprox

structure State where
  ordinal : Γ
  below : (ordinal : Cut) < R.cut
  color : ℕ

structure Step (s : State R) (n : ℕ) where
  x : R.H
  vector : Γ →₀ ℝ
  unit : ‖x‖ = 1
  nonzero : vector ≠ 0
  support : ∀ a ∈ vector.support, a ∈ (blockCrop R.cut R.family s.ordinal s.color).set .mixed
  approx : ‖(x : E)-norming.includeFinite vector‖ < error n
  next : Γ
  next_below : (next : Cut) < R.cut
  before_next : ∀ a ∈ vector.support, a < next

lemma exists_step (s : State R) (n : ℕ) : Nonempty (Step R s n) := by
  obtain ⟨x,v,hx,hv,hvs,he⟩ := R.exists_next_block s.ordinal s.below s.color (error n) (error_pos n) (error_le n)
  have hs : ∀ a ∈ v.support, (a : Cut) < R.cut := fun a ha => ((blockCrop_mem _ _ _ _ _).mp (hvs a ha)).1
  obtain ⟨β,hβ,hβv⟩ := R.beyond_finite v.support hs
  exact ⟨⟨x,v,hx,hv,hvs,he,β,hβ,hβv⟩⟩

def step (s : State R) (n : ℕ) : Step R s n := (exists_step R s n).some

def nextState (s : State R) (n : ℕ) : State R where
  ordinal := (step R s n).next
  below := (step R s n).next_below
  color := max s.color ((step R s n).vector.support.sup Colors.color + 1)

def state : ℕ → State R
  | 0 => ⟨R.cut_nonempty.choose,R.cut_nonempty.choose_spec,0⟩
  | n+1 => nextState R (state n) n

def node (n : ℕ) := step R (state R n) n

lemma state_ordinal_strict : StrictMono (fun n => (state R n).ordinal) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨a,ha⟩ := Finsupp.support_nonempty_iff.mpr (node R n).nonzero
  have hs := ((blockCrop_mem _ _ _ _ _).mp ((node R n).support a ha)).2.1
  exact hs.trans_lt ((node R n).before_next a ha)

lemma state_color_mono : Monotone (fun n => (state R n).color) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

lemma support_after {n : ℕ} {a : Γ} (ha : a ∈ (node R n).vector.support) :
    (state R n).ordinal ≤ a ∧ (a : Cut) < R.cut ∧
      (R.family = .mixed → (state R n).color ≤ Colors.color a) := by
  have h := (blockCrop_mem _ _ _ _ _).mp ((node R n).support a ha)
  refine ⟨h.2.1,h.1,?_⟩
  intro hf
  simpa only [hf] using h.2.2

lemma support_color_next {n : ℕ} {a : Γ} (ha : a ∈ (node R n).vector.support) :
    Colors.color a < (state R (n+1)).color := by
  have h := Finset.le_sup (f := Colors.color) ha
  exact (Nat.lt_succ_of_le h).trans_le (le_max_right _ _)

/-- A block sequence approximating unit vectors in the reduced closed subspace, in the selected pure or mixed family. -/
def blocks : BlockSequence R.family where
  vector n := (node R n).vector
  nonzero n := (node R n).nonzero
  successive i j hij a ha b hb := by
    have hβ : a < (state R (i+1)).ordinal := (node R i).before_next a ha
    have hj := support_after R hb
    refine ⟨hβ.trans_le (((state_ordinal_strict R).monotone (Nat.succ_le_iff.mpr hij)).trans hj.1),?_⟩
    intro hm
    exact (support_color_next R ha).trans_le
      ((state_color_mono R (Nat.succ_le_iff.mpr hij)).trans (hj.2.2 hm))
  pure_color k hk n a ha := by
    have h := ((blockCrop_mem _ _ _ _ _).mp ((node R n).support a ha)).2.2
    simpa only [hk] using h

end BlockApprox
end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.LpDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.LpCoding
open Filter
open scoped Classical Topology ENNReal
universe u v
variable {ι : Type u} {p q : ℝ≥0∞}

/-- The finite-support formulation of the norm of an ℓp dual element. -/
lemma finite_dual_bound (hpq : p.toReal.HolderConjugate q.toReal)
    (C : ℝ) (hC : 0 ≤ C) (a : ι → ℝ)
    (h : ∀ c : ι →₀ ℝ, |c.sum (fun i t => t*a i)| ≤ C*‖finite p c‖)
    (s : Finset ι) : ∑ i ∈ s, |a i| ^ q.toReal ≤ C ^ q.toReal := by
  let sign : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1
  have sign_abs (t : ℝ) : |sign t| = 1 := by dsimp [sign]; split_ifs <;> norm_num
  have sign_mul (t : ℝ) : sign t*t = |t| := by
    dsimp [sign]; split_ifs with ht
    · simp [abs_of_nonneg ht]
    · simp [abs_of_neg (lt_of_not_ge ht)]
  let c : ι →₀ ℝ := Finsupp.onFinset s
    (fun i => if i ∈ s then sign (a i)*|a i|^(q.toReal-1) else 0)
    (fun i hi => by by_contra hn; exact hi (ite_eq_right hn))
  have ci (i : ι) : c i = if i ∈ s then sign (a i)*|a i|^(q.toReal-1) else 0 := rfl
  let A : ℝ := ∑ i ∈ s, |a i|^q.toReal
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hpow (i : ι) : |sign (a i)*|a i|^(q.toReal-1)|^p.toReal = |a i|^q.toReal := by
    rw [abs_mul,sign_abs,one_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_mul (abs_nonneg _),hpq.symm.sub_one_mul_conj]
  have hc : ‖finite p c‖ = A^(1/p.toReal) := by
    rw [lp.norm_eq_tsum_rpow hpq.pos]
    congr 1
    calc
      _ = ∑ i ∈ s, |c i|^p.toReal := by
        simp only [finite_apply,Real.norm_eq_abs]
        apply tsum_eq_sum
        intro i hi
        simp only [ci,ite_eq_right hi,abs_zero,Real.zero_rpow hpq.ne_zero]
      _ = A := Finset.sum_congr rfl (fun i hi => by rw [ci,ite_eq_left hi,hpow])
  have hpair : c.sum (fun i t => t*a i) = A := by
    rw [Finsupp.sum_of_support_subset c (show c.support ⊆ s from by
      intro i hi; by_contra hn; exact Finsupp.mem_support_iff.mp hi (by rw [ci,ite_eq_right hn]))
      (fun i t => t*a i) (fun i _ => zero_mul _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ci,ite_eq_left hi]
    calc
      sign (a i)*|a i|^(q.toReal-1)*a i = |a i|^(q.toReal-1)*|a i| := by rw [← sign_mul]; ring
      _ = |a i|^q.toReal := by
        rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith [hpq.symm.pos])]
        congr 1
        ring
  have hb := h c
  rw [hpair,abs_of_nonneg hA,hc] at hb
  by_cases hAz : A=0
  · rw [show (∑ i ∈ s, |a i|^q.toReal)=0 from hAz]
    exact Real.rpow_nonneg hC _
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hnorm : A^(1/q.toReal) ≤ C := by
    have hexp : 1/q.toReal = 1-1/p.toReal := by simpa only [one_div] using hpq.one_sub_inv.symm
    rw [hexp,Real.rpow_sub hAp,Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hAp _)).mpr hb
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hA _) hnorm hpq.symm.pos.le
  simpa only [← Real.rpow_mul hA,one_div_mul_cancel hpq.symm.ne_zero,Real.rpow_one] using hr

lemma dual_mem (hpq : p.toReal.HolderConjugate q.toReal)
    (C : ℝ) (hC : 0 ≤ C) (a : ι → ℝ)
    (h : ∀ c : ι →₀ ℝ, |c.sum (fun i t => t*a i)| ≤ C*‖finite p c‖) : Memℓp a q := by
  apply memℓp_gen'
  simpa only [Real.norm_eq_abs] using finite_dual_bound hpq C hC a h

lemma dual_norm (hpq : p.toReal.HolderConjugate q.toReal)
    (C : ℝ) (hC : 0 ≤ C) (a : ι → ℝ)
    (h : ∀ c : ι →₀ ℝ, |c.sum (fun i t => t*a i)| ≤ C*‖finite p c‖) :
    ‖(⟨a,dual_mem hpq C hC a h⟩ : lp (fun _ : ι => ℝ) q)‖ ≤ C := by
  apply lp.norm_le_of_forall_sum_le hpq.symm.pos hC
  simpa only [Real.norm_eq_abs] using finite_dual_bound hpq C hC a h

end SeparableQuotient.LpCoding

namespace SeparableQuotient.LpCoding
open Filter
open scoped Classical Topology ENNReal
universe u v
variable {ι : Type u} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

lemma coefficient_bound (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) (c : ι →₀ ℝ) :
    |c.sum (fun i t => t*g (lp.single p i 1))| ≤ ‖g‖ * ‖finite p c‖ := by
  have he : c.sum (fun i t => t*g (lp.single p i 1)) = g (finite p c) := by
    conv_rhs => rw [← Finsupp.sum_single c]
    simp only [map_finsuppSum,finite_single]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [single_eq_smul p i (c i),map_smul,smul_eq_mul]
  rw [he]
  exact g.le_opNorm _

def coefficients (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) : lp (fun _ : ι => ℝ) q :=
  ⟨fun i => g (lp.single p i 1),
    dual_mem hpq ‖g‖ (norm_nonneg _) _ (coefficient_bound g)⟩

omit [Fact (1 ≤ q)] in
@[simp] lemma coefficients_apply (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) (i : ι) :
    coefficients hpq g i = g (lp.single p i 1) := rfl

omit [Fact (1 ≤ q)] in
lemma norm_coefficients_le (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) : ‖coefficients hpq g‖ ≤ ‖g‖ :=
  dual_norm hpq ‖g‖ (norm_nonneg _) _ (coefficient_bound g)

/-- Symmetry of the two ℓp dual evaluations. -/
lemma eval_coefficients_symm (hpq : p.toReal.HolderConjugate q.toReal)
    (hp : p ≠ ∞) (hq : q ≠ ∞)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p))
    (h : StrongDual ℝ (lp (fun _ : ι => ℝ) q)) :
    g (coefficients hpq.symm h) = h (coefficients hpq g) := by
  have hg := g.continuous.tendsto _ |>.comp
    (lp.hasSum_single hp (coefficients hpq.symm h))
  have hh := h.continuous.tendsto _ |>.comp
    (lp.hasSum_single hq (coefficients hpq g))
  have he : (fun s : Finset ι => g (∑ i ∈ s, lp.single p i (coefficients hpq.symm h i))) =
      (fun s : Finset ι => h (∑ i ∈ s, lp.single q i (coefficients hpq g i))) := by
    funext s
    simp only [map_sum,coefficients_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [single_eq_smul p i (h (lp.single q i 1)),
      single_eq_smul q i (g (lp.single p i 1))]
    simp only [map_smul,smul_eq_mul,mul_comm]
  exact tendsto_nhds_unique hg (by simpa only [Function.comp_def,← he] using hh)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def analysisMap (hpq : p.toReal.HolderConjugate q.toReal)
    (T : lp (fun _ : ι => ℝ) p →L[ℝ] E) : StrongDual ℝ E →L[ℝ] lp (fun _ : ι => ℝ) q :=
  LinearMap.mkContinuous
    { toFun := fun g => coefficients hpq (g.comp T)
      map_add' := fun g h => by apply lp.ext; rfl
      map_smul' := fun c g => by apply lp.ext; rfl }
    ‖T‖ (fun g => (norm_coefficients_le hpq (g.comp T)).trans
      (by simpa only [mul_comm] using ContinuousLinearMap.opNorm_comp_le g T))

@[simp] lemma analysisMap_apply (hpq : p.toReal.HolderConjugate q.toReal)
    (T : lp (fun _ : ι => ℝ) p →L[ℝ] E) (g : StrongDual ℝ E) (i : ι) :
    analysisMap hpq T g i = g (T (lp.single p i 1)) := rfl

lemma norm_analysisMap_le (hpq : p.toReal.HolderConjugate q.toReal)
    (T : lp (fun _ : ι => ℝ) p →L[ℝ] E) : ‖analysisMap hpq T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  change ‖coefficients hpq (g.comp T)‖ ≤ _
  exact (norm_coefficients_le hpq (g.comp T)).trans
    (by simpa only [mul_comm] using ContinuousLinearMap.opNorm_comp_le g T)

end SeparableQuotient.LpCoding

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.pathDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.pathDualSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.wGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.wSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.wComplete
lemma norm_pathMap_le (f : Family) : ‖pathMap f‖ ≤ 1 := by
  exact LinearMap.opNorm_extendOfNorm_le (f := finitePathMap f)
    (e := LpCoding.finite f.pathExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.pathExponent) f.pathExponent_ne_top)
    (by norm_num) (fun c => by simpa only [one_mul] using finitePathMap_bound f c)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures Cardinal
open scoped Classical Cardinal

lemma Family.index_injective : Function.Injective Family.index := by
  intro f g h
  cases f <;> cases g <;> simp_all [Family.index]

lemma pathLabel_injective (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) :
    Function.Injective (fun z : (f : Family) × PathIndex f => pathLabel hCH z.1 z.2) := by
  rintro ⟨f,P⟩ ⟨g,Q⟩ h
  have hi := congrArg (fun a => (Colors.partitionEquiv a).2) h
  simp only [pathLabel,Colors.inColor,Equiv.apply_symm_apply] at hi
  have hf : f=g := Family.index_injective (by
    have hh := congrArg Colors.color hi
    simpa [Colors.color] using hh)
  subst g
  have hp : P=Q := (pathLabelBase hCH f).injective
    (Colors.inColor_injective _ hi)
  cases hp
  rfl

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

lemma norm_labelMap_le (f : Family) : ‖labelMap hCH f‖ ≤ 1 := by
  exact LinearMap.opNorm_extendOfNorm_le (f := finiteLabelMap hCH f)
    (e := LpCoding.finite f.sourceExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.sourceExponent) f.sourceExponent_ne_top)
    (by norm_num) (fun c => by simpa only [one_mul] using finiteLabelMap_bound hCH f c)

@[simp] lemma labelMap_single (f : Family) (P : PathIndex f) (a : ℝ) :
    labelMap hCH f (lp.single f.sourceExponent P a) = a • e (pathLabel hCH f P) := by
  rw [← LpCoding.finite_single,labelMap_finite,finiteLabelMap_eq,Finsupp.embDomain_single]
  change norming.includeFinite (Finsupp.single (pathLabel hCH f P) a) = _
  have hs : Finsupp.single (pathLabel hCH f P) a = a • Finsupp.single (pathLabel hCH f P) (1 : ℝ) := by
    simp
  rw [hs,map_smul]
  rfl

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

namespace SeparableQuotient.Norming

def Family.at : ℕ → Family
  | 0 => .mixed
  | k+1 => .pure k
@[simp] lemma Family.at_index (f : Family) : Family.at f.index = f := by cases f <;> rfl
@[simp] lemma Family.index_at (n : ℕ) : (Family.at n).index = n := by cases n <;> rfl
end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace

open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

@[reducible] local instance opDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance opDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
local instance opXClosed : IsClosed (X₀ : Set (StrongDual ℝ E)) := norming.predual_isClosed
@[reducible] local instance opWGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance opWSpace : NormedSpace ℝ W := inferInstance
local instance opWT2 : T2Space W := @cachedNormedT2 W opWGroup

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

def labelAnalysis (f : Family) : StrongDual ℝ E →L[ℝ] lp (fun _ : PathIndex f => ℝ) f.pathExponent :=
  LpCoding.analysisMap f.pathConjugate (labelMap hCH f)

@[simp] lemma labelAnalysis_apply (f : Family) (y : StrongDual ℝ E) (P : PathIndex f) :
    labelAnalysis hCH f y P = y (e (pathLabel hCH f P)) := by
  change y (labelMap hCH f (lp.single f.sourceExponent P 1)) = _
  rw [labelMap_single,one_smul]

lemma norm_labelAnalysis_le (f : Family) : ‖labelAnalysis hCH f‖ ≤ 1 :=
  (LpCoding.norm_analysisMap_le _ _).trans (norm_labelMap_le hCH f)

def familyOperator (f : Family) : StrongDual ℝ E →L[ℝ] W :=
  (pathMap f).comp (labelAnalysis hCH f)

lemma norm_familyOperator_le (f : Family) : ‖familyOperator hCH f‖ ≤ 1 := by
  calc
    _ ≤ ‖pathMap f‖ * ‖labelAnalysis hCH f‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul (norm_pathMap_le f) (norm_labelAnalysis_le hCH f)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma labelAnalysis_coordinate_self (f : Family) (P : PathIndex f) :
    labelAnalysis hCH f (coordinate (pathLabel hCH f P)) = lp.single f.pathExponent P 1 := by
  apply lp.ext
  funext Q
  simp only [labelAnalysis_apply,coordinate_e,lp.single_apply,Pi.single_apply]
  have he : pathLabel hCH f P = pathLabel hCH f Q ↔ P=Q := (pathLabelEmb hCH f).injective.eq_iff
  simp only [he,eq_comm]

lemma labelAnalysis_coordinate_other (f g : Family) (P : PathIndex f) (hfg : f ≠ g) :
    labelAnalysis hCH g (coordinate (pathLabel hCH f P)) = 0 := by
  apply lp.ext
  funext Q
  have hn : pathLabel hCH f P ≠ pathLabel hCH g Q := by
    intro h
    have hs : (Sigma.mk f P : (t : Family) × PathIndex t) = Sigma.mk g Q :=
      pathLabel_injective hCH h
    exact hfg (congrArg Sigma.fst hs)
  simp [labelAnalysis_apply,coordinate_e,hn]

lemma familyOperator_coordinate (f g : Family) (P : PathIndex f) :
    familyOperator hCH g (coordinate (pathLabel hCH f P)) =
      if f=g then pathCoset P else 0 := by
  by_cases h : f=g
  · subst g
    simp [familyOperator,labelAnalysis_coordinate_self]
  · simp [familyOperator,labelAnalysis_coordinate_other hCH f g P h,h]

lemma operator_summable : Summable (fun n => tau n • familyOperator hCH (Family.at n)) := by
  apply tau_summable.of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_of_nonneg (tau_pos n).le]
  exact mul_le_of_le_one_right (tau_pos n).le (norm_familyOperator_le hCH _)

/-- The CH perturbation operator with norm at most 1/10. -/
def B : StrongDual ℝ E →L[ℝ] W := ∑' n, tau n • familyOperator hCH (Family.at n)

lemma B_coordinate (f : Family) (P : PathIndex f) :
    B hCH (coordinate (pathLabel hCH f P)) = tau f.index • pathCoset P := by
  have hsum := (ContinuousLinearMap.apply ℝ W (coordinate (pathLabel hCH f P))).hasSum
    (operator_summable hCH).hasSum
  have hf : (fun n => (tau n • familyOperator hCH (Family.at n))
      (coordinate (pathLabel hCH f P))) =
      (fun n => if n=f.index then tau f.index • pathCoset P else 0) := by
    funext n
    rw [smul_apply,familyOperator_coordinate]
    by_cases h : n=f.index
    · subst n; simp
    · have hn : f ≠ Family.at n := by
        intro hf
        apply h
        rw [hf,Family.index_at]
      simp [h,hn]
  have he := hasSum_ite_eq f.index (tau f.index • pathCoset P)
  exact hsum.unique (by simpa only [ContinuousLinearMap.apply_apply,hf] using he)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

@[reducible] local instance propDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance propDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
local instance propXClosed : IsClosed (X₀ : Set (StrongDual ℝ E)) := norming.predual_isClosed
@[reducible] local instance propWGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance propWSpace : NormedSpace ℝ W := inferInstance
@[reducible] local instance propWDualGroup : NormedAddCommGroup (StrongDual ℝ W) := inferInstance
@[reducible] local instance propWDualSpace : NormedSpace ℝ (StrongDual ℝ W) := inferInstance

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

lemma pathMap_mem_closed (Z : Submodule ℝ W) (hZ : IsClosed (Z : Set W))
    (f : Family) (hf : ∀ P : PathIndex f, pathCoset P ∈ Z)
    (a : lp (fun _ : PathIndex f => ℝ) f.pathExponent) : pathMap f a ∈ Z := by
  refine (LpCoding.finite_dense (ι := PathIndex f) (p := f.pathExponent) f.pathExponent_ne_top).induction_on
    (p := fun a => pathMap f a ∈ Z) a (hZ.preimage (pathMap f).continuous) ?_
  intro c
  rw [pathMap_finite]
  exact Z.sum_mem (fun i _ => Z.smul_mem _ (hf i))

lemma pathCoset_mem_B_predual (f : Family) (P : PathIndex f) :
    pathCoset P ∈ X₀.map (B hCH).toLinearMap := by
  have h : tau f.index • pathCoset P ∈ X₀.map (B hCH).toLinearMap := by
    refine ⟨coordinate (pathLabel hCH f P),norming.coordinate_mem_predual _,?_⟩
    exact B_coordinate hCH f P
  have hh := (X₀.map (B hCH).toLinearMap).smul_mem (tau f.index)⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ (tau_pos _).ne',one_smul] using hh

lemma B_range_mem_predual_closure :
    (B hCH).range ≤ (X₀.map (B hCH).toLinearMap).topologicalClosure := by
  rintro _ ⟨y,rfl⟩
  let Z := (X₀.map (B hCH).toLinearMap).topologicalClosure
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    ((ContinuousLinearMap.apply ℝ W y).hasSum (operator_summable hCH).hasSum)
  apply Eventually.of_forall
  intro s
  simp only [ContinuousLinearMap.apply_apply,smul_apply]
  apply Z.sum_mem
  intro n _
  apply Z.smul_mem
  exact pathMap_mem_closed Z (Submodule.isClosed_topologicalClosure _) (Family.at n)
    (fun P => Submodule.le_topologicalClosure _ (pathCoset_mem_B_predual hCH _ P))
    (labelAnalysis hCH _ y)

def familyVector (f : Family) (w : StrongDual ℝ W) : E :=
  labelMap hCH f (LpCoding.coefficients f.pathConjugate.symm (w.comp (pathMap f)))

lemma norm_familyVector_le (f : Family) (w : StrongDual ℝ W) :
    ‖familyVector hCH f w‖ ≤ ‖w‖ := by
  calc
    _ ≤ ‖labelMap hCH f‖ * ‖LpCoding.coefficients f.pathConjugate.symm (w.comp (pathMap f))‖ :=
      (labelMap hCH f).le_opNorm _
    _ ≤ 1 * ‖w.comp (pathMap f)‖ := mul_le_mul (norm_labelMap_le hCH f)
      (LpCoding.norm_coefficients_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ ‖w‖ := by
      rw [one_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (norm_pathMap_le f))

lemma familyVector_pair (f : Family) (w : StrongDual ℝ W) (y : StrongDual ℝ E) :
    y (familyVector hCH f w) = w (familyOperator hCH f y) := by
  exact LpCoding.eval_coefficients_symm f.pathConjugate f.sourceExponent_ne_top f.pathExponent_ne_top
    (y.comp (labelMap hCH f)) (w.comp (pathMap f))

lemma vector_summable (w : StrongDual ℝ W) :
    Summable (fun n => tau n • familyVector hCH (Family.at n) w) := by
  apply (tau_summable.mul_right ‖w‖).of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_of_nonneg (tau_pos n).le]
  exact mul_le_mul_of_nonneg_left (norm_familyVector_le hCH _ _) (tau_pos n).le

/-- The adjoint perturbation has range in the canonical evaluation image. -/
lemma B_adjoint (w : StrongDual ℝ W) :
    ∃ v : E, w.comp (B hCH) = NormedSpace.inclusionInDoubleDual ℝ E v := by
  refine ⟨∑' n, tau n • familyVector hCH (Family.at n) w,?_⟩
  ext y
  have hB := w.hasSum ((ContinuousLinearMap.apply ℝ W y).hasSum (operator_summable hCH).hasSum)
  have hv := y.hasSum (vector_summable hCH w).hasSum
  have he : (fun n => w ((tau n • familyOperator hCH (Family.at n)) y)) =
      fun n => y (tau n • familyVector hCH (Family.at n) w) := by
    funext n
    simp only [smul_apply,map_smul,familyVector_pair]
  change w (B hCH y) = y (∑' n, tau n • familyVector hCH (Family.at n) w)
  exact hB.unique (by simpa only [ContinuousLinearMap.apply_apply,he] using hv)

end SeparableQuotient.ActualSpace

end

end OAI
end


