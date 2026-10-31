-- Prove2me | Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
-- name    : MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:37:01.596857+00:00
-- url     : https://prove2.me/theorems/11c9c296-8c3a-412e-88bd-58e579c53601
-- title:
--   MarkovProcess: MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaApproximation_2f7df37a
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology

noncomputable section

namespace MarkovProcess.Semigroup

/-- A map preserves a set if it sends every member of the set back into it. -/
def PreservesSet {E F : Type*} (T : E → F) (C : Set E) (D : Set F) : Prop :=
  ∀ ⦃x⦄, x ∈ C → T x ∈ D

namespace PreservesSet

variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}

theorem id : PreservesSet (fun x : E ↦ x) C C :=
  fun _ hx ↦ hx



/-- A closed set is preserved by the pointwise limit of preserving maps. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    [TopologicalSpace F] [T2Space F] {T : ι → E → F} {S : E → F}
    (hD : IsClosed D) (hT : ∀ i, PreservesSet (T i) C D)
    (hlim : ∀ x, Tendsto (fun i ↦ T i x) l (nhds (S x))) :
    PreservesSet S C D := by
  intro x hx
  exact hD.mem_of_tendsto (hlim x) (Eventually.of_forall fun i ↦ hT i hx)

end PreservesSet

end MarkovProcess.Semigroup

namespace Convex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite subprobability barycenter of points in a convex set containing
zero belongs to the set. -/
theorem p2m_embedded_40ef409b42f7e116 {C : Set E} (hC : Convex ℝ C) (hzero : 0 ∈ C)
    (s : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1)
    (hz : ∀ i ∈ s, z i ∈ C) :
    ∑ i ∈ s, w i • z i ∈ C := by
  classical
  let s' : Finset (Option ι) := insert none (s.image some)
  let w' : Option ι → ℝ
    | none => 1 - ∑ i ∈ s, w i
    | some i => w i
  let z' : Option ι → E
    | none => 0
    | some i => z i
  have hnone : none ∉ s.image some := by
    simp
  have hw' : ∀ i ∈ s', 0 ≤ w' i := by
    intro i hi
    rcases i with _ | i
    · exact sub_nonneg.mpr hsum
    · exact hw i (by
        have : some i ∈ s.image some := by
          simpa only [s', Finset.mem_insert, Option.some_ne_none, false_or] using hi
        simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right] using this)
  have hz' : ∀ i ∈ s', z' i ∈ C := by
    intro i hi
    rcases i with _ | i
    · exact hzero
    · exact hz i (by
        have : some i ∈ s.image some := by
          simpa only [s', Finset.mem_insert, Option.some_ne_none, false_or] using hi
        simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right] using this)
  have hsum' : ∑ i ∈ s', w' i = 1 := by
    simp [s', hnone, w']
  have hmem := hC.sum_mem hw' hsum' hz'
  simpa [s', hnone, z', w'] using hmem

/-- A convergent countable subprobability barycenter of points in a closed
convex set containing zero belongs to the set. -/
theorem tsum_mem_of_tsum_le_one {C : Set E} (hclosed : IsClosed C)
    (hC : Convex ℝ C) (hzero : 0 ∈ C) (w : ℕ → ℝ) (z : ℕ → E)
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) (htsum : ∑' n, w n ≤ 1)
    (hz : ∀ n, z n ∈ C) (hweighted : Summable fun n ↦ w n • z n) :
    ∑' n, w n • z n ∈ C := by
  apply hclosed.mem_of_tendsto hweighted.hasSum.tendsto_sum_nat
  exact Eventually.of_forall fun n ↦
    _root_.Convex.p2m_embedded_40ef409b42f7e116
      hC hzero (Finset.range n) w z
      (fun i _ ↦ hw i)
      ((hsum.sum_le_tsum (Finset.range n) (fun i _ ↦ hw i)).trans htsum)
      (fun i _ ↦ hz i)

end Convex

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Invariance under a normalized resolvent propagates to all of its finite
iterates.  These are the atoms in the Poisson representation of a bounded
Yosida exponential. -/
theorem preservesSet_scaledOperator_pow (R : ContractiveResolvent E)
    (C : Set E) (α : PositiveShift)
    (hQ : PreservesSet (R.scaledOperator α) C C) (n : ℕ) :
    PreservesSet ((R.scaledOperator α) ^ n) C C := by
  induction n with
  | zero =>
      simpa only [pow_zero, one_apply_eq_self] using!
        (PreservesSet.id (C := C))
  | succ n ih =>
      intro x hx
      rw [pow_succ, mul_apply_eq_comp]
      exact ih (hQ hx)

section CompleteSpace

variable [CompleteSpace E]

/-- If every canonical bounded Yosida approximation preserves a closed set,
then the generated strong-limit semigroup preserves it as well.  This theorem
contains no semigroup-level preservation hypothesis: its input is the concrete
approximating family produced from the resolvent. -/
theorem preservesSet_generatedSemigroup_of_yosida
    (R : ContractiveResolvent E) (C : Set E) (hC : IsClosed C)
    (happrox : ∀ n t, PreservesSet
      (R.yosidaOperator (naturalShift n) t) C C) (t : NNReal) :
    PreservesSet (R.generatedSemigroup t) C C := by
  exact PreservesSet.of_tendsto hC (fun n ↦ happrox n t)
    (R.tendsto_yosidaOperator_naturalShift_apply t)

/-- A version exposing all positive shifts, convenient when the Poisson
invariance theorem has been proved uniformly in the shift. -/
theorem preservesSet_generatedSemigroup
    (R : ContractiveResolvent E) (C : Set E) (hC : IsClosed C)
    (happrox : ∀ α t, PreservesSet (R.yosidaOperator α t) C C)
    (t : NNReal) : PreservesSet (R.generatedSemigroup t) C C := by
  exact R.preservesSet_generatedSemigroup_of_yosida C hC
    (fun n s ↦ happrox (naturalShift n) s) t

end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup


