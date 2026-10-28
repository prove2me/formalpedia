-- Prove2me | Definitions.Def_OAIQ9Tr002
-- name    : OAIQ9Tr002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T09:50:42.803988+00:00
-- url     : https://prove2.me/theorems/09e64ad3-6a9c-4e49-96dd-2a90aa6fb371
-- title:
--   Definitions bundle OAIQ9Tr002 of the split of OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 53 definitions, 1 instance and 7 theorems. The definitions and types are `OAI.TraceReconstruction.sourceChronologyCode`, `OAI.TraceReconstruction.sourceClippingCost`, `OAI.TraceReconstruction.sourceCoefficient`, `OAI.TraceReconstruction.sourceCollectionIndex`, `OAI.TraceReconstruction.sourceCollectionSet`, `OAI.TraceReconstruction.sourceDensePair`, `OAI.TraceReconstruction.sourceEffectiveHiddenTail`, `OAI.TraceReconstruction.sourceFlatFillerWord`, `OAI.TraceReconstruction.sourceFlatLeafType`, `OAI.TraceReconstruction.sourceFlatTrialWord`, `OAI.TraceReconstruction.sourceForcedBudget`, `OAI.TraceReconstruction.sourceFramedWord`, `OAI.TraceReconstruction.sourceFullWord`, `OAI.TraceReconstruction.sourceGlobalCoefficient`, `OAI.TraceReconstruction.sourceGoodRoleSquare`, `OAI.TraceReconstruction.sourceGroupCoefficient`, `OAI.TraceReconstruction.sourceInitialAnchor`, `OAI.TraceReconstruction.sourceInitialCount`, `OAI.TraceReconstruction.sourceInitialError`, `OAI.TraceReconstruction.sourceInitialPure`, `OAI.TraceReconstruction.sourceInitialWord`, `OAI.TraceReconstruction.sourceInteriorExponent`, `OAI.TraceReconstruction.sourceLeafProduct`, `OAI.TraceReconstruction.sourceOracleCoefficient`, `OAI.TraceReconstruction.sourceOracleDecode`, `OAI.TraceReconstruction.sourceOracleDensity`, `OAI.TraceReconstruction.sourcePlateauCenter`, `OAI.TraceReconstruction.sourcePostCount`, `OAI.TraceReconstruction.sourcePreCount`, `OAI.TraceReconstruction.sourceReferenceLaw`, `OAI.TraceReconstruction.sourceSharpDegreeBudget`, `OAI.TraceReconstruction.sourceSharpEnergyBudget`, `OAI.TraceReconstruction.sourceSignedCoefficient`, `OAI.TraceReconstruction.sourceSubsetCode`, `OAI.TraceReconstruction.sourceTailDenominator`, `OAI.TraceReconstruction.sourceTailExponent`, `OAI.TraceReconstruction.sourceTreeLeafSign`, `OAI.TraceReconstruction.sourceTreeWord`, `OAI.TraceReconstruction.sourceTypicalSet`, `OAI.TraceReconstruction.sourceWindowStart` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/TraceReconstruction, in whole or in part: `TraceReconstruction_Amplification`, `TraceReconstruction_Anchors`, `TraceReconstruction_Differences`, `TraceReconstruction_Energy`, `TraceReconstruction_InitialDensity`, `TraceReconstruction_InitialRates`, `TraceReconstruction_Layout`, `TraceReconstruction_LayoutRates`, `TraceReconstruction_LeafOracle`, `TraceReconstruction_Metadata`, `TraceReconstruction_Model`, `TraceReconstruction_Oracles`, `TraceReconstruction_Propagation`, `TraceReconstruction_Ranks`, `TraceReconstruction_Restoration`, `TraceReconstruction_Simulation`, `TraceReconstruction_SourceOracle`.
--
--   **Imports.** It imports the published bundle `Def_TraceReconstruction`; the bundles `OAIQ9Tr000` and `OAIQ9Tr001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.TraceReconstruction.actual_one_window_oracle`, `OAI.TraceReconstruction.actual_source_oracle`, `OAI.TraceReconstruction.source_initial_oracles_eventually`, `OAI.TraceReconstruction.source_level_all_budgets`, `OAI.TraceReconstruction.source_level_energy`, `OAI.TraceReconstruction.source_level_overlap`, `OAI.TraceReconstruction.source_level_warmup_second` and `OAI.TraceReconstruction.source_reference_clipped_exists`; the proofs of `OAI.TraceReconstruction.actual_initial_oracles`, `OAI.TraceReconstruction.actual_one_window_oracle`, `OAI.TraceReconstruction.actual_source_oracle`, `OAI.TraceReconstruction.initial_pure_sigma_clipped_exists`, `OAI.TraceReconstruction.initial_sigma_clipped_exists`, `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.source_all_levels_eventually`, `OAI.TraceReconstruction.source_initial_level_eventually`, `OAI.TraceReconstruction.source_initial_oracles_eventually`, `OAI.TraceReconstruction.source_level_all_budgets`, `OAI.TraceReconstruction.source_level_energy`, `OAI.TraceReconstruction.source_level_overlap`, `OAI.TraceReconstruction.source_level_warmup_second`, `OAI.TraceReconstruction.source_reference_clipped_exists` and `OAI.TraceReconstruction.superpolynomial_one_trace`.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/TraceReconstruction at commit adc7f12

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_OAIQ9Tr000
import Definitions.Def_OAIQ9Tr001

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Model

Independent deletion, complete trace observations, randomized estimators, ENNReal fixed-budget complexity, concatenation, and literal input words.
-/

open scoped ENNReal
noncomputable section

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction




/-! ## Exact finite channel laws -/

theorem traceOfMask_mem {n : ℕ} (x : Word n) (a : Mask n) :
    traceOfMask x a ∈ traceSpace n :=
  mem_traceSpace_of_length_le _ (traceOfMask_length_le x a)


end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ranks

Retained subsets, conditional rank experiments, tagged gaps, period geometry, Gaussian Schur estimates, and uniform square sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


namespace TraceReconstruction

instance taggedRankEvent_decidable {n l r : ℕ} (p : Fin r → Fin n)
    (v : Fin r → Fin l) (S : FixedSubset (Fin n) l) : Decidable (taggedRankEvent p v S) := by
  unfold taggedRankEvent
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Differences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

namespace TraceReconstruction

/-- The tensor product of finitely supported one-dimensional coefficient
series, represented on its literal vector-valued exponents. -/
def tensorSeries {ι : Type*} [Fintype ι] (f : ι → IntSeries) :
    AddMonoidAlgebra ℝ (ι → ℤ) :=
by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (Fintype.piFinset (fun i => (f i).coeff.support))
    (fun z => ∏ i, (f i).coeff (z i)) (by
      classical
      intro z hz
      simp only [Fintype.mem_piFinset,Finsupp.mem_support_iff]
      exact fun i => (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)))

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialDensity

Defect monomials, orthogonality, normalized initial densities, and common mass.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section

namespace TraceReconstruction
open FiniteLaw

/-- Canonical increasing tuple associated with a selected set of ranks. -/
def tupleOfMask {l r : ℕ} (σ : Fin l → Bool) (hσ : monomialDegree σ = r) :
    IncreasingTuple l r := by
  classical
  let S : Finset (Fin l) := Finset.univ.filter (fun i => σ i = true)
  have hS : S.card = r := hσ
  exact ⟨fun i => ((S.orderIsoOfFin hS) i).val, (S.orderIsoOfFin hS).strictMono⟩

end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

variable {α β : Type*} [Fintype α] [Fintype β]

def visibleFiberEquiv (m : ℕ) (S : Finset α) (hS : S.card≤ m) :
    {T : FixedSubset (α⊕β) m // T.val.toLeft=S} ≃ FixedSubset β (m-S.card) where
  toFun T := ⟨T.val.val.toRight,by
    have hc := Finset.card_toLeft_add_card_toRight (u:=T.val.val)
    rw [T.property,T.val.property] at hc
    omega⟩
  invFun R := ⟨⟨S.disjSum R.val,by simp only [Finset.card_disjSum,R.property]; omega⟩,by simp⟩
  left_inv T := by
    apply Subtype.ext; apply Subtype.ext
    simpa only [T.property] using (Finset.toLeft_disjSum_toRight (u:=T.val.val))
  right_inv R := by apply Subtype.ext; exact Finset.toRight_disjSum

def visibleScheduleLaw (m : ℕ) (hm : m≤Fintype.card α+Fintype.card β) : FiniteLaw (Finset α) :=
  (uniformSubsetLaw (α:=α⊕β) m (by simpa using hm)).map (fun T => T.val.toLeft)

end TraceReconstruction

noncomputable section


noncomputable section


noncomputable section
noncomputable section

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

def uniformSchedulePayload {n : ℕ} (P Q : FiniteLaw α) (m : ℕ) (hm : m≤n) :
    FiniteLaw (Fin n→α) :=
  (uniformSubsetLaw (α:=Fin n) m (by simpa using hm)).bind
    (fun S => FiniteLaw.coordinateProduct (fun i => if i∈S.val then Q else P))

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LeafOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LeafOracle

Recursive leaf oracles, sparse high tails, occupied shapes, posterior smoothing, source bit trees, and singleton cancellation.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Literal top-down type recursion in the source's unconditioned surrogate.
`X path` is the root anchor or `w_j-Y_path`. Dependence of different paths
through the same global jitter is retained by this single full-tree map. -/
def windowLeafSign (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ) :
    (b : ℕ) → List ℕ → ℝ → WindowLeaf T b → ℝ
  | 0, _, τ, _ => τ
  | b+1, path, τ, v => windowLeafSign T s X b (path++[v.1.val])
      (motifChildSign s (X path) v.1.val τ) v.2

def windowLeafType (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) (v : WindowLeaf T b) : Bool :=
  decide (windowLeafSign T s X b path τ v= -1)

/-- A finite indexing of all leaves, not just the active or fitted leaves. -/
def windowFinType (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (τ : ℝ) (i : Fin (Fintype.card (WindowLeaf T b))) : Bool :=
  windowLeafType T s X b [] τ ((Fintype.equivFin (WindowLeaf T b)).symm i)

/-- Exact number of minus leaves in a fixed realization, without a fit condition. -/
def windowMinusCount (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) : ℕ :=
  ∑v : WindowLeaf T b, if windowLeafSign T s X b path τ v= -1 then 1 else 0

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Exact recursive leaf signs for the complete bit tree, with one joint
parent-global shift supplied to each sibling's local mechanism. -/
def sourceTreeLeafSign (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → WindowAssignments T n g Bool b → ℤ → ℝ → WindowLeaf T b → ℝ
  | 0, _, _, τ, _ => τ
  | b+1, bits, incoming, τ, v =>
      sourceTreeLeafSign T n g s center globalShift b (bits.2.2 v.1)
        (globalShift b bits.2.1 v.1)
        (motifChildSign s (center b-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) v.1.val τ) v.2

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Anchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Anchors

Forced anchors, extra-leaf closeness, and correlated group square-sum estimates.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section

noncomputable section


namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def sourceLeafProduct (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) : ℝ :=
  ∏v∈S, sourceBottomIndicator T n g s center globalShift b bits incoming v

end TraceReconstruction



end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy

Shaped envelopes, actual coefficient aggregation, role counts, central contributions, and full coefficient energy.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The coefficient is defined directly from the two literal leaf-type
patterns under the common complete posterior bit tree. -/
def sourceCoefficient (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) : ℝ :=
  (windowPosteriorLaw T n g (b+1) d).expect (fun bits =>
    ∏v∈S,(1-sourceTreeLeafSign T n g s center globalShift (b+1) bits incoming 1 v)/2) -
  (windowPosteriorLaw T n g (b+1) d).expect (fun bits =>
    ∏v∈S,(1-sourceTreeLeafSign T n g s center globalShift (b+1) bits incoming (-1) v)/2)

def sourceGoodRoleSquare (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (w : SourceRoleIndex T b) : ℝ :=
  if h : w.1.card=r ∧ Nonempty (occupiedWindowTerm T b w.1 w.2).Forced then
    let u : DegreeForcedRole T b r := ⟨w,h⟩
    if BinaryWindowLabels.allowed T A s (b+1)
      ((u.shape T b r).forced.labels T (occupiedTermLabels T b w.1 w.2)) then
      (sourceRoleAverage T n g s center globalShift b d incoming w.1 w.2)^2 else 0
  else 0

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Layout

Multiwindow and paired layouts, coordinate simulations, and literal source types and trees.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section

noncomputable section


noncomputable section

noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourcePreCount (N A t h : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) : Fin N → ℕ :=
  pairedPreCount (sourceBundleLeft N) (sourcePreFiller N A t h)
    (sourceBundleCount N t h loc glob)

def sourcePostCount (N B t h : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) : Fin N → ℕ :=
  pairedPostCount (sourceBundleRight N) (sourcePostFiller N B t h)
    (fun _ => sourceLayoutReserve t h) (sourceBundleCount N t h loc glob)

def sourceWindowStart (N A t : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) : ℕ :=
  ((A:ℤ)+sourceDisplacement N t loc glob u).toNat

end TraceReconstruction


noncomputable section


noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The unconditional literal surrogate partition: local and common-global
 pairs contribute their real selected pure lengths, on every bit assignment. -/
def sourceTreeWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → List Bool
  | 0, _, _, τ => atom τ
  | 1, bits, incoming, τ => sourceCenterWord s P T n center atom 1 bits incoming τ
  | b+2, bits, incoming, τ =>
      let loc := fun u => (bits.2.2 u).1
      let glob := bits.2.1
      coordinateWord (fun u : Fin (T (b+1)) =>
        pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) (sourceNominalPre P T b) (n b) (h b) loc glob u) ++
        sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
          (sourceScheduledShift T n (b+1) glob u)
          (integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) bits incoming) τ u) ++
        pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePostCount (T (b+1)) (sourceNominalPost P T b) (n b) (h b) loc glob u))

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Metadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metadata

Hidden metadata, fair jitter, heterogeneous emissions, independent window trials, concentration, and fit.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceGlobalCoefficient (N t : ℕ) (u : Fin N) (k : Fin ((N/4)*t)) : ℝ :=
  let v := ((globalTrialEquiv N t).symm k).1
  if v.val≤u.val ∧ u.val+v.val<N then 1 else 0

def sourceGroupCoefficient (T n : ℕ → ℕ) (b : ℕ) (u : Fin (T (b+1))) :
    WindowTrial T n (sourceScheduledTrials T n) (b+2) → ℝ
  | .inl _ => 0
  | .inr (.inl k) => sourceGlobalCoefficient (T (b+1)) (n b) u k
  | .inr (.inr (v,.inl _)) => if v=u then 1 else 0
  | .inr (.inr (_,.inr _)) => 0

end TraceReconstruction


end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simulation

Canonical and filled simulations, central fit, root words, chronology, slots, finite codes, and complete-trace decoding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical



/-- Full literal unconditioned root partition, including both members of
 every outer paired side. Its top trial count is the source's J, even or odd. -/
def sourceFullWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (τ : Bool) : List Bool :=
  pureAtomRun (sourceBlockWord s P atom b false) (n b*h b+∑i,bitIndex (bits.1 i)) ++
  sourceTreeWord s P T n h (sourceLocalCenter T n) atom (b+1) bits 0 τ ++
  pureAtomRun (sourceBlockWord s P atom b false) (n b*(h b+1)-∑i,bitIndex (bits.1 i))

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem treeChronology_length (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ) :
    (treeChronology T n g pre post b).length=Fintype.card (TreeEmission T n g b) := by
  induction b with
  | zero =>
    change 1=Fintype.card ((PEmpty × Bool) ⊕ (PEmpty ⊕ Fin 1))
    simp
  | succ b ih =>
    have hp := sum_fiber_list_length (pre b) (List.ofFn id : List (Fin (g b)))
    have hq := sum_fiber_list_length (post b) (List.ofFn id : List (Fin (g b)))
    simp only [List.length_ofFn] at hp hq
    change _=Fintype.card (((Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b))) × Bool) ⊕
      (((Fin (T b) × Bool) ⊕ (Fin (T b) × WindowFiller T b)) ⊕ (Fin (T b) × WindowLeaf T b)))
    simp only [treeChronology,treeLocalSlots,treeGlobalSlots,List.length_append,
      List.length_flatten,List.map_ofFn,Function.comp_apply,List.length_ofFn,List.length_map,List.length_cons,List.length_nil,
      Finset.sum_add_distrib,List.sum_ofFn,ih,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    rw [hp,hq]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring

theorem treeChronology_mem (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ)
    (x : TreeEmission T n g b) : x∈treeChronology T n g pre post b := by
  induction b with
  | zero =>
    rcases x with ⟨i,p⟩ | f | v
    · exact PEmpty.elim i
    · exact PEmpty.elim f
    · change Fin 1 at v
      have hv : v=0 := Subsingleton.elim _ _
      subst v; exact List.mem_singleton.mpr rfl
  | succ b ih =>
    have hc (u : Fin (T b)) (x : TreeEmission T n g (b+1))
        (hx : x∈treeGlobalSlots T n g b false (pre b) u ++ [.inr (.inl (.inl (u,false)))] ++
          (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) ++
          treeGlobalSlots T n g b true (post b) u ++ [.inr (.inl (.inl (u,true)))]) :
        x∈treeChronology T n g pre post (b+1) := by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_flatten.mpr
      exact ⟨_,List.mem_ofFn.mpr ⟨u,rfl⟩,hx⟩
    rcases x with ⟨k,p⟩ | f | v
    · rcases k with k | k | ⟨u,k⟩
      · cases p <;>
          simp [treeChronology,treeLocalSlots,List.mem_ofFn]
      · cases p
        · apply hc (pre b k)
          simp only [List.mem_append,treeGlobalSlots,List.mem_map,List.mem_filter,List.mem_ofFn]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨k,⟨⟨k,rfl⟩,by simp⟩,rfl⟩)))
        · apply hc (post b k)
          simp only [List.mem_append,treeGlobalSlots,List.mem_map,List.mem_filter,List.mem_ofFn]
          exact Or.inl (Or.inr ⟨k,⟨⟨k,rfl⟩,by simp⟩,rfl⟩)
      · apply hc u
        have hm : TreeEmission.up T n g b u (.inl (k,p))∈
            (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) := List.mem_map.mpr ⟨_,ih _,rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
    · rcases f with ⟨u,p⟩ | ⟨u,f⟩
      · cases p <;> apply hc u <;> simp
      · apply hc u
        have hm : TreeEmission.up T n g b u (.inr (.inl f))∈
            (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) := List.mem_map.mpr ⟨_,ih _,rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
    · rcases v with ⟨u,v⟩
      apply hc u
      have hm : TreeEmission.up T n g b u (.inr (.inr v))∈
          (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) := List.mem_map.mpr ⟨_,ih _,rfl⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))

theorem treeChronology_nodup (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ) :
    (treeChronology T n g pre post b).Nodup := by
  have hs : (treeChronology T n g pre post b).toFinset=Finset.univ := by
    ext x
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact treeChronology_mem T n g pre post b x
  have hh : (treeChronology T n g pre post b).toFinset.card=(treeChronology T n g pre post b).length := by
    rw [hs,Finset.card_univ,treeChronology_length]
  exact Multiset.coe_nodup.mp ((Multiset.toFinset_card_eq_card_iff_nodup
    (m := (treeChronology T n g pre post b : Multiset (TreeEmission T n g b)))).mp hh)


/-- A genuine complete chronological bijection, not an assumed layout. -/
def treeChronologyEquiv (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ) :
    Fin (treeChronology T n g pre post b).length ≃ TreeEmission T n g b :=
  List.Nodup.getEquivOfForallMemList _ (treeChronology_nodup T n g pre post b)
    (treeChronology_mem T n g pre post b)

end TraceReconstruction



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceFramedWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → List Bool
  | 0,_,_,τ => atom τ
  | b+1,bits,incoming,τ =>
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (bits.1 i) false) ++
      sourceTreeWord s P T n h center atom (b+1) bits incoming τ ++
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (bits.1 i) true)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceChronologyCode (T n : ℕ → ℕ) (b : ℕ) :
    Fin (treeChronology T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).length ≃
      EmissionSlot (SourceTrialCount T n b) (SourceFillerCount T b) (SourceLeafCount T b) :=
  (treeChronologyEquiv T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).trans
    (sourceEmissionEnum T n b).symm

def sourceFlatLeafType (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ) (b : ℕ) (incoming : ℤ) (τ : Bool)
    (bits : Fin (SourceTrialCount T n b) → Bool) (j : Fin (SourceLeafCount T b)) : Bool :=
  sourceTreeLeafBool T n s center b ((sourceAssignmentCode T n Bool b).symm bits) incoming τ (finEnumeration _ j)

def sourceFlatTrialWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (c : Bool) (j : Fin (SourceTrialCount T n b)) : List Bool :=
  sourceTrialWord s P T n h atom b (finEnumeration _ j) c

def sourceFlatFillerWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (j : Fin (SourceFillerCount T b)) : List Bool :=
  sourceFillerWord s P T n h atom b (finEnumeration _ j)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A fixed public decoder. It does not know the hidden orientations or the
 input hypothesis, and it drops rather than reveals all pairing flags. -/
def sourceOracleDecode {Side Leaf : Type} (T n : ℕ → ℕ) (b : ℕ)
    (f : Side → List Bool) (g : Leaf → List Bool) :
    ((Reports Side (SourceTrialCount T n b) × (Fin (SourceLeafCount T b) → Leaf)) ×
      (Fin (SourceFillerCount T b) → Side)) → List Bool := fun x =>
  coordinateWord (fun j => PairedMechanisms.slotDecode f g (sourceChronologyCode T n b j)
    (emissionAssignmentEquiv Side Leaf (SourceTrialCount T n b) (SourceFillerCount T b)
      (SourceLeafCount T b) (fun i => (x.1.1 i).2,x.2,x.1.2) (sourceChronologyCode T n b j)))

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The paired experiment uses the actual unseparated complete deletion
traces, and the actual normalized minimum of their mass functions. -/
def tracePairedMechanisms {m : ℕ} {q ω : ℝ} (hq : q∈Set.Icc 0 1) (hω : 0<ω)
    (U V : Fin m → List Bool) (M : ℕ) (hU : ∀j,(U j).length≤M) (hV : ∀j,(V j).length≤M)
    (hov : ∀j,ω≤listTraceOverlap q hq (U j) (V j)) : PairedMechanisms (BoundedTrace M) m where
  first j := listTraceLaw q hq (U j) M (hU j)
  second j := listTraceLaw q hq (V j) M (hV j)
  common j := FiniteLaw.commonPart _ _ (hω.trans_le ((hov j).trans (listTraceOverlap_le_ambient hq _ _ M _ _)))
  hiddenWeight _ := ω
  weight_nonneg _ := hω.le
  common_first j := FiniteLaw.commonPart_le_left _ _ _
    ((hov j).trans (listTraceOverlap_le_ambient hq _ _ M _ _))
  common_second j := FiniteLaw.commonPart_le_right _ _ _
    ((hov j).trans (listTraceOverlap_le_ambient hq _ _ M _ _))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A monomial is precisely its set of actual leaf addresses. -/
def sourceSubsetCode (T : ℕ → ℕ) (b : ℕ) :
    (Fin (SourceLeafCount T b) → Bool) ≃ Finset (WindowLeaf T b) :=
  (maskSubsetEquiv _).trans (Equiv.finsetCongr (finEnumeration _))

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceCollectionIndex (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Fin (collectionCount T n (sourceScheduledTrials T n) b v) → Fin (SourceTrialCount T n b) :=
  fun j => (finEnumeration _).symm (collectionTrial T n (sourceScheduledTrials T n) b v j)

def sourceCollectionSet (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Finset (Fin (SourceTrialCount T n b)) := Finset.univ.image (sourceCollectionIndex T n b v)

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourcePlateauCenter (T n : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | b+1 => (T (b+1)/4:ℕ)*(n b/2:ℕ)

def sourceForcedBudget (T n : ℕ → ℕ) (s b r : ℕ) (ω : ℝ) : ℝ :=
  (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*interiorLabelBudget T b r *
    ((2^s:ℕ):ℝ)^(2*(r-2^(b+1))) *
    ((2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
      binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*
        hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceOracleCoefficient {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    (Fin (SourceLeafCount T (b+1)) → Bool) → ℝ :=
  averagedCoefficient (PairedMechanisms.orientationsGiven z)
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)

def sourceSignedCoefficient {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (σ : Fin (SourceLeafCount T (b+1)) → Bool) : ℝ :=
  sourceOracleCoefficient T n s b z false σ-sourceOracleCoefficient T n s b z true σ

end TraceReconstruction

noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact finite-union metadata cost; it contains no postulated typical
 event and no independence assertion between different collections. -/
def sourceEffectiveHiddenTail (T n : ℕ → ℕ) (b : ℕ) (ω : ℝ) : ℝ :=
  ∑v : WindowCollection T b,if collectionCount T n (sourceScheduledTrials T n) b v=0 then 0 else Real.exp (-(collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^4/16)


end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal density of the source's unconditioned finite canonical oracle. -/
def sourceOracleDensity {Side Leaf : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (Z : Leaf → ℝ) (τ : Bool)
    (zx : Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) : ℝ :=
  averagedDensity (PairedMechanisms.orientationsGiven zx.1)
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ) Z zx.2

theorem sourceOracleDensity_nonneg {Side Leaf : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (Z : Leaf → ℝ) (hZ : ∀a,0 ≤ 1+Z a) (τ : Bool)
    (zx : Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) :
    0 ≤ sourceOracleDensity T n s b Z τ zx := averagedDensity_nonneg _ _ _ hZ _

theorem sourceOracleDensity_mean {Side Leaf : Type*} [Fintype Leaf] (T n : ℕ → ℕ) (s b : ℕ)
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hZ : P.expect Z=0) (τ : Bool)
    (z : Reports Side (SourceTrialCount T n (b+1))) :
    (P.product (SourceLeafCount T (b+1))).expect (fun x => sourceOracleDensity T n s b Z τ (z,x))=1 :=
  averagedDensity_mean P (PairedMechanisms.orientationsGiven z) Z hZ
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Below the genuine forced binary leaf threshold there is NO forced
 contribution; retaining even its coarse bound would lose the main exponent. -/
def sourceSharpDegreeBudget (T n : ℕ → ℕ) (s b r : ℕ) (ω η a : ℝ) : ℝ :=
  4*(3^((b+1)*r):ℕ)*
    (((SourceLeafCount T (b+1)).choose r:ℕ)*(3^((b+1)*r):ℕ)*(η^2+a^2)+
      if 2^(b+1) ≤ r then sourceForcedBudget T n s b r ω else 0)

def sourceSharpEnergyBudget (T n : ℕ → ℕ) (s b R : ℕ) (ω η a w : ℝ) : ℝ :=
  (∑r∈Finset.range R, w^(2*r)*(if r=0 then 0 else sourceSharpDegreeBudget T n s b r ω η a))+
    4*(w^2*sourceSparseCount T s b)^R/(1-w^2*sourceSparseCount T s b)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical


def sourceReferenceLaw {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P : FiniteLaw Leaf) :
    FiniteLaw (Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) :=
  M.reports.prod (P.product (SourceLeafCount T (b+1)))

theorem sourceOracleDensity_total {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hZ : P.expect Z=0) (τ : Bool) :
    (sourceReferenceLaw T n b M P).expect (sourceOracleDensity T n s b Z τ)=1 := by
  rw [sourceReferenceLaw,FiniteLaw.expect_prod]
  simp_rw [sourceOracleDensity_mean T n s b P Z hZ τ]
  exact M.reports.expect_const 1

def sourceTypicalSet {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (ω a : ℝ) :
    Finset (Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) :=
  Finset.univ.filter (fun x => SourceTypical T n s b ω a x.1)

def sourceClippingCost (T n : ℕ → ℕ) (s b k : ℕ) (ω a L : ℝ) : ℝ :=
  sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a+
    Real.sqrt (6*(4*sourceCenteredBudget T s b k L)^k)

end TraceReconstruction



end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Amplification

Oracle products, mixed powers, padding, warmup and nested template Hellinger estimates, overlap, and block assembly.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal dense substitution of the old auxiliary laws, used only for
 overlap comparison. Statistical cost is paid only for differing motif
 leaves, not the filler atoms. -/
def sourceDensePair {q E V : ℝ} (hq : q∈Set.Icc 0 1) (s : ℕ) (P : ℕ → ℕ)
    (atom : Bool → List Bool) (C : HellingerTracePair q (atom false) (atom true) E V) :
    (j : ℕ) → HellingerTracePair q (sourceBlockWord s P atom j false)
      (sourceBlockWord s P atom j true) ((sourceBlockLength P 1 j:ℝ)*E) (((2^s:ℕ):ℝ)^j*V)
  | 0 => by simpa only [sourceBlockWord,sourceBlockLength,Nat.cast_one,pow_zero,one_mul] using C
  | j+1 => by
      have D := (sourceDensePair hq s P atom C j).template hq (P j) (P j/2-1) (2^s) (prouhetBool s)
      rw [bool_word_eta] at D
      simpa only [sourceBlockWord,sourceBlockLength,Nat.cast_mul,pow_succ,
        mul_assoc,mul_left_comm,mul_comm] using D

end TraceReconstruction



end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialRates

Initial geometric parameters, moment depths, error and overlap rates, and production of the base induction pair.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

/-- One-based manuscript anchors translated once to zero-based list indices. -/
def sourceInitialAnchor (q N : ℝ) : ℤ := ((sourceInitialP q N/2:ℕ):ℤ)-1

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

def sourceInitialCount (q N : ℝ) : ℕ :=
  ⌈sourceOverlapConstant q*(initialSideCount q (sourceInitialM N):ℝ)*(sourceInitialP q N:ℝ)⌉₊

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceInitialWord (q N : ℝ) (τ : ℝ) : List Bool :=
  if hm : 4 ≤ sourceInitialM N then
    motifPeriodWord (sourceInitialOffset (sourceInitialM N) hm)
      (sourceInitialOffset_interior _ hm) (sourceInitialP q N) 300 (sourceInitialAnchor q N) τ
  else []

def sourceInitialPure (q N : ℝ) : List Bool :=
  pureAtomRun (initialPeriod (sourceInitialM N) (sourceInitialM N/2-1)) (sourceInitialP q N)

def sourceInitialError (q N : ℝ) (k : ℕ) : ℝ :=
  initialErrorCap (sourceInitialJ q N) (sourceInitialK N) (sourceInitialM N) k q
    (initialOverlapLower q) (sourceInitialWeight q k)

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LayoutRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LayoutRates

Integer block schedules, rounding, length and trial margins, sparse gaps, and forced-anchor decay.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The interior scale mass excludes the bottom window, as required by the
 sparse role count rather than the much larger total leaf count. -/
def sourceInteriorExponent (b : ℕ) (ε : ℝ) : ℝ :=
  ∑j∈Finset.range (b-1),scaleKappa b (j+2) ε

end TraceReconstruction


end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Propagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation

Moment restriction, scale margins, sharp budget closure, clipping and error propagation, and dense/warmup overlap.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceWorkSize (B D : ℕ) : ℝ :=
  totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10

end TraceReconstruction

noncomputable section

noncomputable section

noncomputable section

noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceTailDenominator (B D : ℕ) (q : ℝ) : ℝ :=
  512+9600*sourceCapEnvelope B D q*(initialOverlapLower q)⁻¹^4

def sourceTailExponent (B D : ℕ) : ℝ :=
  300*(totalScoreExponent B D+B+1)+40*sourceWorkSize B D+5

end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Restoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restoration

Restoration to honest complete traces, degradation to the requested channel, and exact-length padding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def wordOfLength {n : ℕ} (w : List Bool) (h : w.length=n) : Word n := h ▸ w.get

end TraceReconstruction

end
end
end
end

end OAI
end


