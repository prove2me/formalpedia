-- Prove2me | Definitions.Def_Q220Uk009
-- name    : Q220Uk009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:53:58.27177+00:00
-- url     : https://prove2.me/theorems/355a1cf6-c347-473e-8904-3ca854af038b
-- title:
--   Definitions bundle Q220Uk009 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 209 declarations of OpenAI's Lean: 52 definitions and 157 theorems. The definitions and types are `OAI.UniformKServer.PartitionTree.anchorIntegral`, `OAI.UniformKServer.PartitionTree.anchorPayment`, `OAI.UniformKServer.PartitionTree.anchorPayments`, `OAI.UniformKServer.PartitionTree.anchorTerm`, `OAI.UniformKServer.PartitionTree.anchorTravel`, `OAI.UniformKServer.PartitionTree.coordinateCost`, `OAI.UniformKServer.PartitionTree.frozenPotential`, `OAI.UniformKServer.PartitionTree.geometry`, `OAI.UniformKServer.PartitionTree.heavyCoefficient`, `OAI.UniformKServer.PartitionTree.heavyNear`, `OAI.UniformKServer.PartitionTree.heavyParkChange`, `OAI.UniformKServer.PartitionTree.heavySelection`, `OAI.UniformKServer.PartitionTree.heavyState`, `OAI.UniformKServer.PartitionTree.heavyValue`, `OAI.UniformKServer.PartitionTree.keyRegion`, `OAI.UniformKServer.PartitionTree.labelDecEq`, `OAI.UniformKServer.PartitionTree.labelPark`, `OAI.UniformKServer.PartitionTree.labelTracker`, `OAI.UniformKServer.PartitionTree.labelTravel`, `OAI.UniformKServer.PartitionTree.labelVertices`, `OAI.UniformKServer.PartitionTree.lawFlow`, `OAI.UniformKServer.PartitionTree.memberDrift`, `OAI.UniformKServer.PartitionTree.nearHeavy`, `OAI.UniformKServer.PartitionTree.pathEdits`, `OAI.UniformKServer.PartitionTree.pathMove`, `OAI.UniformKServer.PartitionTree.payments`, `OAI.UniformKServer.PartitionTree.refreshStep`, `OAI.UniformKServer.PartitionTree.retainedMoving`, `OAI.UniformKServer.PartitionTree.selectedDen`, `OAI.UniformKServer.PartitionTree.selectedVertices`, `OAI.UniformKServer.PartitionTree.sizeRefresh`, `OAI.UniformKServer.PartitionTree.totalAnchorTravel`, `OAI.UniformKServer.PartitionTree.totalCoordinate`, `OAI.UniformKServer.SideFiniteInput.changes`, `OAI.UniformKServer.SideFiniteInput.oldMask`, `OAI.UniformKServer.SideFiniteLedger.coefficient`, `OAI.UniformKServer.SideFiniteLedger.jump`, `OAI.UniformKServer.SideFiniteLedger.movement`, `OAI.UniformKServer.SideFiniteLedger.potential`, `OAI.UniformKServer.StarAllSteps.expense` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualAllocationBudget`, `UniformKServer_ActualAnchorDrift`, `UniformKServer_ActualAnchorDriftSum`, `UniformKServer_ActualAnchorFiltering`, `UniformKServer_ActualAnchorPotential`, `UniformKServer_ActualAnchorRelease`, `UniformKServer_ActualAnchorStep`, `UniformKServer_ActualAnchorTravel`, `UniformKServer_ActualCoordinate`, `UniformKServer_ActualCoordinateBudget`, `UniformKServer_ActualEditIntegration`, `UniformKServer_ActualRoundedStep`, `UniformKServer_ActualSizeBudget`, `UniformKServer_AnchorBudget`, `UniformKServer_AnchorFinance`, `UniformKServer_AnchorLedger`, `UniformKServer_CommonAnchorTravel`, `UniformKServer_FiniteLawFinance`, `UniformKServer_HeavyLabelParks`, `UniformKServer_LabelParkVariation`, `UniformKServer_LabelParks`, `UniformKServer_PartitionGeometry`, `UniformKServer_PartitionLaw`, `UniformKServer_PartitionMovement`, `UniformKServer_PartitionTree`, `UniformKServer_RoundingChain`, `UniformKServer_SelectedParkCoefficients`, `UniformKServer_SideFiniteInput`, `UniformKServer_SideFiniteLedger`, `UniformKServer_StarActualJumps`, `UniformKServer_StarAllSteps`, `UniformKServer_StarAllocator`, `UniformKServer_StarCaps`, `UniformKServer_StarCoarseBudgets`, `UniformKServer_StarEnergy`, `UniformKServer_StarIntegratedJumps`, `UniformKServer_StarLocalCharges`, `UniformKServer_StarMovementBudget`, `UniformKServer_StarMovementData`, `UniformKServer_StarOutputMovement`, `UniformKServer_StarPotentialBounds`, `UniformKServer_StarTrackerBudgets`, `UniformKServer_SwitchFinite`, `UniformKServer_SwitchFiniteLedger`, `UniformKServer_TreeAllocationMovement`, `UniformKServer_TreeCountData`, `UniformKServer_TreeCoverage`.
--
--   **Imports.** It imports the bundles `Q220Uk007` and `Q220Uk008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q220Uk011`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q220Uk007
import Definitions.Def_Q220Uk008

section
-- module Solutions.Q220_UK.UniformKServer_RoundingChain
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Chosen joint repairs form one adapted Markov chain on a fixed finite state
space. The choices use the old distribution and current geometric data only. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]

namespace ChainInput
variable (D : ChainInput S k X Ω)

theorem first (t : ℕ) (ω : Ω) (F : State S k→ℝ) :
    (D.joint t ω).expect (F ∘ Prod.fst)=(D.distribution t ω).law.expect F :=
  (D.step t ω (D.distribution t ω)).first F

end ChainInput
end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarCaps
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! The source's fine caps, instantiated with absolute tolerances and the
actual causal held-size epochs. Endpoint trackers are never restarted. -/
noncomputable section
namespace UniformKServer.StarCaps
open Finset StarRanks StarSchedules RankTracking RankData CoarseData FlexEstimates
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem not_wholesale_parent (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : wholesale d t ω=false) :
    parentRefresh d StarConstants.delta t ω=false := by
  have hf : ¬ AllocationEpoch.fires (EpochGeometry.scalar (epoch d StarConstants.delta t ω))
      (EpochGeometry.variation (held d t ω) (held d (t+1) ω)) (parentRefresh d StarConstants.delta t ω) := by
    simpa only [wholesale,SideReferenceSchedule.reset,epoch,decide_eq_false_iff_not] using h
  unfold AllocationEpoch.fires at hf
  exact Bool.eq_false_iff.mpr (fun hp => hf (Or.inl hp))

theorem not_wholesale_upper (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : wholesale d t ω=false) :
    upper d StarConstants.delta (t+1) ω=upper d StarConstants.delta t ω := by
  have hp := not_wholesale_parent d t ω h
  have he : ParentScale.reference (parentInput d) StarConstants.delta (t+1) ω=
      ParentScale.reference (parentInput d) StarConstants.delta t ω := by
    simpa only [parentRefresh,decide_eq_false_iff_not,not_not] using hp
  simp only [upper,ParentBeta.heldParam,ParentScale.lowerX,he]

theorem not_wholesale_factor (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (h : wholesale d t ω=false) :
    factor (epoch d StarConstants.delta (t+1) ω) k i=factor (epoch d StarConstants.delta t ω) k i := by
  have hd := SideReferenceSchedule.not_reset_dominant h
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  simp only [factor,hd]

theorem cap_step (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) (h : wholesale d t ω=false) :
    |cap d (t+1) ω i-cap d t ω i| ≤
      2*FineVariation.endpointVariation (input d i) (StarConstants.rho/EpochAlpha.ell k) t ω+
      3*coreChange (input d i) t ω := by
  rw [cap_eq,cap_eq,not_wholesale_upper d t ω h,not_wholesale_factor d t ω i h]
  exact FineVariation.cap_step _ (upper_allowed d StarConstants.delta_bounds.1 hk t ω)
    (factor_range _ k i) _ t ω

end UniformKServer.StarCaps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideFiniteInput
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Actual posterior/core inputs in a finite reveal law. Conditions describe the
 held, measurable data, not a movement conclusion. Empty and null-fiber cases
 still use the zero conventions of the conditional kernel. -/
noncomputable section
namespace UniformKServer.SideFiniteInput
open Finset UniformKServer.AdaptiveSide UniformKServer.ConditionalLaw
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def oldMask (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (post d (t+1) ω i) (d.flag t ω i)

def changes (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i, SyntheticCore.changes (d.flag t ω i) (d.flag (t+1) ω i)

theorem flag_supported (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SyntheticCore.Supported (activeFlag (d.param t ω)) (d.flag t ω) := by
  intro i hi r
  exact d.supported t ω i (by simpa [activeFlag] using hi) r

theorem errors (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    (∑ i, |oldMask d t ω i-star d t ω i|) ≤ changes d t ω ∧
    (∑ i, |input d (t+1) ω i-star d t ω i|) ≤ changes d t ω ∧
    0 ≤ (∑ i, input d (t+1) ω i)-(∑ i, star d t ω i) ∧
    (∑ i, input d (t+1) ω i)-(∑ i, star d t ω i) ≤ changes d t ω :=
  SyntheticCore.errors _ _ _ _ _ (post_range d (t+1) ω)
    (flag_supported d t ω) (flag_supported d (t+1) ω)

end UniformKServer.SideFiniteInput

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SwitchFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal causal hysteresis under finite observation laws.  The old-rule
potential is filtered on every step, before the wholesale/reset decision. -/
noncomputable section
namespace UniformKServer.SwitchFinite
open Finset UniformKServer.AlphaFiniteInput UniformKServer.SwitchTracker
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def potential (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  SwitchTracker.potential (rule d t ω) (mass d t ω) (d.deficit t ω)

def wholesale (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  if d.reset t ω then mass d (t+1) ω+d.deficit (t+1) ω else 0

def coefficient (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι × R → ℝ :=
  CoreFiltering.liftCoefficient (fun v _ => indicator (rule d t v)) (d.core.flag t) ω

theorem coefficient_bound (d : Data Ω ι R) (t : ℕ) (ω : Ω) (ir : ι × R) :
    |coefficient d t ω ir| ≤ 1 := by
  apply CoreFiltering.lift_bound _ _ (by norm_num) _ ω ir
  intro v i
  unfold indicator
  split_ifs <;> norm_num

theorem coefficient_measurable (d : Data Ω ι R) (t : ℕ) (ir : ι × R) :
    ConditionalLaw.measurable (d.core.filtration t) (fun ω => coefficient d t ω ir) := by
  apply CoreFiltering.lift_measurable
  · intro i ω v h
    dsimp only
    rw [rule_measurable d t h]
  · intro ω v h i r
    rw [d.core.flag_measurable t ω v h]

theorem flags_error (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    |mass d (t+1) ω-oldMass d t ω| ≤ changes d.core t ω := by
  unfold mass oldMass
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_sub_comm]
  exact SyntheticCore.input_difference _ _ _ (post_range d.core (t+1) ω i)

theorem frozen_change (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SwitchTracker.potential (rule d t ω) (oldMass d t ω) (d.deficit t ω)-potential d t ω =
      AdaptiveLedger.increment d.core.weight (d.core.filtration t) (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) ω+
      AdaptiveLedger.drift d.core.weight (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) (d.core.hidden (t+1)) ω := by
  unfold potential
  rw [affine,affine]
  have hx : ∀ (s : ℕ) (f : ℕ), indicator (rule d t ω)*(∑ i, SyntheticCore.input
      (post d.core s ω i) (d.core.flag f ω i)) =
      ∑ ir, CoreFiltering.liftCoefficient (fun v _ => indicator (rule d t v))
        (d.core.flag f) ω ir*AdaptiveLedger.post d.core.weight (d.core.filtration s) (d.core.hidden s) ω ir := by
    intro s f
    rw [mul_sum]
    exact CoreFiltering.masked_linear (fun v (_ : ι) => indicator (rule d t v)) (d.core.flag f)
      (AdaptiveLedger.post d.core.weight (d.core.filtration s) (d.core.hidden s)) ω
  unfold mass oldMass input oldMask
  rw [hx,hx]
  rw [show ∀ a b c : ℝ, a+c-(b+c)=a-b by intros; ring]
  simp only [AdaptiveLedger.increment,AdaptiveLedger.drift,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro ir _
  unfold coefficient
  ring

end UniformKServer.SwitchFinite

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarAllocator
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The actual causal star allocator.  At time zero it uses the true lower
requirements, avoiding an unjustified feasibility claim for the arbitrary
initial minimizer states.  All subsequent outputs are the source's two rules. -/
noncomputable section
namespace UniformKServer.StarAllocator
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) (i : ι) : 0 ≤ output d hk t ω q i :=
  (lower_nonneg d (child_allowed d hk t ω i) t ω i).trans ((feasible d hk t ω hq).1 i)

end UniformKServer.StarAllocator

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeCoverage
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The allocation serves every request and is dominated by true posterior
counts. Positive parks therefore have validity witnesses; no impossible
history is used in either conclusion. -/
noncomputable section
namespace UniformKServer.TreeCoverage
open Finset TreeRounding TreeRankData
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

theorem required (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n)
    (hcount : ∀ x, (d.filtration t).r ω x → 1 ≤ d.count t x v) :
    1 ≤ TreeAllocator.amount d hk t ω v := by
  apply le_trans _ (TreeAllocator.lower_le d hk t ω v)
  exact ConditionalRanks.required_rank_lower d.weight (d.filtration t) ω (fun x => d.count t x v)
    (fun x hx _ => hcount x hx) k (by omega) (beta d v t ω) (allowed d hk v t ω)

end UniformKServer.TreeCoverage

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeCountData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Tree-law data and guaranteed request coverage derived from a causal map to
leaves and actual legal hidden one-server trajectories. -/
noncomputable section
namespace UniformKServer.TreeCountData
open Finset TreeRounding TreeAncestry TreeLeaves
open scoped Classical
variable {X Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

theorem serves (D : HiddenFlow.Data X Ω k) (M : Map D S) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    1 ≤ TreeAllocator.amount (data D M) hk (t+1) ω (M.toLeaf (t+1) ω (D.request t ω)) :=
  TreeCoverage.required (data D M) hk (t+1) ω _ (served_count D M t ω)

end UniformKServer.TreeCountData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionTree
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The actual fixed full-prefix tree associated with the literal partition.
The alphabet, tree and independent tape domains are instance-dependent but
law- and horizon-independent (apart from a finite tape restriction). -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem same_prefix (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (p q : X)
    (hp : p∈region A D hk z t ω v) (hq : q∈region A D hk z t ω v)
    (j : Fin J) (hj : j.val<depth (shape A k J) v) :
    word A D hk z t ω p j=word A D hk z t ω q j := by
  have he := (region_prefix A D hk z t ω v p hp).symm.trans (region_prefix A D hk z t ω v q hq)
  have hw := congrArg (PrefixTree.chart (Label X A.C k) J) he
  simp only [PrefixTree.atLevel,Equiv.apply_symm_apply] at hw
  have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v
  have hf : (fun i : Fin (depth (shape A k J) v) => word A D hk z t ω p ⟨i.val,by have := i.isLt; omega⟩)=
      (fun i : Fin (depth (shape A k J) v) => word A D hk z t ω q ⟨i.val,by have := i.isLt; omega⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hw).2
  exact congrFun hf ⟨j.val,hj⟩

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionLaw
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The multiscale independent partition tape; its law is input-law independent. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset FiniteProbability
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.ixPL
attribute [local instance] OAI.UniformKServer.PartitionTree.pairPL
theorem coordinate_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k)
    (hk : 2≤k) (ω : Ω) (j : Fin J) (f : LevelTape A k N j.val→ℝ) :
    (tapeLaw A N k J).expect (fun z=>f (z j))=
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.law.expect f := by
  exact Law.expect_pi_coordinate (fun j : Fin J=>levelLaw A N k j.val) j f

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Actual prefix region geometry and the shared parked subtree capacity. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem disjoint (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (u v : Vertex (size A k J))
    (hd : depth (shape A k J) u=depth (shape A k J) v) (hne : u≠v) :
    Disjoint (region A D hk z t ω u) (region A D hk z t ω v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hne (same_ancestor (mem_filter.mp hp).2 (mem_filter.mp hq).2 hd)

theorem diameter (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (hdiam : ∀ p q : X, dist p q≤40*A.R) (p q : X)
    (hp : p∈region A D hk z t ω v) (hq : q∈region A D hk z t ω v) :
    dist p q≤40*radius A (depth (shape A k J) v) := by
  by_cases hv : v=0
  · subst v
    simpa only [depth_root,radius,pow_zero,mul_one] using hdiam p q
  · have hd := depth_positive A v hv
    have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v
    let j : Fin J := ⟨depth (shape A k J) v-1,by omega⟩
    have he := same_prefix A D hk z t ω v p q hp hq j (by dsimp [j]; omega)
    have h := LevelMap.Data.diameter ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p q he
    change dist p q≤40*(A.R*A.q^(j.val+1)) at h
    have hj : j.val+1=depth (shape A k J) v := by dsimp [j]; omega
    simpa only [hj,radius] using h

def geometry (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hdiam : ∀ p q : X, dist p q≤40*A.R) :
    ParkCapacity.Geometry (shape A k J) X where
  region := region A D hk z t ω
  nested := nested A D hk z t ω
  disjoint := disjoint A D hk z t ω
  radius := radius A
  nonneg := radius_nonneg A
  antitone := radius_antitone A
  diameter := fun v p hp q hq => diameter A D hk z t ω v hdiam p q hp hq

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarMovementData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Actual scalar bounds and epoch cases for the coefficient-one output
movement estimate.  No unproved tracker ledger occurs in these hypotheses. -/
noncomputable section
namespace UniformKServer.StarMovementData
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility StarAllocator
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem holes_one (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) (hreg : deficit d StarConstants.delta t ω/2 ≤ StarOutputData.mass d t ω) :
    AllocationOutputs.excess (StarCaps.cap d t ω) q ≤ 4*StarOutputData.mass d t ω := by
  have h := required_holes d hk t ω hq
  have he := error_rule_one d hk t ω hreg
  have hc : parentBeta d t ω+4*StarConstants.eps/EpochAlpha.ell k ≤ 4 := by
    have hb := (parent_allowed d hk t ω).2
    have hc := (eps_bound k).2
    rw [mul_div_assoc]
    linarith
  have hm := mul_le_mul_of_nonneg_right hc (mass_nonneg d t ω)
  nlinarith only [h,he,hm]

theorem holes_down (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o)
    (hreg : StarOutputData.mass d t ω ≤ deficit d StarConstants.delta t ω/2) :
    AllocationOutputs.excess (StarCaps.cap d t ω) q ≤ 4*deficit d StarConstants.delta t ω := by
  have h := required_holes d hk t ω hq
  have he := (StarCaps.dominant d hk t ω o ho).2
  have hD := (StarCaps.deficit_comparison d hk t ω o ho).1
  change parentFlex d t ω o/2 ≤ _ at hD
  change StarCaps.flex d t ω o ≤ (1+StarConstants.eps/EpochAlpha.ell k)*parentFlex d t ω o at he
  have he' : error d t ω ≤ 2*(StarConstants.eps/EpochAlpha.ell k)*deficit d StarConstants.delta t ω := by
    simp only [error,ho]
    have hh := mul_le_mul_of_nonneg_left (show parentFlex d t ω o ≤ 2*deficit d StarConstants.delta t ω by linarith) (eps_bound k).1
    nlinarith only [he,hh]
  have hb := parent_allowed d hk t ω
  have hm := mul_le_mul_of_nonneg_left hreg (show 0 ≤ parentBeta d t ω by linarith [hb.1])
  have hc : parentBeta d t ω/2+2*(StarConstants.eps/EpochAlpha.ell k) ≤ 4 := by
    linarith [hb.2,(eps_bound k).2]
  have hh := mul_le_mul_of_nonneg_right hc (deficit_nonneg d StarConstants.delta t ω)
  nlinarith only [h,he',hm,hh]

theorem side_sum (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, side d hk t ω i) ≤ 11 := (SideFiniteInput.tracker_state (sideData d hk) t ω).2.2

theorem epoch_base (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false) :
    (epoch d StarConstants.delta (t+1) ω).base=(epoch d StarConstants.delta t ω).base := by
  have hf : ¬ AllocationEpoch.fires (EpochGeometry.scalar (epoch d StarConstants.delta t ω))
      (EpochGeometry.variation (held d t ω) (held d (t+1) ω)) (parentRefresh d StarConstants.delta t ω) := by
    simpa only [StarCaps.wholesale,SideReferenceSchedule.reset,epoch,decide_eq_false_iff_not] using h
  change (EpochGeometry.update (epoch d StarConstants.delta t ω) (held d t ω) (held d (t+1) ω)
    (parentRefresh d StarConstants.delta t ω)).base=_
  rw [EpochGeometry.update,ite_eq_right hf]

theorem empty_next (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false)
    (hz : ∀ i, held d t ω i=0) : ∀ i, held d (t+1) ω i=0 := by
  have h₀ := (EpochGeometry.total_comparison (epoch_valid d StarConstants.delta t ω)).1
  have h₁ := (EpochGeometry.total_comparison (epoch_valid d StarConstants.delta (t+1) ω)).2
  rw [epoch_base d t ω h] at h₁
  have hsum : EpochGeometry.total (held d t ω)=0 := by simp [EpochGeometry.total,hz]
  rw [hsum] at h₀
  intro i
  have hi : held d (t+1) ω i ≤ EpochGeometry.total (held d (t+1) ω) :=
    single_le_sum (fun j _ => held_nonneg d (t+1) ω j) (mem_univ i)
  exact le_antisymm (by linarith) (held_nonneg d (t+1) ω i)

theorem dominant_active (d : Data Ω ι k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) : 0 < held d t ω o := by
  have hp := (EpochGeometry.dominant_spec ho).1
  have hh := (EpochGeometry.dominant_size (epoch_valid d StarConstants.delta t ω) ho).1
  linarith

theorem tag_step (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false) :
    tag d (t+1) ω=SwitchTracker.update (tag d t ω) (StarOutputData.mass d (t+1) ω) (deficit d StarConstants.delta (t+1) ω) := by
  change SwitchFinite.rule (switchData d) (t+1) ω=_
  rw [SwitchFinite.rule]
  change SwitchTracker.update (if StarCaps.wholesale d t ω then .one else tag d t ω) _ _=_
  rw [h]
  rfl

def charge (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := SwitchFinite.charge (switchData d) t ω

theorem charge_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ charge d t ω := by
  unfold charge SwitchFinite.charge
  split
  · exact le_rfl
  · exact SwitchTracker.charge_nonneg _ (mass_nonneg d (t+1) ω) (deficit_nonneg d StarConstants.delta (t+1) ω)

theorem charge_step (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false) :
    charge d t ω=SwitchTracker.charge (tag d t ω) (StarOutputData.mass d (t+1) ω) (deficit d StarConstants.delta (t+1) ω) := by
  change (if StarCaps.wholesale d t ω then 0 else _) = _
  rw [h]
  rfl

end UniformKServer.StarMovementData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarOutputMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Literal non-wholesale output movement with coefficient one on the parent.
The switch charge is the actual causal hysteresis charge. -/
noncomputable section
namespace UniformKServer.StarOutputMovement
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility StarAllocator StarMovementData
open AllocationOutputs
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def alphaMove (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  StarOutputData.mass d (t+1) ω*variation (alpha d t ω) (alpha d (t+1) ω)
def sideMove (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ℝ :=
  deficit d StarConstants.delta (t+1) ω*variation (side d hk t ω) (side d hk (t+1) ω)
def deficitMove (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  |deficit d StarConstants.delta (t+1) ω-deficit d StarConstants.delta t ω|
def expense (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ℝ :=
  alphaMove d t ω+sideMove d hk t ω+deficitMove d t ω+StarMovementData.charge d t ω

theorem parts_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    0 ≤ alphaMove d t ω ∧ 0 ≤ sideMove d hk t ω ∧ 0 ≤ deficitMove d t ω ∧
    0 ≤ StarMovementData.charge d t ω :=
  ⟨mul_nonneg (mass_nonneg d (t+1) ω) (sum_nonneg fun _ _ => abs_nonneg _),
   mul_nonneg (deficit_nonneg d StarConstants.delta (t+1) ω) (sum_nonneg fun _ _ => abs_nonneg _),
   abs_nonneg _,StarMovementData.charge_nonneg d t ω⟩

theorem one_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ)
    (hq : parentLower d (t+1) ω ≤ q₁)
    (hreg : deficit d StarConstants.delta (t+1) ω/2 ≤ StarOutputData.mass d (t+1) ω)
    (hs : (∑ i, alpha d t ω i)=1) :
    variation (one d t ω q₀) (one d (t+1) ω q₁) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have h := rule_one_movement (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)
    (alpha d t ω) (alpha d (t+1) ω) q₀ q₁ (alpha_nonneg d t ω) hs
  have hm := mul_le_mul_of_nonneg_right (holes_one d hk (t+1) ω hq hreg)
    (show 0 ≤ variation (alpha d t ω) (alpha d (t+1) ω) from sum_nonneg fun _ _ => abs_nonneg _)
  change variation (one d t ω q₀) (one d (t+1) ω q₁) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  dsimp only [expense,alphaMove] at *
  nlinarith only [h,hm,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem two_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ) (o : ι) :
    variation (two d hk t ω q₀ o) (two d hk (t+1) ω q₁ o) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have h := rule_two_movement (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)
    (side d hk t ω) (side d hk (t+1) ω) q₀ q₁ (deficit d StarConstants.delta t ω)
    (deficit d StarConstants.delta (t+1) ω) o (deficit_nonneg d StarConstants.delta t ω)
    (deficit_nonneg d StarConstants.delta (t+1) ω) (side_nonneg d hk t ω) (side_nonneg d hk (t+1) ω)
  have hm := mul_le_mul_of_nonneg_left (side_sum d hk t ω)
    (abs_nonneg (deficit d StarConstants.delta (t+1) ω-deficit d StarConstants.delta t ω))
  change variation (two d hk t ω q₀ o) (two d hk (t+1) ω q₁ o) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  dsimp only [expense,sideMove,deficitMove] at *
  nlinarith only [h,hm,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem down_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ) (o : ι)
    (hq : parentLower d (t+1) ω ≤ q₁)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some o)
    (hs : (∑ i, alpha d t ω i)=1)
    (hreg : StarOutputData.mass d (t+1) ω < deficit d StarConstants.delta (t+1) ω/2)
    (hc : StarMovementData.charge d t ω=deficit d StarConstants.delta (t+1) ω) :
    variation (one d t ω q₀) (two d hk (t+1) ω q₁ o) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have h := downcross (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω) (alpha d t ω)
    (side d hk (t+1) ω) q₀ q₁ (deficit d StarConstants.delta (t+1) ω) 4 11 o
    (alpha_nonneg d t ω) hs (deficit_nonneg d StarConstants.delta (t+1) ω)
    (side_nonneg d hk (t+1) ω) (side_sum d hk (t+1) ω) (holes_down d hk (t+1) ω hq o ho hreg.le)
  change variation (one d t ω q₀) (two d hk (t+1) ω q₁ o) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  unfold expense
  rw [←hc] at h
  nlinarith only [h,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem up_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ) (o : ι)
    (hq : parentLower d (t+1) ω ≤ q₁) (hs : (∑ i, alpha d (t+1) ω i)=1)
    (hreg : 2*deficit d StarConstants.delta (t+1) ω < StarOutputData.mass d (t+1) ω)
    (hc : StarMovementData.charge d t ω=StarOutputData.mass d (t+1) ω) :
    variation (two d hk t ω q₀ o) (one d (t+1) ω q₁) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have hreg' : deficit d StarConstants.delta (t+1) ω/2 ≤ StarOutputData.mass d (t+1) ω := by
    linarith [deficit_nonneg d StarConstants.delta (t+1) ω]
  have h := upcross (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω) (side d hk t ω)
    (alpha d (t+1) ω) q₀ q₁ (deficit d StarConstants.delta t ω) (deficit d StarConstants.delta (t+1) ω)
    (StarOutputData.mass d (t+1) ω) 4 11 o (alpha_nonneg d (t+1) ω) hs (deficit_nonneg d StarConstants.delta t ω)
    (side_nonneg d hk t ω) (side_sum d hk t ω) (holes_one d hk (t+1) ω hq hreg') (by linarith)
  change variation (two d hk t ω q₀ o) (one d (t+1) ω q₁) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  unfold expense
  rw [←hc] at h
  change variation (two d hk t ω q₀ o) (one d (t+1) ω q₁) ≤ _+_+_*StarMovementData.charge d t ω+11*deficitMove d t ω at h
  nlinarith only [h,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem rule_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ)
    (hq : parentLower d (t+1) ω ≤ q₁) (hr : StarCaps.wholesale d t ω=false) :
    variation (ruleOutput d hk t ω q₀) (ruleOutput d hk (t+1) ω q₁) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have hd := SideReferenceSchedule.not_reset_dominant hr
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none =>
    rw [ho] at hd
    simp only [ruleOutput,ho,hd]
    by_cases ha : ∃ i, 0 < held d t ω i
    · obtain ⟨i,hi⟩ := ha
      apply one_move d hk t ω q₀ q₁ hq _ (alpha_sum d t ω i hi)
      simp only [deficit,hd,zero_div]
      exact mass_nonneg d (t+1) ω
    · have hz : ∀ i, held d t ω i=0 := fun i => le_antisymm
        (le_of_not_gt (fun h => ha ⟨i,h⟩)) (held_nonneg d t ω i)
      have hn := empty_next d t ω hr hz
      have he₀ : one d t ω q₀=fun _ => 0 := funext fun i => one_inactive d hk t ω q₀ i (hz i)
      have he₁ : one d (t+1) ω q₁=fun _ => 0 := funext fun i => one_inactive d hk (t+1) ω q₁ i (hn i)
      rw [he₀,he₁]
      simp only [variation,sub_self,abs_zero,sum_const_zero]
      have hp := parts_nonneg d hk t ω
      have hv : 0 ≤ ∑ i, |StarCaps.cap d (t+1) ω i-StarCaps.cap d t ω i| := sum_nonneg fun _ _ => abs_nonneg _
      unfold expense
      linarith [abs_nonneg (q₁-q₀),hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
  | some o =>
    rw [ho] at hd
    have hs₀ := alpha_sum d t ω o (dominant_active d t ω o ho)
    have hs₁ := alpha_sum d (t+1) ω o (dominant_active d (t+1) ω o hd)
    have hstep := tag_step d t ω hr
    have hc := charge_step d t ω hr
    cases ht₀ : tag d t ω <;> cases ht₁ : tag d (t+1) ω <;>
      simp only [ruleOutput,ho,hd,ht₀,ht₁]
    · apply one_move d hk t ω q₀ q₁ hq _ hs₀
      have h := tag_valid d (t+1) ω
      simpa only [ht₁,SwitchTracker.valid] using h
    · have hh : StarOutputData.mass d (t+1) ω < deficit d StarConstants.delta (t+1) ω/2 := by
        by_contra hn
        simp only [ht₀,ht₁,SwitchTracker.update,ite_eq_right hn] at hstep
        cases hstep
      apply down_move d hk t ω q₀ q₁ o hq hd hs₀ hh
      simpa only [ht₀,SwitchTracker.charge,ite_eq_left hh] using hc
    · have hh : 2*deficit d StarConstants.delta (t+1) ω < StarOutputData.mass d (t+1) ω := by
        by_contra hn
        simp only [ht₀,ht₁,SwitchTracker.update,ite_eq_right hn] at hstep
        cases hstep
      apply up_move d hk t ω q₀ q₁ o hq hs₁ hh
      simpa only [ht₀,SwitchTracker.charge,ite_eq_left hh] using hc
    · exact two_move d hk t ω q₀ q₁ o

end UniformKServer.StarOutputMovement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarLocalCharges
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Pointwise charges which enter the actual finite-law star ledger. In
particular marking-side changes and deficit changes are not assumed free. -/
noncomputable section
namespace UniformKServer.StarLocalCharges
open Finset StarRanks StarSchedules CoarseData RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def wholesaleMass (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  if StarCaps.wholesale d t ω then (∑ i, held d t ω i)+(∑ i, held d (t+1) ω i) else 0

theorem wholesale_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ wholesaleMass d t ω := by
  unfold wholesaleMass
  split_ifs
  · exact add_nonneg (sum_nonneg fun i _ => held_nonneg d t ω i) (sum_nonneg fun i _ => held_nonneg d (t+1) ω i)
  · rfl

theorem wholesale_path (d : Data Ω ι k) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, wholesaleMass d t ω) ≤
      203*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))+
      (∑ t ∈ range H, if parentRefresh d StarConstants.delta t ω then
        EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) := by
  have h := SideReferenceSchedule.wholesale_budget (fun s i => held_nonneg d s ω i)
    (fun s => parentRefresh d StarConstants.delta s ω) H
  have hv := sum_le_sum (s:=range H) fun t _ => EpochAlphaBudget.variation_le
    (fun i => held_nonneg d t ω i) (fun i => held_nonneg d (t+1) ω i)
  change (∑ t ∈ range H, wholesaleMass d t ω) ≤ _ at h
  linarith

theorem alpha_changes (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    AlphaFiniteInput.changes (StarOutputData.alphaData d) t ω=coreChanges d t ω := by
  unfold AlphaFiniteInput.changes coreChanges coreChange SyntheticCore.changes
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change (if flags d t ω i j=flags d (t+1) ω i j then (0:ℝ) else 1)=_
  simp only [flags,eq_comm]
  rfl

theorem side_flag_formula (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) :
    StarTrackers.sideFlags d StarConstants.delta t ω i j=
      match EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
      | none => false
      | some o => if i=o then false else flags d t ω i j := by
  unfold StarTrackers.sideFlags EpochSide.active
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simp
  | some o =>
    by_cases hi : i=o
    · simp [hi]
    · by_cases ha : 0 < held d t ω i
      · simp [hi,EpochParameters.mem_active,ha]
      · have hz := le_antisymm (le_of_not_gt ha) (held_nonneg d t ω i)
        simp [hi,EpochParameters.mem_active,ha,zero_flags d t ω i hz]

theorem side_changes_same (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (hr : StarCaps.wholesale d t ω=false) :
    SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤ coreChanges d t ω := by
  have hd := SideReferenceSchedule.not_reset_dominant hr
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  unfold SideFiniteInput.changes coreChanges SyntheticCore.changes coreChange
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  change (if StarTrackers.sideFlags d StarConstants.delta t ω i j=
    StarTrackers.sideFlags d StarConstants.delta (t+1) ω i j then (0:ℝ) else 1) ≤ _
  rw [side_flag_formula,side_flag_formula,hd]
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => split_ifs <;> norm_num at *
  | some o =>
    by_cases hi : i=o
    · simp only [hi]
      split_ifs <;> norm_num at *
    · simp only [ite_eq_right hi]
      simp only [flags,eq_comm]
      exact le_rfl

theorem side_changes_size (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤
      40*((∑ i, held d t ω i)+(∑ i, held d (t+1) ω i)) := by
  have hl : SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤
      (∑ i, RankData.coreCount (flags d t ω i))+(∑ i, RankData.coreCount (flags d (t+1) ω i)) := by
    rw [←sum_add_distrib]
    unfold SideFiniteInput.changes SyntheticCore.changes RankData.coreCount
    apply sum_le_sum
    intro i _
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro j _
    change (if StarTrackers.sideFlags d StarConstants.delta t ω i j=
      StarTrackers.sideFlags d StarConstants.delta (t+1) ω i j then (0:ℝ) else 1) ≤ _
    rw [side_flag_formula,side_flag_formula]
    cases h₀ : flags d t ω i j <;> cases h₁ : flags d (t+1) ω i j <;>
      cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) <;>
      cases hn : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω) <;>
      split_ifs <;> norm_num at *
  have h₀ := sum_le_sum (s:=univ) fun i _ => CoarseBridge.core_count_bound (input d i) t ω
  have h₁ := sum_le_sum (s:=univ) fun i _ => CoarseBridge.core_count_bound (input d i) (t+1) ω
  change (∑ i, RankData.coreCount (flags d t ω i)) ≤ ∑ i, 40*held d t ω i at h₀
  change (∑ i, RankData.coreCount (flags d (t+1) ω i)) ≤ ∑ i, 40*held d (t+1) ω i at h₁
  rw [←mul_sum] at h₀ h₁
  linarith

theorem side_changes (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤
      coreChanges d t ω+40*wholesaleMass d t ω := by
  cases hr : StarCaps.wholesale d t ω
  · simpa only [wholesaleMass,hr,Bool.false_eq_true,ite_false, if_false,mul_zero,add_zero] using side_changes_same d hk t ω hr
  · have hs := side_changes_size d hk t ω
    unfold wholesaleMass
    rw [hr]
    simp only [ite_true, if_true]
    linarith [core_nonneg d t ω]

theorem deficit_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    deficit d StarConstants.delta t ω ≤ 120*∑ i, held d t ω i := by
  unfold deficit
  split
  · exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => held_nonneg d t ω i)
  · rename_i i hi
    exact (coarse_flex_bound d t ω i).trans
      (mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => held_nonneg d t ω j) (mem_univ i)) (by norm_num))

theorem deficit_same (d : Data Ω ι k) (t : ℕ) (ω : Ω) (hr : StarCaps.wholesale d t ω=false) :
    StarOutputMovement.deficitMove d t ω ≤ endpoints d sizeTolerance t ω+coreChanges d t ω := by
  have hd := SideReferenceSchedule.not_reset_dominant hr
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  unfold StarOutputMovement.deficitMove deficit
  rw [hd]
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simpa only [sub_self,abs_zero] using add_nonneg (endpoints_nonneg d sizeTolerance t ω) (core_nonneg d t ω)
  | some i =>
    apply (FineVariation.flex_step (input d i) (show RankFunctions.allowed 3 by norm_num [RankFunctions.allowed]) _ _ _).trans
    change _ ≤ (∑ j, FineVariation.endpointVariation (input d j) sizeTolerance t ω)+(∑ j, coreChange (input d j) t ω)
    rw [←sum_add_distrib]
    exact single_le_sum (f:=fun j => FineVariation.endpointVariation (input d j) sizeTolerance t ω+coreChange (input d j) t ω) (fun j _ => add_nonneg
      (sum_nonneg fun r _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (sum_nonneg fun r _ => by split_ifs <;> norm_num)) (mem_univ i)

theorem deficit_step (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    StarOutputMovement.deficitMove d t ω ≤ endpoints d sizeTolerance t ω+coreChanges d t ω+120*wholesaleMass d t ω := by
  cases hr : StarCaps.wholesale d t ω
  · simpa only [wholesaleMass,hr,Bool.false_eq_true,ite_false, if_false,mul_zero,add_zero] using deficit_same d t ω hr
  · have h := abs_sub (deficit d StarConstants.delta (t+1) ω) (deficit d StarConstants.delta t ω)
    rw [abs_of_nonneg (deficit_nonneg d _ (t+1) ω),abs_of_nonneg (deficit_nonneg d _ t ω)] at h
    change StarOutputMovement.deficitMove d t ω ≤ _ at h
    unfold wholesaleMass
    rw [hr]
    simp only [ite_true, if_true]
    linarith [deficit_bound d t ω,deficit_bound d (t+1) ω,endpoints_nonneg d sizeTolerance t ω,core_nonneg d t ω]

end UniformKServer.StarLocalCharges

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarAllSteps
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! All-time movement of the causal allocator, including its separate feasible
initial state. There is exactly one initial allowance, not one per epoch. -/
noncomputable section
namespace UniformKServer.StarAllSteps
open Finset StarRanks StarSchedules StarAllocator StarLocalCharges AllocationOutputs
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem size_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q₀ q₁ : ℝ}
    (h₀ : StarLower.parentLower d t ω ≤ q₀) (h₁ : StarLower.parentLower d (t+1) ω ≤ q₁) :
    variation (output d hk t ω q₀) (output d hk (t+1) ω q₁) ≤
      120*((∑ i, held d t ω i)+(∑ i, held d (t+1) ω i)) := by
  unfold variation
  calc
    _ ≤ ∑ i, (output d hk (t+1) ω q₁ i+output d hk t ω q₀ i) := by
      apply sum_le_sum
      intro i _
      have h := abs_sub (output d hk (t+1) ω q₁ i) (output d hk t ω q₀ i)
      simpa only [abs_of_nonneg (nonneg d hk (t+1) ω h₁ i),abs_of_nonneg (nonneg d hk t ω h₀ i)] using h
    _ ≤ ∑ i, (120*held d (t+1) ω i+120*held d t ω i) := by
      apply sum_le_sum
      intro i _
      exact add_le_add (((feasible d hk (t+1) ω h₁).2.1 i).trans (StarCaps.cap_bound d hk (t+1) ω i))
        (((feasible d hk t ω h₀).2.1 i).trans (StarCaps.cap_bound d hk t ω i))
    _ = _ := by rw [sum_add_distrib,←mul_sum,←mul_sum]; ring

def expense (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ℝ :=
  4*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+6*coreChanges d t ω+
    32*StarOutputMovement.expense d hk t ω+120*wholesaleMass d t ω+
    if t=0 then 480*(k:ℝ) else 0

theorem step (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q₀ q₁ : ℝ}
    (h₀ : StarLower.parentLower d t ω ≤ q₀) (h₁ : StarLower.parentLower d (t+1) ω ≤ q₁) :
    variation (output d hk t ω q₀) (output d hk (t+1) ω q₁) ≤ |q₁-q₀|+expense d hk t ω := by
  have hm := size_move d hk t ω h₀ h₁
  have hp := StarOutputMovement.parts_nonneg d hk t ω
  have he := endpoints_nonneg d (StarConstants.rho/EpochAlpha.ell k) t ω
  have hc := core_nonneg d t ω
  have hw := wholesale_nonneg d t ω
  have hq := abs_nonneg (q₁-q₀)
  by_cases ht : t=0
  · have hb₀ := held_sum d t ω
    have hb₁ := held_sum d (t+1) ω
    unfold expense StarOutputMovement.expense
    rw [ite_eq_left ht]
    linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
  · cases hr : StarCaps.wholesale d t ω
    · have hcap := sum_le_sum (s:=univ) fun i _ => StarCaps.cap_step d hk t ω i hr
      change variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω) ≤ _ at hcap
      simp only [sum_add_distrib,←mul_sum] at hcap
      change _ ≤ 2*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+3*coreChanges d t ω at hcap
      have h := StarOutputMovement.rule_move d hk t ω q₀ q₁ h₁ hr
      have ho : output d hk t ω q₀=ruleOutput d hk t ω q₀ := by cases t <;> simp_all [output]
      rw [ho]
      change variation (ruleOutput d hk t ω q₀) (ruleOutput d hk (t+1) ω q₁) ≤ _
      unfold expense
      rw [ite_eq_right ht]
      linarith
    · change _ ≤ |q₁-q₀|+(4*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+6*coreChanges d t ω+
        32*StarOutputMovement.expense d hk t ω+120*wholesaleMass d t ω+(if t=0 then 480*(k:ℝ) else 0))
      rw [ite_eq_right ht]
      unfold wholesaleMass StarOutputMovement.expense
      rw [hr]
      simp only [ite_true, if_true]
      linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]

end UniformKServer.StarAllSteps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideFiniteLedger
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! All-step side ledger with actual affine posterior coefficients fixed before
refresh. No posterior-ratio variation or after-refresh filtering is used. -/
noncomputable section
namespace UniformKServer.SideFiniteLedger
open Finset UniformKServer.AdaptiveSide UniformKServer.SideFiniteInput
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def potential (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AdaptiveSide.potential (d.param t ω) (input d t ω) (d.deficit t ω) (tracker d t ω)
def movement (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  d.deficit (t+1) ω*SideTracker.movement (tracker d (t+1) ω) (tracker d t ω)
def jump (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AdaptiveSide.potential (d.param (t+1) ω) (star d t ω) (d.deficit (t+1) ω) (prepared d t ω)-
    AdaptiveSide.potential (d.param t ω) (star d t ω) (d.deficit (t+1) ω) (prepared d t ω)
def coefficient (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι × R → ℝ :=
  CoreFiltering.liftCoefficient (fun v => SideLinear.bCoefficient (d.param t v) (tracker d t v))
    (d.flag t) ω

theorem coefficient_bound (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, slope (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) (ir : ι × R) :
    |coefficient d t ω ir| ≤ K := by
  apply CoreFiltering.lift_bound _ _ hK _ ω ir
  intro v i
  exact (SideLinear.bBound (d.param_valid t v) _ (tracker_state d t v) i).trans (hk t v)

theorem coefficient_measurable (d : Data Ω ι R) (t : ℕ) (ir : ι × R) :
    ConditionalLaw.measurable (d.filtration t) (fun ω => coefficient d t ω ir) := by
  apply CoreFiltering.lift_measurable
  · intro i ω v h
    dsimp only
    rw [d.param_measurable t ω v h,tracker_measurable d t h]
  · intro ω v h i r
    rw [d.flag_measurable t ω v h]

theorem frozen_change (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    AdaptiveSide.potential (d.param t ω) (oldMask d t ω) (d.deficit (t+1) ω) (tracker d t ω)-
      potential d t ω =
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω+
      SideLinear.dCoefficient (d.param t ω) (tracker d t ω)*(d.deficit (t+1) ω-d.deficit t ω) := by
  unfold potential
  rw [SideLinear.affine,SideLinear.affine]
  have hnew : oldMask d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration (t+1)) (d.hidden (t+1))) ω := rfl
  have hold : input d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration t) (d.hidden t)) ω := rfl
  rw [hnew,hold,CoreFiltering.masked_linear
    (fun v => SideLinear.bCoefficient (d.param t v) (tracker d t v)),
    CoreFiltering.masked_linear
    (fun v => SideLinear.bCoefficient (d.param t v) (tracker d t v))]
  have he : (∑ ir, coefficient d t ω ir*AdaptiveLedger.post d.weight (d.filtration (t+1)) (d.hidden (t+1)) ω ir)-
      (∑ ir, coefficient d t ω ir*AdaptiveLedger.post d.weight (d.filtration t) (d.hidden t) ω ir) =
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1)) (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1)) (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω := by
    simp only [AdaptiveLedger.increment,AdaptiveLedger.drift,←sum_add_distrib,←sum_sub_distrib]
    apply sum_congr rfl
    intro ir _
    ring
  change (∑ ir, coefficient d t ω ir*_)+_-((∑ ir, coefficient d t ω ir*_)+_)=_
  linarith

theorem step_bound (d : Data Ω ι R) {K : ℝ}
    (hk : ∀ t ω, slope (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) :
    movement d t ω ≤ potential d t ω-potential d (t+1) ω+
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω+
      (jump d t ω+2*K*changes d t ω+K*|d.deficit (t+1) ω-d.deficit t ω|) := by
  have hs := (SideFiniteInput.step d t ω).2.2.2.2.2
  have he := errors d t ω
  have ho := input_bound (d.param_valid t ω) (star d t ω) (oldMask d t ω)
    (tracker d t ω) (d.deficit (t+1) ω) (d.deficit (t+1) ω) (tracker_state d t ω)
  have hdiff : (∑ i, |star d t ω i-oldMask d t ω i|) ≤ changes d t ω := by
    simpa only [abs_sub_comm] using he.1
  have hr : 0 ≤ changes d t ω :=
    (sum_nonneg fun i _ => abs_nonneg (oldMask d t ω i-star d t ω i)).trans he.1
  have hold : AdaptiveSide.potential (d.param t ω) (star d t ω) (d.deficit (t+1) ω) (tracker d t ω)-
      AdaptiveSide.potential (d.param t ω) (oldMask d t ω) (d.deficit (t+1) ω) (tracker d t ω) ≤ K*changes d t ω := by
    have hh := (le_abs_self _).trans ho
    simp only [sub_self,abs_zero,add_zero] at hh
    have h1 := mul_le_mul_of_nonneg_left hdiff (slope_nonneg (d.param_valid t ω))
    have h2 := mul_le_mul_of_nonneg_right (hk t ω) hr
    linarith
  have hnew : slope (d.param (t+1) ω)*(∑ i, |input d (t+1) ω i-star d t ω i|) ≤ K*changes d t ω := by
    exact (mul_le_mul_of_nonneg_left he.2.1 (slope_nonneg (d.param_valid (t+1) ω))).trans
      (mul_le_mul_of_nonneg_right (hk (t+1) ω) hr)
  have hD : SideLinear.dCoefficient (d.param t ω) (tracker d t ω)*(d.deficit (t+1) ω-d.deficit t ω) ≤
      K*|d.deficit (t+1) ω-d.deficit t ω| := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      ((SideLinear.dBound (d.param_valid t ω) _ (tracker_state d t ω)).trans (hk t ω)) (abs_nonneg _)
  have hf := frozen_change d t ω
  change movement d t ω ≤ _ at hs
  dsimp only [jump,potential,movement] at *
  linarith

theorem budget (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, slope (d.param t ω) ≤ K) (H : ℕ) :
    (∑ t ∈ range H, AdaptiveLedger.expect d.weight (movement d t)) ≤
      AdaptiveLedger.expect d.weight (potential d 0)-AdaptiveLedger.expect d.weight (potential d H)+
      K*(∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => ∑ ir, |d.hidden (t+1) ω ir-d.hidden t ω ir|))+
      ∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => jump d t ω+2*K*changes d t ω+K*|d.deficit (t+1) ω-d.deficit t ω|) :=
  AdaptiveLedger.telescope d.nonneg d.filtration d.refines (coefficient d) d.hidden
    (potential d) (movement d) (fun t ω => jump d t ω+2*K*changes d t ω+K*|d.deficit (t+1) ω-d.deficit t ω|)
    hK (coefficient_bound d hK hk) (coefficient_measurable d) (step_bound d hk) H

end UniformKServer.SideFiniteLedger

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarActualJumps
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Parameter jumps of the two actual causal minimizers. -/
noncomputable section
namespace UniformKServer.StarActualJumps
open Finset StarRanks StarSchedules StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem alpha_scale (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    AlphaEmpty.scale ((alphaData d).param t ω) ≤ alphaScale k := by
  apply EpochAlphaJump.scale_bound
  exact scale_nonneg k

theorem alpha_star_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    AlphaFiniteInput.star (alphaData d) t ω i ≤ 40*held d (t+1) ω i := by
  have h : AlphaFiniteInput.star (alphaData d) t ω i ≤ AlphaFiniteInput.input (alphaData d) (t+1) ω i :=
    (SyntheticCore.core_le_new _ _ _ _ (fun i j => (AlphaFiniteInput.post_range (alphaData d) (t+1) ω i j).1) i).2
  exact h.trans (core_bound d (t+1) ω i)

theorem side_star_bound (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    SideFiniteInput.star (sideData d hk) t ω i ≤ 40*held d (t+1) ω i := by
  have h : SideFiniteInput.star (sideData d hk) t ω i ≤ SideFiniteInput.input (sideData d hk) (t+1) ω i :=
    (SyntheticCore.core_le_new _ _ _ _ (fun i j => (SideFiniteInput.post_range (sideData d hk) (t+1) ω i j).1) i).2
  exact h.trans ((StarTrackers.side_core_le d StarConstants.delta (t+1) ω i).trans (core_bound d (t+1) ω i))

theorem alpha_jump (d : Data Ω ι k) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, |AlphaFiniteLedger.jump (alphaData d) t ω|) ≤
      4100000*alphaScale k*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))+
      4400*alphaScale k*(∑ t ∈ range H, if parentRefresh d StarConstants.delta t ω then
        EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) := by
  apply EpochAlphaBudget.jump_budget (fun t i => held_nonneg d t ω i) _ (scale_nonneg k)
  · have hp := EpochAlpha.ell_one k
    apply (div_le_one (by linarith : 0 < EpochAlpha.ell k)).2
    exact le_trans (by norm_num [StarConstants.ct]) hp
  · exact fun t => (alphaData d).param_valid t ω
  · exact fun t i => (AlphaFiniteInput.valid_input (alphaData d) ω).2.1 t i
  · exact fun t i => alpha_star_bound d t ω i
  · exact fun t => AlphaFiniteInput.star_supported_old (alphaData d) t ω
  · exact fun t => AlphaFiniteInput.star_supported_new (alphaData d) t ω
  · exact fun t => (AlphaFiniteInput.step (alphaData d) t ω).2.1
  · exact fun t => (AlphaFiniteInput.step (alphaData d) t ω).2.2.2.1

theorem side_jump (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, |SideFiniteLedger.jump (sideData d hk) t ω|) ≤
      97920*sideSlope k*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))+
      480*sideSlope k*(∑ t ∈ range H, if parentRefresh d StarConstants.delta t ω then
        EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) := by
  apply EpochSideBudget.jump_budget (fun t i => held_nonneg d t ω i) _ (EpochAlpha.ell k) StarConstants.cw
    (fun t => upper d StarConstants.delta t ω)
  · intro t ht
    exact (StarCaps.not_wholesale_upper d t ω ht).symm
  · exact fun t => (sideData d hk).param_valid t ω
  · exact fun t => deficit_nonneg d StarConstants.delta (t+1) ω
  · exact fun t i => (SideFiniteInput.valid_input (sideData d hk) ω).2.2.1 t i
  · exact fun t i => side_star_bound d hk t ω i
  · exact fun t => (SideFiniteInput.step (sideData d hk) t ω).2.1
  · exact fun t => (SideFiniteInput.step (sideData d hk) t ω).2.2.2.2.1

end UniformKServer.StarActualJumps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarEnergy
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The sole law-dependent energy is the actual hidden child-count movement.
Posterior drift is derived by conditional contraction, never assumed. -/
noncomputable section
namespace UniformKServer.StarEnergy
open Finset StarRanks RankTracking CoarseData StarLocalCharges
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem hidden_move (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ ir : ι × Fin k, |(StarOutputData.alphaData d).hidden (t+1) ω ir-
      (StarOutputData.alphaData d).hidden t ω ir|)=countMove d t ω := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  change (∑ j : Fin k, |ConditionalRank.indicator (d.count (t+1) ω i) j-
    ConditionalRank.indicator (d.count t ω i) j|)=_
  have h := ConditionalRank.indicator_distance (child_bound d (t+1) ω i) (child_bound d t ω i)
  simpa only [←Fin.sum_univ_eq_sum_range] using h

end UniformKServer.StarEnergy

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarCoarseBudgets
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Fixed absolute coarse-charge constants. They carry no factor of ell. -/
noncomputable section
namespace UniformKServer.StarCoarseBudgets
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem endpoint_budget (d : Data Ω ι k) {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 1/2) (H : ℕ) :
    integral d H (endpoints d ξ) ≤ (160/ξ)*energy d H := by
  have h := sum_le_sum (s:=univ) fun i _ => FineVariation.endpoint_budget (input d i) d.weight
    (fun _ => rfl) hξ hξ' H
  simp only [Fintype.card_fin] at h
  change integral d H (fun t ω => ∑ i, FineVariation.endpointVariation (input d i) ξ t ω) ≤ _
  rw [integral_sum]
  have he : (∑ i, (160/ξ)*(totalDrift (input d i) H+(k:ℝ))) =
      (160/ξ)*((∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k) := by
    simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ]
  exact h.trans (he.le.trans (mul_le_mul_of_nonneg_left (child_allowance d H) (by positivity)))

theorem wholesale_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (wholesaleMass d) ≤ (10:ℝ)^33*energy d H := by
  have h := average_mono (fun ω => (d.positive ω).le) (wholesale_path d H)
  simp only [average_add,average_mul,average_range_sum] at h
  change integral d H (wholesaleMass d) ≤ 203*integral d H _+integral d H _ at h
  have hs := size_budget d H
  have hp := parent_budget d H
  have hn := energy_nonneg d H
  nlinarith only [h,hs,hp,hn]

theorem coarse_endpoints (d : Data Ω ι k) (H : ℕ) :
    integral d H (endpoints d sizeTolerance) ≤ 160000*energy d H := by
  have h := endpoint_budget d
    (show 0 < sizeTolerance by norm_num [sizeTolerance]) (show sizeTolerance < 1/2 by norm_num [sizeTolerance]) H
  norm_num [sizeTolerance] at h ⊢
  exact h

theorem deficit_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarOutputMovement.deficitMove d) ≤ (10:ℝ)^36*energy d H := by
  have h := integral_mono d H (deficit_step d)
  simp only [integral_add,integral_mul] at h
  have he := coarse_endpoints d H
  have hc := core_budget d H
  have hw := wholesale_budget d H
  have hn := energy_nonneg d H
  nlinarith only [h,he,hc,hw,hn]

theorem side_flags_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (SideFiniteInput.changes (StarOutputData.sideData d hk)) ≤ (10:ℝ)^35*energy d H := by
  have h := integral_mono d H (side_changes d hk)
  simp only [integral_add,integral_mul] at h
  have hc := core_budget d H
  have hw := wholesale_budget d H
  have hn := energy_nonneg d H
  nlinarith only [h,hc,hw,hn]

end UniformKServer.StarCoarseBudgets

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarIntegratedJumps
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Summed jumps and fine endpoints under one law, with a single logarithm. -/
noncomputable section
namespace UniformKServer.StarIntegratedJumps
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open StarActualJumps StarCoarseBudgets
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem fine_endpoints (d : Data Ω ι k) (H : ℕ) :
    integral d H (endpoints d (StarConstants.rho/EpochAlpha.ell k)) ≤
      (10:ℝ)^20*EpochAlpha.ell k*energy d H := by
  have h := endpoint_budget d (StarCaps.tolerance k).1 (StarCaps.tolerance k).2 H
  have he : 160/(StarConstants.rho/EpochAlpha.ell k)=(160/StarConstants.rho)*EpochAlpha.ell k := by
    rw [div_div_eq_mul_div]; ring
  rw [he] at h
  norm_num [StarConstants.rho] at h ⊢
  have hp := mul_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (EpochAlpha.ell_one k)) (energy_nonneg d H)
  nlinarith only [h,hp]

theorem alpha_abs_jump (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t ω => |AlphaFiniteLedger.jump (StarOutputData.alphaData d) t ω|) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H := by
  have h := average_mono (fun ω => (d.positive ω).le) (alpha_jump d H)
  simp only [average_add,average_mul,average_range_sum] at h
  change integral d H (fun t ω => |AlphaFiniteLedger.jump (StarOutputData.alphaData d) t ω|) ≤
    4100000*alphaScale k*integral d H _+4400*alphaScale k*integral d H _ at h
  have hs := mul_le_mul_of_nonneg_left (size_budget d H) (scale_nonneg k)
  have hp := mul_le_mul_of_nonneg_left (parent_budget d H) (scale_nonneg k)
  have hn := mul_nonneg (scale_nonneg k) (energy_nonneg d H)
  norm_num [alphaScale,StarConstants.multiplier] at h hs hp hn
  nlinarith only [h,hs,hp,hn]

theorem side_abs_jump (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (fun t ω => |SideFiniteLedger.jump (StarOutputData.sideData d hk) t ω|) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H := by
  have h := average_mono (fun ω => (d.positive ω).le) (side_jump d hk H)
  simp only [average_add,average_mul,average_range_sum] at h
  change integral d H (fun t ω => |SideFiniteLedger.jump (StarOutputData.sideData d hk) t ω|) ≤
    97920*sideSlope k*integral d H _+480*sideSlope k*integral d H _ at h
  have hs := mul_le_mul_of_nonneg_left (size_budget d H) (slope_nonneg k)
  have hp := mul_le_mul_of_nonneg_left (parent_budget d H) (slope_nonneg k)
  have hb := mul_le_mul_of_nonneg_right (slope_bound k) (energy_nonneg d H)
  have hn := mul_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (EpochAlpha.ell_one k)) (energy_nonneg d H)
  nlinarith only [h,hs,hp,hb,hn]

theorem alpha_jump_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (AlphaFiniteLedger.jump (StarOutputData.alphaData d)) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H :=
  (integral_mono d H (fun _ _ => le_abs_self _)).trans (alpha_abs_jump d H)

theorem side_jump_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (SideFiniteLedger.jump (StarOutputData.sideData d hk)) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H :=
  (integral_mono d H (fun _ _ => le_abs_self _)).trans (side_abs_jump d hk H)

end UniformKServer.StarIntegratedJumps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarPotentialBounds
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Law- and horizon-independent endpoint bounds for the actual three
persistent star potentials. -/
noncomputable section
namespace UniformKServer.StarPotentialBounds
open Finset StarRanks StarSchedules StarOutputData StarLocalCharges StarActualJumps RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem mass_size (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    StarOutputData.mass d t ω ≤ 40*∑ i, held d t ω i := by
  unfold StarOutputData.mass
  rw [mul_sum]
  exact sum_le_sum fun i _ => core_bound d t ω i

theorem mass_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) : StarOutputData.mass d t ω ≤ 80*k := by
  linarith [mass_size d t ω,held_sum d t ω]

theorem deficit_k (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    deficit d StarConstants.delta t ω ≤ 240*k := by
  linarith [deficit_bound d t ω,held_sum d t ω]

theorem alpha_potential (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    |AlphaFiniteLedger.potential (alphaData d) t ω| ≤ 1200*alphaScale k*k := by
  have h := AlphaEmpty.input_bound ((alphaData d).param_valid t ω)
    (AlphaFiniteInput.input (alphaData d) t ω) (fun _ => 0)
    (AlphaFiniteInput.alpha (alphaData d) t ω) (AlphaFiniteInput.alpha_state (alphaData d) t ω)
  simp only [AlphaEmpty.potential_zero,sub_zero,
    abs_of_nonneg (AlphaFiniteInput.input_nonneg (alphaData d) t ω _)] at h
  change |AlphaFiniteLedger.potential (alphaData d) t ω| ≤
    15*AlphaEmpty.scale ((alphaData d).param t ω)*StarOutputData.mass d t ω at h
  have hs := mul_le_mul_of_nonneg_right (alpha_scale d t ω) (mass_nonneg d t ω)
  have hm := mul_le_mul_of_nonneg_left (mass_bound d t ω) (scale_nonneg k)
  nlinarith only [h,hs,hm]

theorem side_mass (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, SideFiniteInput.input (sideData d hk) t ω i) ≤ 80*k := by
  exact (sum_le_sum (fun i _ => StarTrackers.side_core_le d StarConstants.delta t ω i)).trans (mass_bound d t ω)

theorem side_potential (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    |SideFiniteLedger.potential (sideData d hk) t ω| ≤ 320*sideSlope k*k := by
  have h := AdaptiveSide.input_bound ((sideData d hk).param_valid t ω)
    (SideFiniteInput.input (sideData d hk) t ω) (fun _ => 0)
    (SideFiniteInput.tracker (sideData d hk) t ω) (deficit d StarConstants.delta t ω) 0
    (SideFiniteInput.tracker_state (sideData d hk) t ω)
  simp only [SideLinear.zero,sub_zero,
    abs_of_nonneg (SideFiniteInput.input_nonneg (sideData d hk) t ω _),
    abs_of_nonneg (deficit_nonneg d StarConstants.delta t ω)] at h
  change |SideFiniteLedger.potential (sideData d hk) t ω| ≤ sideSlope k*
    ((∑ i, SideFiniteInput.input (sideData d hk) t ω i)+deficit d StarConstants.delta t ω) at h
  have hm := mul_le_mul_of_nonneg_left (add_le_add (side_mass d hk t ω) (deficit_k d t ω)) (slope_nonneg k)
  nlinarith only [h,hm]

theorem switch_potential (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    SwitchFinite.potential (StarAllocator.switchData d) t ω ∈ Set.Icc (0:ℝ) (240*k) := by
  change SwitchTracker.potential (StarAllocator.tag d t ω) (StarOutputData.mass d t ω) (deficit d StarConstants.delta t ω) ∈ _
  cases StarAllocator.tag d t ω
  · exact ⟨deficit_nonneg d StarConstants.delta t ω,deficit_k d t ω⟩
  · exact ⟨mass_nonneg d t ω,(mass_bound d t ω).trans (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)⟩

theorem switch_wholesale (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    SwitchFinite.wholesale (StarAllocator.switchData d) t ω ≤ 160*wholesaleMass d t ω := by
  unfold SwitchFinite.wholesale
  change (if StarCaps.wholesale d t ω then StarOutputData.mass d (t+1) ω+deficit d StarConstants.delta (t+1) ω else 0) ≤ _
  unfold wholesaleMass
  split_ifs
  · linarith [mass_size d (t+1) ω,deficit_bound d (t+1) ω,
      sum_nonneg (s:=univ) (fun i _ => held_nonneg d t ω i)]
  · norm_num

end UniformKServer.StarPotentialBounds

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SwitchFiniteLedger
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! All-step switch charge ledger with BEFORE-refresh measurable coefficients.
No stopping-event conditioning or posterior-ratio variation is used. -/
noncomputable section
namespace UniformKServer.SwitchFiniteLedger
open Finset UniformKServer.SwitchFinite
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def expense (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AlphaFiniteInput.changes d.core t ω+|d.deficit (t+1) ω-d.deficit t ω|+wholesale d t ω

theorem pointwise (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    charge d t ω/2 ≤ SwitchTracker.potential (rule d t ω) (oldMass d t ω) (d.deficit t ω)-
      potential d (t+1) ω+expense d t ω := by
  have hc : 0 ≤ AlphaFiniteInput.changes d.core t ω :=
    sum_nonneg fun i _ => SyntheticCore.changes_nonneg _ _
  have hd := abs_nonneg (d.deficit (t+1) ω-d.deficit t ω)
  by_cases hr : d.reset t ω=true
  · have hh := SwitchTracker.wholesale_step (rule d t ω) (rule d (t+1) ω)
      (oldMass_nonneg d t ω) (d.nonneg t ω)
      (Snew:=SwitchFinite.mass d (t+1) ω) (Dnew:=d.deficit (t+1) ω)
      (C:=SwitchFinite.mass d (t+1) ω+d.deficit (t+1) ω)
      (le_add_of_nonneg_right (d.nonneg (t+1) ω))
      (le_add_of_nonneg_left (mass_nonneg d (t+1) ω))
    change potential d (t+1) ω-_ ≤ _ at hh
    simp only [charge,expense,wholesale,ite_eq_left hr,zero_div]
    linarith
  · have hh := SwitchTracker.nonwholesale_step (rule d t ω)
      (oldMass d t ω) (d.deficit t ω) (SwitchFinite.mass d (t+1) ω) (d.deficit (t+1) ω)
      (AlphaFiniteInput.changes d.core t ω) (flags_error d t ω)
    have he : rule d (t+1) ω=SwitchTracker.update (rule d t ω) (SwitchFinite.mass d (t+1) ω) (d.deficit (t+1) ω) := by
      simp only [rule,ite_eq_right hr]
    rw [←he] at hh
    change potential d (t+1) ω-_ ≤ _ at hh
    simp only [charge,expense,wholesale,ite_eq_right hr,add_zero]
    linarith

theorem step_bound (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    charge d t ω/2 ≤ potential d t ω-potential d (t+1) ω+
      AdaptiveLedger.increment d.core.weight (d.core.filtration t) (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) ω+
      AdaptiveLedger.drift d.core.weight (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) (d.core.hidden (t+1)) ω+expense d t ω := by
  linarith [pointwise d t ω,frozen_change d t ω]

theorem budget (d : Data Ω ι R) (H : ℕ) :
    (∑ t ∈ range H, AdaptiveLedger.expect d.core.weight (fun ω => charge d t ω/2)) ≤
      AdaptiveLedger.expect d.core.weight (potential d 0)-AdaptiveLedger.expect d.core.weight (potential d H)+
      (∑ t ∈ range H, AdaptiveLedger.expect d.core.weight
        (fun ω => ∑ ir, |d.core.hidden (t+1) ω ir-d.core.hidden t ω ir|))+
      ∑ t ∈ range H, AdaptiveLedger.expect d.core.weight (expense d t) := by
  simpa only [one_mul] using AdaptiveLedger.telescope d.core.nonneg d.core.filtration d.core.refines
    (coefficient d) d.core.hidden (potential d) (fun t ω => charge d t ω/2) (expense d)
    (by norm_num : (0:ℝ)≤1) (coefficient_bound d) (coefficient_measurable d) (step_bound d) H

end UniformKServer.SwitchFiniteLedger

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarTrackerBudgets
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Actual minimizer and hysteresis budgets, composed from their all-step
filtering identities. The logarithmic slope is used only on coarse data. -/
noncomputable section
namespace UniformKServer.StarTrackerBudgets
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open StarActualJumps StarCoarseBudgets StarIntegratedJumps StarPotentialBounds StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem alpha_ledger (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarOutputMovement.alphaMove d) ≤ 2400*alphaScale k*k+
      15*alphaScale k*cost d H+integral d H (AlphaFiniteLedger.jump (alphaData d))+
      (30*alphaScale k+4)*integral d H (coreChanges d) := by
  have h := AlphaFiniteLedger.budget (alphaData d) (scale_nonneg k) (alpha_scale d) H
  simp only [hidden_move] at h
  change integral d H (StarOutputMovement.alphaMove d) ≤
    average d.weight (AlphaFiniteLedger.potential (alphaData d) 0)-
    average d.weight (AlphaFiniteLedger.potential (alphaData d) H)+15*alphaScale k*cost d H+
    integral d H (fun t ω => AlphaFiniteLedger.jump (alphaData d) t ω+
      (30*alphaScale k+4)*AlphaFiniteInput.changes (alphaData d) t ω) at h
  simp only [alpha_changes,integral_add,integral_mul] at h
  have h₀ := (average_interval d (alpha_potential d 0)).2
  have hH := (average_interval d (alpha_potential d H)).1
  linarith only [h,h₀,hH]

theorem side_ledger (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (StarOutputMovement.sideMove d hk) ≤ 640*sideSlope k*k+
      sideSlope k*cost d H+integral d H (SideFiniteLedger.jump (sideData d hk))+
      2*sideSlope k*integral d H (SideFiniteInput.changes (sideData d hk))+
      sideSlope k*integral d H (StarOutputMovement.deficitMove d) := by
  have h := SideFiniteLedger.budget (sideData d hk) (slope_nonneg k) (fun _ _ => le_rfl) H
  have hh (t : ℕ) (ω : Ω) : (∑ ir, |(sideData d hk).hidden (t+1) ω ir-(sideData d hk).hidden t ω ir|)=countMove d t ω :=
    hidden_move d t ω
  simp only [hh] at h
  change integral d H (StarOutputMovement.sideMove d hk) ≤
    average d.weight (SideFiniteLedger.potential (sideData d hk) 0)-
    average d.weight (SideFiniteLedger.potential (sideData d hk) H)+sideSlope k*cost d H+
    integral d H (fun t ω => SideFiniteLedger.jump (sideData d hk) t ω+
      2*sideSlope k*SideFiniteInput.changes (sideData d hk) t ω+
      sideSlope k*StarOutputMovement.deficitMove d t ω) at h
  simp only [integral_add,integral_mul] at h
  have h₀ := (average_interval d (side_potential d hk 0)).2
  have hH := (average_interval d (side_potential d hk H)).1
  linarith only [h,h₀,hH]

theorem switch_ledger (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarMovementData.charge d) ≤ 480*k+2*cost d H+
      2*integral d H (coreChanges d)+2*integral d H (StarOutputMovement.deficitMove d)+
      320*integral d H (wholesaleMass d) := by
  have h := SwitchFiniteLedger.budget (StarAllocator.switchData d) H
  have hh (t : ℕ) (ω : Ω) : (∑ ir, |(StarAllocator.switchData d).core.hidden (t+1) ω ir-
      (StarAllocator.switchData d).core.hidden t ω ir|)=countMove d t ω := hidden_move d t ω
  simp only [hh] at h
  change integral d H (fun t ω => StarMovementData.charge d t ω/2) ≤
    average d.weight (SwitchFinite.potential (StarAllocator.switchData d) 0)-
    average d.weight (SwitchFinite.potential (StarAllocator.switchData d) H)+cost d H+
    integral d H (SwitchFiniteLedger.expense (StarAllocator.switchData d)) at h
  have he := integral_mono d H (fun t ω => show SwitchFiniteLedger.expense (StarAllocator.switchData d) t ω ≤
      coreChanges d t ω+StarOutputMovement.deficitMove d t ω+160*wholesaleMass d t ω from by
    unfold SwitchFiniteLedger.expense
    change AlphaFiniteInput.changes (alphaData d) t ω + StarOutputMovement.deficitMove d t ω +
      SwitchFinite.wholesale (StarAllocator.switchData d) t ω ≤ _
    rw [alpha_changes]
    exact add_le_add le_rfl (switch_wholesale d t ω))
  simp only [integral_add,integral_mul] at he
  have h₀ : average d.weight (SwitchFinite.potential (StarAllocator.switchData d) 0) ≤ 240*k := by
    rw [←average_const d.weight d.total (240*k)]
    exact average_mono (fun ω => (d.positive ω).le) (fun ω => (switch_potential d 0 ω).2)
  have hH : 0 ≤ average d.weight (SwitchFinite.potential (StarAllocator.switchData d) H) :=
    sum_nonneg fun ω _ => mul_nonneg (d.positive ω).le (switch_potential d H ω).1
  have hm : integral d H (fun t ω => StarMovementData.charge d t ω/2)=
      (1/2)*integral d H (StarMovementData.charge d) := by
    simp only [div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,integral_mul]
    ring
  rw [hm] at h
  linarith only [h,he,h₀,hH]

theorem alpha_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarOutputMovement.alphaMove d) ≤ (10:ℝ)^58*EpochAlpha.ell k*energy d H := by
  have h := alpha_ledger d H
  have he := EpochAlpha.ell_one k
  have hc := mul_le_mul_of_nonneg_left (cost_le_energy d H) (scale_nonneg k)
  have hk := mul_le_mul_of_nonneg_left ((allowance_bounds ι k).2.1.trans (allowance_le_energy d H)) (scale_nonneg k)
  have hf := mul_le_mul_of_nonneg_left (core_budget d H) (show 0 ≤ 30*alphaScale k+4 by positivity [scale_nonneg k])
  have hj := alpha_jump_budget d H
  have hn := mul_le_mul_of_nonneg_right he (energy_nonneg d H)
  norm_num [alphaScale,StarConstants.multiplier] at h hc hk hf
  nlinarith only [h,hc,hk,hf,hj,hn,energy_nonneg d H]

theorem side_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (StarOutputMovement.sideMove d hk) ≤ (10:ℝ)^58*EpochAlpha.ell k*energy d H := by
  have h := side_ledger d hk H
  have hc := mul_le_mul_of_nonneg_left (cost_le_energy d H) (slope_nonneg k)
  have hk' := mul_le_mul_of_nonneg_left ((allowance_bounds ι k).2.1.trans (allowance_le_energy d H)) (slope_nonneg k)
  have hf := mul_le_mul_of_nonneg_left (side_flags_budget d hk H) (slope_nonneg k)
  have hd := mul_le_mul_of_nonneg_left (deficit_budget d H) (slope_nonneg k)
  have hj := side_jump_budget d hk H
  have hb := mul_le_mul_of_nonneg_right (slope_bound k) (energy_nonneg d H)
  have hn := mul_le_mul_of_nonneg_right (EpochAlpha.ell_one k) (energy_nonneg d H)
  nlinarith only [h,hc,hk',hf,hd,hj,hb,hn,energy_nonneg d H]

theorem switch_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarMovementData.charge d) ≤ (10:ℝ)^38*energy d H := by
  have h := switch_ledger d H
  have hk := (allowance_bounds ι k).2.1.trans (allowance_le_energy d H)
  nlinarith only [h,hk,cost_le_energy d H,core_budget d H,deficit_budget d H,
    wholesale_budget d H,energy_nonneg d H]

end UniformKServer.StarTrackerBudgets

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarMovementBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! The complete actual local movement theorem. Parent movement has coefficient
one; the absolute large coefficient multiplies only the hidden count movement.
The additive allowance is independent of both the law and the horizon. -/
noncomputable section
namespace UniformKServer.StarMovementBudget
open Finset StarRanks StarSchedules StarEnergy StarLocalCharges StarTrackerBudgets
open StarCoarseBudgets StarIntegratedJumps AllocationOutputs RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem expense_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (StarAllSteps.expense d hk) ≤ (10:ℝ)^63*EpochAlpha.ell k*energy d H := by
  change integral d H (fun t ω => 4*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+
    6*coreChanges d t ω+32*(StarOutputMovement.alphaMove d t ω+
    StarOutputMovement.sideMove d hk t ω+StarOutputMovement.deficitMove d t ω+
    StarMovementData.charge d t ω)+120*wholesaleMass d t ω+
    if t=0 then 480*(k:ℝ) else 0) ≤ _
  simp only [integral_add,integral_mul]
  have h₀ := initial_budget d H
  have he := fine_endpoints d H
  have hc := core_budget d H
  have ha := alpha_budget d H
  have hs := side_budget d hk H
  have hd := deficit_budget d H
  have hw := wholesale_budget d H
  have ht := switch_budget d H
  have hk' := (allowance_bounds ι k).2.1.trans (allowance_le_energy d H)
  have hn := mul_le_mul_of_nonneg_right (EpochAlpha.ell_one k) (energy_nonneg d H)
  nlinarith only [h₀,he,hc,ha,hs,hd,hw,ht,hk',hn,energy_nonneg d H]

theorem movement (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) (q : ℕ → Ω → ℝ)
    (hq : ∀ t ω, StarLower.parentLower d t ω ≤ q t ω) :
    integral d H (fun t ω => variation (StarAllocator.output d hk t ω (q t ω))
      (StarAllocator.output d hk (t+1) ω (q (t+1) ω))) ≤
    integral d H (fun t ω => |q (t+1) ω-q t ω|)+
      (10:ℝ)^63*EpochAlpha.ell k*cost d H+
      (10:ℝ)^63*EpochAlpha.ell k*allowance ι k := by
  have h := integral_mono d H (fun t ω => StarAllSteps.step d hk t ω (hq t ω) (hq (t+1) ω))
  simp only [integral_add] at h
  have hb := expense_budget d hk H
  unfold energy at hb
  linarith only [h,hb]

end UniformKServer.StarMovementBudget

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeAllocationMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                             
section

/-! Global allocation movement with an absolute, degree/depth independent
coefficient. The finite additive term is displayed as a function of the fixed
tree, its radii and k, not of a law or a horizon. -/
noncomputable section
namespace UniformKServer.TreeAllocationMovement
open Finset TreeRounding TreeRankData TreeAllocator RankTracking
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def nodeMove (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (v : Vertex n) : ℝ :=
  integral d H (fun t ω => |amount d hk (t+1) ω v-amount d hk t ω v|)

def movement (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (w : Vertex n → ℝ) : ℝ :=
  ∑ v, if v=0 then 0 else w (S.parent v)*nodeMove d hk H v

theorem local_movement (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (v : Vertex n) :
    (∑ i : Children S v, nodeMove d hk H i.val) ≤ nodeMove d hk H v+
      (10:ℝ)^63*EpochAlpha.ell k*(∑ i : Children S v, hiddenMove d H i.val)+
      (10:ℝ)^63*EpochAlpha.ell k*StarEnergy.allowance (Children S v) k := by
  have h := StarMovementBudget.movement (TreeRankData.star d v) hk H (fun t ω => amount d hk t ω v)
    (fun t ω => parent_le d hk t ω v)
  have hop (t : ℕ) (ω : Ω) :
      StarAllocator.output (TreeRankData.star d v) hk t ω (amount d hk t ω v)=fun i => amount d hk t ω i.val :=
    funext fun i => (child d hk t ω v i).symm
  simp only [hop,AllocationOutputs.variation,StarEnergy.cost,
    StarEnergy.integral_sum] at h
  unfold StarEnergy.countMove at h
  simp only [StarEnergy.integral_sum] at h
  exact h

theorem node_nonneg (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (v : Vertex n) :
    0 ≤ nodeMove d hk H v := integral_nonneg d H fun _ _ => abs_nonneg _

theorem root_move (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) : nodeMove d hk H 0=0 := by
  simp [nodeMove,integral,TreeAllocator.root,average]

theorem movement_nonneg (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (w : Vertex n → ℝ)
    (hw : ∀ v, 0 ≤ w v) : 0 ≤ movement d hk H w := by
  apply sum_nonneg
  intro v _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw _) (node_nonneg d hk H v)

theorem global_movement (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (w : Vertex n → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hsep : ∀ v, v ≠ 0 → 22*w v ≤ w (S.parent v)) :
    movement d hk H w ≤ 2*(10:ℝ)^63*EpochAlpha.ell k*hiddenCost d H w+
      2*(10:ℝ)^63*EpochAlpha.ell k*allowance S k w := by
  have h := sum_le_sum (s:=univ) (fun v _ => mul_le_mul_of_nonneg_left (local_movement d hk H v) (hw v))
  have hrewrite : (∑ v, w v*(nodeMove d hk H v+
      (10:ℝ)^63*EpochAlpha.ell k*(∑ i : Children S v, hiddenMove d H i.val)+
      (10:ℝ)^63*EpochAlpha.ell k*StarEnergy.allowance (Children S v) k)) =
      (∑ v, w v*nodeMove d hk H v)+(10:ℝ)^63*EpochAlpha.ell k*hiddenCost d H w+
      (10:ℝ)^63*EpochAlpha.ell k*allowance S k w := by
    simp only [mul_add,mul_left_comm (w _),sum_add_distrib,←mul_sum]
    rw [weighted_children]
    rfl
  rw [weighted_children,hrewrite] at h
  have hs := weight_separation S w (nodeMove d hk H) hsep (node_nonneg d hk H) (root_move d hk H)
  change 22*(∑ v,w v*nodeMove d hk H v) ≤ movement d hk H w at hs
  change movement d hk H w ≤ _ at h
  have hn := movement_nonneg d hk H w hw
  linarith only [h,hs,hn]

end UniformKServer.TreeAllocationMovement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Movement of the actual allocation on the actual common tree, reduced to
literal coordinate-key edits. All addends are uniform in hidden law/horizon. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def coordinateCost (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k,∑ i : Fin J,radius A i.val*PrefixMovement.diff
    (word A D hk z (t+1) ω (D.position (t+1) ω a) i)
    (word A D hk z t ω (D.position t ω a) i)

theorem pointwise_hidden (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ v : Vertex (size A k J), if v=0 then 0 else weight A ((shape A k J).parent v)*
      |((TreeCountData.data D (map A D hk z)).count (t+1) ω v:ℝ)-
       (TreeCountData.data D (map A D hk z)).count t ω v|)≤
    4*coordinateCost A D hk z t ω := by
  have h := PrefixMovement.count_variation
    (fun a => word A D hk z (t+1) ω (D.position (t+1) ω a))
    (fun a => word A D hk z t ω (D.position t ω a))
    (radius A) (radius_nonneg A) (fun d => by
      have := radius_step A d
      have := radius_nonneg A (d+1)
      linarith)
  change (∑ v : Vertex (size A k J),PrefixMovement.edgeWeight (radius A) (depth (shape A k J) v)*
    |((TreeCountData.data D (map A D hk z)).count (t+1) ω v:ℝ)-
       (TreeCountData.data D (map A D hk z)).count t ω v|)≤_ at h
  refine Eq.trans_le ?_ h
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · subst v
    rw [depth_root]
    simp [PrefixMovement.edgeWeight]
  · rw [ite_eq_right hv,PrefixMovement.edgeWeight,ite_eq_right (Nat.ne_of_gt (depth_positive A v hv))]
    simp only [weight,depth_child v hv,Nat.add_sub_cancel]

theorem hidden_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) :
    hiddenCost (TreeCountData.data D (map A D hk z)) H (weight A)≤
    4*integral (TreeCountData.data D (map A D hk z)) H (coordinateCost A D hk z) := by
  let d := TreeCountData.data D (map A D hk z)
  have h := sum_le_sum (s:=range H) (fun t _ => PilotEdits.average_mono D.weight _ _
    (fun ω => (D.positive ω).le) (pointwise_hidden A D hk z t))
  change (∑ t∈range H,∑ ω,D.weight ω*(∑ v : Vertex (size A k J),if v=0 then 0 else
    weight A ((shape A k J).parent v)*|(d.count (t+1) ω v:ℝ)-d.count t ω v|))≤_ at h
  have he : hiddenCost d H (weight A)=
    ∑ t∈range H,∑ ω,D.weight ω*(∑ v : Vertex (size A k J),if v=0 then 0 else
      weight A ((shape A k J).parent v)*|(d.count (t+1) ω v:ℝ)-d.count t ω v|) := by
    have hv (v : Vertex (size A k J)) :
        (if v=0 then 0 else weight A ((shape A k J).parent v)*hiddenMove d H v)=
        ∑ t∈range H,∑ ω,D.weight ω*(if v=0 then 0 else
          weight A ((shape A k J).parent v)*|(d.count (t+1) ω v:ℝ)-d.count t ω v|) := by
      by_cases hz : v=0
      · simp only [hz,ite_true, if_true,mul_zero,sum_const_zero]
      · simp only [hz,ite_false, if_false,hiddenMove,integral,RankTracking.average,mul_sum]
        apply sum_congr rfl
        intro t _
        apply sum_congr rfl
        intro ω _
        change _*(D.weight ω*_)=D.weight ω*(_*_)
        ring
    simp only [hiddenCost,hv]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    rw [sum_comm]
    apply sum_congr rfl
    intro ω _
    rw [mul_sum]
  rw [he]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [integral,RankTracking.average,PilotEdits.average,mul_sum]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro ω _
  change (4:ℝ)*(D.weight ω*_)=D.weight ω*(4*_)
  ring

theorem actual_movement (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) :
    movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A)≤
      8*(10:ℝ)^63*EpochAlpha.ell k*
        integral (TreeCountData.data D (map A D hk z)) H (coordinateCost A D hk z)+
      2*(10:ℝ)^63*EpochAlpha.ell k*allowance (shape A k J) k (weight A) := by
  have h := global_movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A)
    (fun v => radius_nonneg A _) (weight_separated A)
  have hc := mul_le_mul_of_nonneg_left (hidden_bound A D hk z H)
    (show 0≤2*(10:ℝ)^63*EpochAlpha.ell k by
      have := EpochAlpha.ell_one k; positivity)
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualCoordinate
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Literal coordinate-key motion split into actual edits and the one mover. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.ixAC
local instance pairAC_r76ef31_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
def pathEdits (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k,∑ j : Fin J,GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
    (word A D hk z (t+1) ω (D.position t ω a) j) (word A D hk z t ω (D.position t ω a) j)

def pathMove (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
    (word A D hk z (t+1) ω (D.request t ω) j)
    (word A D hk z (t+1) ω (D.position t ω (D.chosen t ω)) j)

theorem coordinate_split (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    A.q*coordinateCost A D hk z t ω≤pathEdits A D hk z t ω+pathMove A D hk z t ω := by
  have hr (j : Fin J) : A.q*radius A j.val=GeometricMass.radius A.R A.q j.val := by
    unfold radius GeometricMass.radius
    rw [pow_succ]
    ring
  have h1 := sum_le_sum (fun a (_ : a∈(univ : Finset (Fin k)))=>
    sum_le_sum (fun j (_ : j∈(univ : Finset (Fin J)))=>
      mul_le_mul_of_nonneg_left (diff_triangle
        (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
        (word A D hk z (t+1) ω (D.position t ω a) j)
        (word A D hk z t ω (D.position t ω a) j))
        (GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j.val).le))
  have he (a : Fin k) : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
      (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
      (word A D hk z (t+1) ω (D.position t ω a) j))=
      if a=D.chosen t ω then pathMove A D hk z t ω else 0 := by
    rw [D.update]
    split_ifs with ha
    · subst a; rfl
    · simp [PrefixMovement.diff]
  simp only [mul_add,sum_add_distrib,he,sum_ite_eq',mem_univ,ite_true, if_true] at h1
  unfold coordinateCost
  simp only [mul_sum,←mul_assoc,hr]
  dsimp only [pathEdits] at *
  linarith only [h1]

theorem move_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) :
    (tapeLaw A N k J).expect (fun z=>pathMove A D hk z n.val ω)≤
      (A.input (N:=N) (J:=J) D hk ω).coefficient*(1+Real.log k)*
        dist (D.request n.val ω) (D.position n.val ω (D.chosen n.val ω)) := by
  unfold pathMove
  rw [Law.expect_sum]
  simp only [Law.expect_mul]
  have he (j : Fin J) :
      (tapeLaw A N k J).expect (fun z=>PrefixMovement.diff
        (word A D hk z (n.val+1) ω (D.request n.val ω) j)
        (word A D hk z (n.val+1) ω (D.position n.val ω (D.chosen n.val ω)) j))=
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).separation n
          (D.position n.val ω (D.chosen n.val ω)) := by
    change (tapeLaw A N k J).expect (fun z=>FirstStructure.indicator
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) (n.val+1) (D.request n.val ω))
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) (n.val+1)
          (D.position n.val ω (D.chosen n.val ω))))=_
    unfold PartitionLevel.Input.separation
    exact coordinate_expect (N:=N) A D hk ω j (fun zz=>FirstStructure.indicator
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz (n.val+1) (D.request n.val ω))
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz (n.val+1)
          (D.position n.val ω (D.chosen n.val ω))))
  simp_rw [he]
  simpa only [←Fin.sum_univ_eq_sum_range,PartitionScales.Input.level,ActualPartitions.Config.input] using A.separation (J:=J) D hk ω n (D.position n.val ω (D.chosen n.val ω))

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualEditIntegration
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! True post-request filtering tests of literal integrated key edits. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

local instance ixEI_r76ef31_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairEI_r76ef31_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem integrated_edit (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) (j : Fin J) (p : X) :
    (tapeLaw A N k J).expect (fun z=>GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
      (word A D hk z (n.val+1) ω p j) (word A D hk z n.val ω p j))=
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.editCost n
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order p := by
  rw [Law.expect_mul]
  simp_rw [diff_indicator]
  exact congrArg (fun x=>GeometricMass.radius A.R A.q j.val*x) (coordinate_expect (N:=N) A D hk ω j
    (fun zz=>FirstStructure.indicator
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz n.val p)
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz (n.val+1) p)))

theorem edit_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) (j : Fin J) (ω v : Ω) (h : (D.filtration (n.val+1)).r ω v) :
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.editCost n
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order =
    ((A.input (N:=N) (J:=J) D hk v).level j.val).data.editCost n
        ((A.input (N:=N) (J:=J) D hk v).level j.val).order := by
  funext p
  rw [←integrated_edit A D hk ω n j p,←integrated_edit A D hk v n j p]
  congr 1
  funext z
  apply congrArg (fun x=>GeometricMass.radius A.R A.q j.val*x)
  exact congrArg₂ PrefixMovement.diff
    (A.key_measurable (N:=N) (J:=J) D hk ω v (n.val+1) j.val h (z j) p)
    (A.key_measurable (N:=N) (J:=J) D hk ω v n.val j.val (D.refines n.val ω v h) (z j) p)

theorem edits_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) :
    average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>pathEdits A D hk z n.val ω))=
      average D.weight (A.keyEditCost (N:=N) (J:=J) D hk n.val) := by
  have hp (ω : Ω) : (tapeLaw A N k J).expect (fun z=>pathEdits A D hk z n.val ω)=
      ∑ j : Fin J,∑ a : Fin k,
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.editCost n
          ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (D.position n.val ω a) := by
    unfold pathEdits
    simp_rw [Law.expect_sum]
    rw [sum_comm]
    exact sum_congr rfl (fun j _=>sum_congr rfl (fun a _=>integrated_edit A D hk ω n j _))
  simp_rw [hp]
  unfold ActualPartitions.Config.keyEditCost
  simp only [dite_eq_left n.isLt]
  simp only [←Fin.sum_univ_eq_sum_range]
  have hs (f : Fin J→Ω→ℝ) : average D.weight (fun ω=>∑ j,f j ω)=∑ j,average D.weight (f j) := by
    unfold average
    simp only [mul_sum]
    rw [sum_comm]
  rw [hs,hs]
  apply sum_congr rfl
  intro j _
  exact (HiddenFlow.filtered_test D n.val _ (edit_measurable A D hk n j)).symm

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualCoordinateBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The actual multiscale coordinate motion is height-free after integration. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

local instance ixCB_r76ef31_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairCB_r76ef31_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
def totalCoordinate (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) : ℝ :=
  ∑ t∈range N,average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>coordinateCost A D hk z t ω))

theorem average_move (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) :
    average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>pathMove A D hk z n.val ω))≤
       separationRate A*(1+Real.log k)*average D.weight (moverCost (HiddenFlow.flow D) n.val) := by
  have h := average_mono D.weight _ _ (fun ω=>(D.positive ω).le) (fun ω=>move_expect (J:=J) A D hk ω n)
  change _≤average D.weight (fun ω=>separationRate A*(1+Real.log k)*
    dist (D.request n.val ω) (D.position n.val ω (D.chosen n.val ω))) at h
  rw [average_smul] at h
  change _≤_*_*(∑ ω,D.weight ω*_) at h
  rw [←HiddenFlow.expected_mover_cost D n.val] at h
  exact h

theorem coordinate_step_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) :
    A.q*average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>coordinateCost A D hk z n.val ω))≤
      average D.weight (A.keyEditCost (N:=N) (J:=J) D hk n.val)+
      separationRate A*(1+Real.log k)*average D.weight (moverCost (HiddenFlow.flow D) n.val) := by
  have h := average_mono D.weight _ _ (fun ω=>(D.positive ω).le) (fun ω=>
    (tapeLaw A N k J).expect_mono _ _ (fun z=>coordinate_split A D hk z n.val ω))
  simp only [Law.expect_mul,Law.expect_add,average_smul,average_add] at h
  rw [edits_expect] at h
  exact h.trans (add_le_add le_rfl (average_move A D hk n))

theorem coordinate_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) :
    A.q*totalCoordinate (N:=N) (J:=J) A D hk≤
      (A.editBound+separationRate A)*(1+Real.log (k+1))*
        (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+A.editEndpoint k J := by
  let Q := ∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t)
  have hQ : 0≤Q := sum_nonneg (fun t _=>sum_nonneg (fun ω _=>mul_nonneg (D.positive ω).le
    (sum_nonneg (fun p _=>mul_nonneg ((HiddenFlow.flow D).mover_nonneg t ω p) dist_nonneg))))
  have h : (∑ t∈range N, A.q*average D.weight (fun ω=>(tapeLaw A N k J).expect
      (fun z=>coordinateCost A D hk z t ω)))≤
      ∑ t∈range N,(average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t)+
        separationRate A*(1+Real.log k)*average D.weight (moverCost (HiddenFlow.flow D) t)) :=
    sum_le_sum (fun t ht=>coordinate_step_budget (J:=J) A D hk ⟨t,mem_range.mp ht⟩)
  simp only [sum_add_distrib,←mul_sum] at h
  change A.q*totalCoordinate (N:=N) (J:=J) A D hk≤
    (∑ t∈range N,average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t))+
      separationRate A*(1+Real.log k)*Q at h
  have hf := A.edit_finance (N:=N) (J:=J) D hk
  have hlog : 1+Real.log k≤1+Real.log (k+1) := by
    have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    linarith [Real.log_le_log hk' (show (k:ℝ)≤k+1 by linarith)]
  have hz := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (separationRate_nonneg A)) hQ
  change _≤A.editBound*(1+Real.log (k+1))*Q+_ at hf
  change _≤(A.editBound+separationRate A)*(1+Real.log (k+1))*Q+_
  nlinarith only [h,hf,hz]

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAllocationBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The concrete common-tree allocator paid by true metric movement. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

local instance ixAB_r76ef31_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAB_r76ef31_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem allocation_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) :
    (tapeLaw A N k J).expect (fun z=>movement (TreeCountData.data D (map A D hk z))
      (by omega) N (weight A))≤
    (8*(10:ℝ)^63/A.q)*(A.editBound+separationRate A)*EpochAlpha.ell k*(1+Real.log (k+1))*
      (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
    (8*(10:ℝ)^63/A.q)*EpochAlpha.ell k*A.editEndpoint k J+
    2*(10:ℝ)^63*EpochAlpha.ell k*allowance (shape A k J) k (weight A) := by
  have h := (tapeLaw A N k J).expect_mono _ _ (fun z=>actual_movement A D hk z N)
  rw [Law.expect_add,Law.expect_const,Law.expect_mul] at h
  have he : (tapeLaw A N k J).expect
      (fun z=>integral (TreeCountData.data D (map A D hk z)) N (coordinateCost A D hk z))=
      totalCoordinate (N:=N) (J:=J) A D hk := by
    change (tapeLaw A N k J).expect (fun z=>∑ t∈range N,average D.weight (coordinateCost A D hk z t))=_
    rw [Law.expect_sum]
    exact sum_congr rfl (fun t _=>expect_average _ _ _)
  rw [he] at h
  have hc := coordinate_finance (N:=N) (J:=J) A D hk
  have hq := A.q_pos
  have hx : 0≤8*(10:ℝ)^63/A.q*EpochAlpha.ell k := by
    have := EpochAlpha.ell_one k
    positivity
  have hm := mul_le_mul_of_nonneg_left hc hx
  have hf : (8*(10:ℝ)^63/A.q*EpochAlpha.ell k)*
      (A.q*totalCoordinate (N:=N) (J:=J) A D hk)=
      8*(10:ℝ)^63*EpochAlpha.ell k*totalCoordinate (N:=N) (J:=J) A D hk := by
    field_simp [ne_of_gt hq]
  rw [hf] at hm
  nlinarith only [h,hm]

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LabelParks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Actual fixed-coordinate parks and true posterior sizes of each level key. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def labelVertices (A : ActualPartitions.Config X) (j : Fin J) (l : Label X A.C k) :
    Finset (Vertex (size A k J)) :=
  univ.filter (fun v=>depth (shape A k J) v=j.val+1 ∧ lastLabel A v=l)

def keyRegion (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) : Finset X :=
  univ.filter (fun p=>word A D hk z t ω p j=l)

def labelPark (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ v∈labelVertices A j l,park (shape A k J)
    (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v

def labelTracker (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) : KeySizeTracker.Input Ω (k+1) :=
  KeySizePosterior.input D (HiddenFlow.regionCount D (keyRegion A D hk z j l))
    (HiddenFlow.regionCount_range D _)

theorem keyRegion_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω v : Ω)
    (h : (D.filtration t).r ω v) : keyRegion A D hk z j l t ω=keyRegion A D hk z j l t v := by
  apply filter_congr
  intro p _
  have he : word A D hk z t ω p j=word A D hk z t v p j :=
    A.key_measurable (N:=N) (J:=J) D hk ω v t j.val h (z j) p
  rw [he]

theorem labelTracker_size (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) :
    (labelTracker A D hk z j l).size t ω=
      1+ParkCapacity.mass (HiddenFlow.current D t ω) (keyRegion A D hk z j l t ω) := by
  exact congrArg (fun x : ℝ=>1+x)
    (HiddenFlow.region_posterior D _ (keyRegion_measurable A D hk z j l) t ω)

theorem labelPark_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) :
    0≤labelPark A D hk z j l t ω :=
  sum_nonneg (fun v _=>(TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω).park_nonneg v)

theorem label_region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (v : Vertex (size A k J)) (hv : v∈labelVertices A j l) :
    region A D hk z t ω v⊆keyRegion A D hk z j l t ω := by
  obtain ⟨_,hd,hl⟩ := mem_filter.mp hv
  have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
  intro p hp
  have h := last_region A D hk z t ω v h0 p hp
  have hi : (⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v h0; omega⟩ : Fin J)=j := by
    apply Fin.ext
    change depth (shape A k J) v-1=j.val
    omega
  rw [hi,hl] at h
  exact mem_filter.mpr ⟨mem_univ _,h.symm⟩

theorem label_domination (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    labelPark A D hk z j l t ω≤
      132*ParkCapacity.mass (HiddenFlow.current D t ω) (keyRegion A D hk z j l t ω) := by
  let d := TreeCountData.data D (map A D hk z)
  have hp (v : Vertex (size A k J)) : park (shape A k J) (TreeAllocator.amount d (by omega) t ω) v≤
      TreeAllocator.amount d (by omega) t ω v := by
    unfold park
    exact sub_le_self _ (sum_nonneg (fun i _=>TreeAllocator.nonneg d (by omega) t ω i.val))
  have hd := ParkCapacity.disjoint_mass (HiddenFlow.current D t ω) ((HiddenFlow.flow D).post_nonneg t ω)
    (geometry A D hk z t ω hdiam) (labelVertices A j l) (j.val+1) (keyRegion A D hk z j l t ω)
    (fun v hv=>(mem_filter.mp hv).2.1) (label_region A D hk z j l t ω)
  calc
    _≤∑ v∈labelVertices A j l,TreeAllocator.amount d (by omega) t ω v := sum_le_sum (fun v _=>hp v)
    _≤∑ v∈labelVertices A j l,132*ParkCapacity.mass (HiddenFlow.current D t ω) (region A D hk z t ω v) :=
      sum_le_sum (fun v _=>TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω v)
    _=132*(∑ v∈labelVertices A j l,ParkCapacity.mass (HiddenFlow.current D t ω) (region A D hk z t ω v)) := (mul_sum ..).symm
    _≤_ := mul_le_mul_of_nonneg_left hd (by norm_num)

theorem labelPark_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω v : Ω)
    (h : (D.filtration t).r ω v) : labelPark A D hk z j l t ω=labelPark A D hk z j l t v := by
  apply sum_congr rfl
  intro u _
  unfold park
  rw [TreeAllocator.measurable _ _ _ h]
  congr 1
  apply sum_congr rfl
  intro i _
  exact TreeAllocator.measurable _ _ _ h _

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyLabelParks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! The actual held heavy-key denominator and nearby-park geometry. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def heavyState (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) :=
  ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.heavyState (z j).1 t

def nearHeavy (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X) : Prop :=
  l∈(heavyState A D hk z j t ω).present ∧
    dist y ((heavyState A D hk z j t ω).center l)≤7*GeometricMass.radius A.R A.q j.val

theorem label_individual (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    labelPark A D hk z j l t ω/KeySizeTracker.held (labelTracker A D hk z j l) t ω≤(6/5)*132 := by
  have hc := (KeySizeTracker.comparisons (labelTracker A D hk z j l) t ω).1
  have hd := label_domination A D hk z j l t ω hdiam
  rw [labelTracker_size] at hc
  have hp : 0<KeySizeTracker.held (labelTracker A D hk z j l) t ω := by
    linarith [(KeySizeTracker.held_range (labelTracker A D hk z j l) t ω).1]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem heavy_inner_subset (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X)
    (hl : nearHeavy A D hk z j t ω y l) :
    ParkCapacity.ball y (GeometricMass.radius A.R A.q j.val)⊆keyRegion A D hk z j (Sum.inl l) t ω := by
  intro p hp
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  exact LevelMap.Data.inner_heavy ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t y p l hl.1 hl.2 (mem_filter.mp hp).2

theorem heavy_denominator (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X)
    (hl : nearHeavy A D hk z j t ω y l) :
    ParkCoefficients.inner (HiddenFlow.current D t ω) y A.R A.q j.val≤
      (6/5)*KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) t ω := by
  have hm : ParkCapacity.mass (HiddenFlow.current D t ω)
      (ParkCapacity.ball y (GeometricMass.radius A.R A.q j.val))≤
      ParkCapacity.mass (HiddenFlow.current D t ω) (keyRegion A D hk z j (Sum.inl l) t ω) :=
    sum_le_sum_of_subset_of_nonneg (heavy_inner_subset A D hk z j t ω y l hl)
      (fun p _ _=>(HiddenFlow.flow D).post_nonneg t ω p)
  have hc := (KeySizeTracker.comparisons (labelTracker A D hk z j (Sum.inl l)) t ω).1
  rw [labelTracker_size] at hc
  change 1+GeometricMass.mass (HiddenFlow.current D t ω) y _≤_
  rw [ball_mass] at hm
  linarith

theorem label_anchor (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (v : Vertex (size A k J)) (hv : v∈labelVertices A j l) :
    anchor A D hk z t ω v=
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.anchor (z j) t l := by
  obtain ⟨_,hd,hl⟩ := mem_filter.mp hv
  have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
  rw [anchor,dite_eq_right h0]
  have hi : (⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v h0; omega⟩ : Fin J)=j := by
    apply Fin.ext
    change depth (shape A k J) v-1=j.val
    omega
  exact congrArg₂ (fun (i : Fin J) (a : Label X A.C k)=>
    ((A.input (N:=N) (J:=J) D hk ω).level i.val).data.anchor (z i) t a) hi hl

theorem near_park_witness (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X)
    (hl : nearHeavy A D hk z j t ω y l) (v : Vertex (size A k J))
    (hv : v∈labelVertices A j (Sum.inl l))
    (hp : 0<park (shape A k J) (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v) :
    ∃ p∈region A D hk z t ω v,dist y p≤27*radius A (j.val+1) := by
  have ha : 0<TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω v := by
    unfold park at hp
    have hs := sum_nonneg (fun i (_ : i∈(univ : Finset (Children (shape A k J) v)))=>
      TreeAllocator.nonneg (TreeCountData.data D (map A D hk z)) (by omega) t ω i.val)
    linarith
  obtain ⟨p,hp⟩ := witness A D hk z t ω v ha
  have hd := (mem_filter.mp hv).2.1
  have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
  have hpdist := anchor_distance A D hk z t ω v h0 p hp
  rw [label_anchor A D hk z j (Sum.inl l) t ω v hv,hd] at hpdist
  have htri := dist_triangle y ((heavyState A D hk z j t ω).center l) p
  rw [dist_comm ((heavyState A D hk z j t ω).center l) p] at htri
  refine ⟨p,hp,?_⟩
  have hnear : dist y ((heavyState A D hk z j t ω).center l)≤7*radius A (j.val+1) := hl.2
  change dist p ((heavyState A D hk z j t ω).center l)≤_ at hpdist
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SelectedParkCoefficients
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                               
section

/-! Instantiate the height-free coefficient estimate with actual nearby heavy
slots of the completed fractional state. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def selectedVertices (A : ActualPartitions.Config X) (s : Fin J→Option (LevelMap.HeavySlot X))
    (i : ℕ) : Finset (Vertex (size A k J)) :=
  if hi : i<J then ((s ⟨i,hi⟩).map (fun l=>labelVertices A ⟨i,hi⟩ (Sum.inl l))).getD ∅ else ∅

def selectedDen (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (s : Fin J→Option (LevelMap.HeavySlot X)) (t : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  if hi : i<J then ((s ⟨i,hi⟩).map (fun l=>KeySizeTracker.held (labelTracker A D hk z ⟨i,hi⟩ (Sum.inl l)) t ω)).getD (k+1) else k+1

omit [MetricSpace X] in
theorem selected_depth (A : ActualPartitions.Config X) (s : Fin J→Option (LevelMap.HeavySlot X))
    (i : ℕ) (hi : i<J) (v : Vertex (size A k J)) (hv : v∈selectedVertices A s i) :
    depth (shape A k J) v=i+1 := by
  simp only [selectedVertices,dite_eq_left hi] at hv
  cases hs : s ⟨i,hi⟩ with
  | none => simp only [hs,Option.map_none,Option.getD_none,Finset.notMem_empty] at hv
  | some l =>
    simp only [hs,Option.map_some,Option.getD_some] at hv
    exact (mem_filter.mp hv).2.1

theorem selected_coefficients (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (s : Fin J→Option (LevelMap.HeavySlot X)) (t : ℕ) (ω : Ω) (y : X)
    (hs : ∀ j l,s j=some l→nearHeavy A D hk z j t ω y l)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    (∑ i∈range J,(∑ v∈selectedVertices A s i,park (shape A k J)
      (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v)/selectedDen A D hk z s t ω i)≤
      (6/5)*132*(2+7/Real.log 2)*Real.log (k+1) := by
  let a := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω
  let μ := HiddenFlow.current D t ω
  let b : ℕ→ℝ := fun i=>∑ v∈selectedVertices A s i,park (shape A k J) a.amount v
  have hm : ∀ p,0≤μ p := (HiddenFlow.flow D).post_nonneg t ω
  have htotal : ∑ p,μ p≤(k+1:ℝ)-1 := by
    have ht := (HiddenFlow.flow D).post_total t ω
    change (∑ p,μ p)=k at ht
    linarith
  have hden (i : ℕ) (hi : i<J) : ParkCoefficients.inner μ y A.R A.q i≤
      (6/5)*selectedDen A D hk z s t ω i := by
    simp only [selectedDen,dite_eq_left hi]
    cases he : s ⟨i,hi⟩ with
    | none =>
      simp only [Option.map_none,Option.getD_none]
      have hh := (GeometricMass.mass_total μ hm y (GeometricMass.radius A.R A.q i)).trans htotal
      unfold ParkCoefficients.inner
      linarith [Nat.cast_nonneg (α:=ℝ) k]
    | some l =>
      simp only [Option.map_some,Option.getD_some]
      exact heavy_denominator A D hk z ⟨i,hi⟩ t ω y l (hs _ _ he)
  have hind (i : ℕ) (hi : i<J) : b i/selectedDen A D hk z s t ω i≤(6/5)*132 := by
    dsimp only [b]
    simp only [selectedVertices,selectedDen,dite_eq_left hi]
    cases he : s ⟨i,hi⟩ with
    | none => simp only [Option.map_none,Option.getD_none,sum_empty,zero_div] <;> norm_num
    | some l =>
      simp only [Option.map_some,Option.getD_some]
      exact label_individual A D hk z ⟨i,hi⟩ (Sum.inl l) t ω hdiam
  have hcap (j : ℕ) (_hj : j<J) : ParkCoefficients.tail b J j≤132*(ParkCoefficients.outer μ y A.R A.q j-1) := by
    have h := ParkCapacity.level_cumulative a (geometry A D hk z t ω hdiam) μ hm 132 (by norm_num)
      (TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω)
      (selectedVertices A s) J j y (selected_depth A s) (by
        intro i hi v hv hp
        simp only [selectedVertices,dite_eq_left hi] at hv
        cases he : s ⟨i,hi⟩ with
        | none => simp only [he,Option.map_none,Option.getD_none,Finset.notMem_empty] at hv
        | some l =>
          simp only [he,Option.map_some,Option.getD_some] at hv
          exact near_park_witness A D hk z ⟨i,hi⟩ t ω y l (hs _ _ he) v hv hp)
    simpa only [ParkCoefficients.outer,add_sub_cancel_left,geometry,radius,GeometricMass.radius,ball_mass] using h
  have hp : 67*A.q^7≤1 := by
    have hq := pow_le_pow_left₀ A.q_pos.le A.q_small 7
    norm_num at hq
    linarith
  exact ParkCoefficients.pointwise μ hm y (k+1) A.R A.q 132 (6/5) htotal A.R_pos A.q_pos
    (by norm_num) (by norm_num) 7 J hp b (selectedDen A D hk z s t ω)
    (fun i=>sum_nonneg (fun v _=>a.park_nonneg v)) hden hind hcap

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorDrift
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Height-free hidden-motion drift of the actual parked-heavy potential.
The coefficient is evaluated in the old completed state at the true old
member, with no event-conditioned filtering assumption. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance labelDecEq (C : ℝ) (m : ℕ) : DecidableEq (Label X C m) := fun a b=>Classical.propDecidable (a=b)

def heavyCoefficient (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (l : LevelMap.HeavySlot X) : ℝ :=
  labelPark A D hk z j (Sum.inl l) t ω/KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) t ω

def heavySelection (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (j : Fin J) : Option (LevelMap.HeavySlot X) :=
  match word A D hk z t ω y j with
  | Sum.inl l => if dist ((heavyState A D hk z j t ω).center l) y<7*GeometricMass.radius A.R A.q j.val then some l else none
  | Sum.inr _ => none

theorem heavySelection_near (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (j : Fin J) (l : LevelMap.HeavySlot X)
    (hl : heavySelection A D hk z t ω y j=some l) : nearHeavy A D hk z j t ω y l := by
  unfold heavySelection at hl
  cases he : word A D hk z t ω y j with
  | inr a => simp only [he] at hl; cases hl
  | inl a =>
    simp only [he] at hl
    split_ifs at hl with hd
    · have hal : a=l := Option.some.inj hl
      subst a
      have hc := (LevelMap.Data.key_heavy_iff ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t y l).mp he
      exact ⟨hc.1,by simpa only [dist_comm] using hd.le⟩

def heavyNear (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (j : Fin J) : ℝ :=
  AnchorScalar.near (GeometricMass.radius A.R A.q j.val) (heavyCoefficient A D hk z j t ω)
    (heavyState A D hk z j t ω).center (word A D hk z t ω y j) y

theorem near_sum (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    (∑ j : Fin J,heavyNear A D hk z t ω y j)≤(6/5)*132*(2+7/Real.log 2)*Real.log (k+1) := by
  have h := selected_coefficients A D hk z (heavySelection A D hk z t ω y) t ω y
    (fun j l hl=>heavySelection_near A D hk z t ω y j l hl) hdiam
  rw [←Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro j _
  simp only [selectedVertices,selectedDen,dite_eq_left j.isLt,heavySelection,heavyNear,AnchorScalar.near]
  cases he : word A D hk z t ω y j with
  | inr a => simp only [Option.map_none,Option.getD_none,sum_empty,zero_div]
  | inl a =>
    dsimp only
    split_ifs <;> simp only [Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,sum_empty,zero_div]
    rfl

def heavyValue (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (l : Label X A.C k) (p : X) : ℝ :=
  AnchorScalar.value (GeometricMass.radius A.R A.q j.val) (heavyCoefficient A D hk z j t ω)
    (heavyState A D hk z j t ω).center l p

def memberDrift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (a : Fin k) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
    (heavyValue A D hk z j t ω (word A D hk z (t+1) ω (D.position (t+1) ω a) j) (D.position (t+1) ω a)-
     heavyValue A D hk z j t ω (word A D hk z t ω (D.position t ω a) j) (D.position t ω a))

theorem member_drift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (a : Fin k) (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    memberDrift A D hk z t ω a≤
      (6/5)*132*(∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
        PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
          (word A D hk z t ω (D.position t ω a) j))+
      dist (D.position t ω a) (D.position (t+1) ω a)/3*
        ((6/5)*132*(2+7/Real.log 2)*Real.log (k+1)) := by
  have hc (j : Fin J) (l : LevelMap.HeavySlot X) : 0≤heavyCoefficient A D hk z j t ω l :=
    div_nonneg (labelPark_nonneg A D hk z j (Sum.inl l) t ω)
      (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) t ω).1; linarith)
  have h (j : Fin J) := AnchorScalar.member (GeometricMass.radius A.R A.q j.val) ((6/5)*132)
    (GeometricMass.radius_pos _ _ A.R_pos A.q_pos _) (heavyCoefficient A D hk z j t ω)
    (heavyState A D hk z j t ω).center (hc j) (by norm_num)
    (fun l=>label_individual A D hk z j (Sum.inl l) t ω hdiam)
    (word A D hk z t ω (D.position t ω a) j)
    (word A D hk z (t+1) ω (D.position (t+1) ω a) j) (D.position t ω a) (D.position (t+1) ω a)
  have hs := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>h j)
  have hn := mul_le_mul_of_nonneg_left (near_sum A D hk z t ω (D.position t ω a) hdiam)
    (show 0≤dist (D.position t ω a) (D.position (t+1) ω a)/3 by positivity)
  simp only [sum_add_distrib,←mul_sum] at hs
  change memberDrift A D hk z t ω a≤_ at hs
  refine hs.trans ?_
  convert add_le_add (le_refl ((6/5)*132*(∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
      PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j) (word A D hk z t ω (D.position t ω a) j)))) hn using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  unfold PrefixMovement.diff
  by_cases he : word A D hk z t ω (D.position t ω a) j=word A D hk z (t+1) ω (D.position (t+1) ω a) j
  · simp only [he,ite_true, if_true,mul_zero]
  · simp only [ite_eq_right he,ite_eq_right (Ne.symm he),mul_one]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorDriftSum
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! The individual retained-anchor hidden drift summed over exactly the
chosen mover and all stationary members. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem members_drift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    (∑ a : Fin k,memberDrift A D hk z t ω a)≤
      (6/5)*132*A.q*coordinateCost A D hk z t ω+
      (driftLog k/3)*dist (D.position t ω (D.chosen t ω)) (D.request t ω) := by
  have hs := sum_le_sum (s:=univ) (fun a (_ : a∈(univ : Finset (Fin k)))=>member_drift A D hk z t ω a hdiam)
  have he : (∑ a : Fin k,∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
       PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
         (word A D hk z t ω (D.position t ω a) j))=A.q*coordinateCost A D hk z t ω := by
    simp only [coordinateCost,mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro j _
    simp only [GeometricMass.radius,radius,pow_succ]
    ring
  simp only [sum_add_distrib,←mul_sum,←sum_mul,←sum_div] at hs
  rw [he,HiddenFlow.member_distance] at hs
  dsimp only [driftLog]
  nlinarith only [hs]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorPotential
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! The actual four parameter substeps after the unconditional hidden drift. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def anchorIntegral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (m a : ℕ) (ω : Ω) : ℝ :=
  AnchorPotential.integral (GeometricMass.radius A.R A.q j.val) (HiddenFlow.current D m ω)
    (keyRegion A D hk z j (Sum.inl l) m ω) ((heavyState A D hk z j a ω).center l)

def anchorTerm (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (b u m a : ℕ) (ω : Ω) : ℝ :=
  GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) b ω/
    KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) u ω*anchorIntegral A D hk z j l m a ω

theorem anchorIntegral_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (m a : ℕ) (ω : Ω) :
    0 ≤ anchorIntegral A D hk z j l m a ω :=
  AnchorPotential.integral_nonneg _ _ ((HiddenFlow.flow D).post_nonneg m ω) _ _

theorem anchorIntegral_held (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (m a : ℕ) (ω : Ω) :
    anchorIntegral A D hk z j l m a ω ≤ (6/5)*KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) m ω := by
  have hi := AnchorPotential.integral_le (GeometricMass.radius A.R A.q j.val) _
    ((HiddenFlow.flow D).post_nonneg m ω) (keyRegion A D hk z j (Sum.inl l) m ω) ((heavyState A D hk z j a ω).center l)
  have hc := (KeySizeTracker.comparisons (labelTracker A D hk z j (Sum.inl l)) m ω).1
  rw [labelTracker_size] at hc
  exact hi.trans (by
    change (∑ p∈keyRegion A D hk z j (Sum.inl l) m ω,HiddenFlow.current D m ω p) ≤ _
    dsimp only [ParkCapacity.mass] at hc
    linarith)

theorem anchorTerm_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (b u m a : ℕ) (ω : Ω) :
    0 ≤ anchorTerm A D hk z j l b u m a ω := by
  unfold anchorTerm
  exact mul_nonneg (div_nonneg (mul_nonneg (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    (labelPark_nonneg A D hk z j (Sum.inl l) b ω)) (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) u ω).1; linarith))
    (anchorIntegral_nonneg A D hk z j l m a ω)

theorem absent_park (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) (hl : l∉(heavyState A D hk z j t ω).present) :
    labelPark A D hk z j (Sum.inl l) t ω=0 := by
  have he : keyRegion A D hk z j (Sum.inl l) t ω=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hc := (LevelMap.Data.key_heavy_iff ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p l).mp ((mem_filter.mp hp).2)
    exact hl hc.1
  have hd := label_domination A D hk z j (Sum.inl l) t ω hdiam
  rw [he,ParkCapacity.mass,sum_empty,mul_zero] at hd
  exact le_antisymm hd (labelPark_nonneg A D hk z j (Sum.inl l) t ω)

theorem anchorTerm_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (b m a : ℕ) (ω : Ω) :
    anchorTerm A D hk z j l b m m a ω ≤ 
      (6/5)*GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) b ω := by
  have hu : 0<KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) m ω := by
    have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) m ω).1; linarith
  have hi := (div_le_iff₀ hu).mpr (anchorIntegral_held A D hk z j l m a ω)
  have hm := mul_le_mul_of_nonneg_left hi (mul_nonneg (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    (labelPark_nonneg A D hk z j (Sum.inl l) b ω))
  dsimp only [anchorTerm]
  calc
    _ = GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) b ω*
        (anchorIntegral A D hk z j l m a ω/KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) m ω) := by ring
    _ ≤ _ := hm
    _ = _ := by ring

theorem parameter_reference (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    anchorTerm A D hk z j l t (t+1) (t+1) t ω-anchorTerm A D hk z j l t t (t+1) t ω ≤ 
      GeometricMass.radius A.R A.q j.val*((6/5)*132)*KeySizeTracker.charge (labelTracker A D hk z j (Sum.inl l)) t ω := by
  have hu : 0<KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) t ω := by
    have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) t ω).1; linarith
  exact AnchorPotential.reference (labelTracker A D hk z j (Sum.inl l)) _ _ _ _ _ t ω
    (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le (labelPark_nonneg A D hk z j (Sum.inl l) t ω)
    (anchorIntegral_nonneg A D hk z j l (t+1) t ω)
    (AnchorPotential.integral_le _ _ ((HiddenFlow.flow D).post_nonneg (t+1) ω) _ _)
    (labelTracker_size A D hk z j (Sum.inl l) (t+1) ω)
    ((div_le_iff₀ hu).mp (label_individual A D hk z j (Sum.inl l) t ω hdiam)) (by norm_num)

theorem parameter_parks (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω) :
    |anchorTerm A D hk z j l (t+1) (t+1) (t+1) t ω-anchorTerm A D hk z j l t (t+1) (t+1) t ω| ≤ 
      (6/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| := by
  exact AnchorScalar.parks _ _ _ _ _ _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    (anchorIntegral_nonneg A D hk z j l (t+1) t ω)
    (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) (t+1) ω).1; linarith)
    (anchorIntegral_held A D hk z j l (t+1) t ω)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorFiltering
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! The five-substep potential's filtering and hidden-motion identity is an
unconditional finite-law identity at every step. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def frozenPotential (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,∑ l : LevelMap.HeavySlot X,anchorTerm A D hk z j l t t s t ω

theorem frozen_regroup (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (ω : Ω) :
    frozenPotential A D hk z t s ω=∑ p,HiddenFlow.current D s ω p*
      ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*heavyValue A D hk z j t ω (word A D hk z s ω p j) p := by
  have hj (j : Fin J) : (∑ l : LevelMap.HeavySlot X,anchorTerm A D hk z j l t t s t ω)=
      GeometricMass.radius A.R A.q j.val*(∑ p,HiddenFlow.current D s ω p*
        heavyValue A D hk z j t ω (word A D hk z s ω p j) p) := by
    have hm := AnchorPotential.regroup (GeometricMass.radius A.R A.q j.val) (HiddenFlow.current D s ω)
      (heavyCoefficient A D hk z j t ω) (heavyState A D hk z j t ω).center (fun p=>word A D hk z s ω p j)
    dsimp only [heavyValue]
    rw [←hm,mul_sum]
    apply sum_congr rfl
    intro l _
    dsimp only [anchorTerm,anchorIntegral,heavyCoefficient,keyRegion]
    ring_nf
    congr 2
    ext p
    simp only [mem_filter,mem_univ,true_and]
  simp only [frozenPotential,hj,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro j _
  ring

theorem heavyValue_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω v : Ω) (h : (D.filtration t).r ω v)
    (l : Label X A.C k) (p : X) : heavyValue A D hk z j t ω l p=heavyValue A D hk z j t v l p := by
  cases l with
  | inr a => rfl
  | inl l =>
    dsimp only [heavyValue,AnchorScalar.value,heavyCoefficient]
    have hp := labelPark_measurable A D hk z j (Sum.inl l) t ω v h
    have hu := KeySizeTracker.held_measurable (labelTracker A D hk z j (Sum.inl l)) t ω v h
    have ha := A.anchor_measurable (N:=N) (J:=J) D hk ω v t j.val h (z j) (Sum.inl l)
    change (heavyState A D hk z j t ω).center l=(heavyState A D hk z j t v).center l at ha
    rw [hp,hu,ha]

theorem frozen_testing (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (hts : t ≤ s) :
    average D.weight (frozenPotential A D hk z t s)=
      average D.weight (fun ω=>∑ a : Fin k,∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
        heavyValue A D hk z j t ω (word A D hk z s ω (D.position s ω a) j) (D.position s ω a)) := by
  change average D.weight (fun ω=>frozenPotential A D hk z t s ω)=_
  simp_rw [frozen_regroup]
  apply HiddenFlow.current_test
  intro ω v h
  funext p
  apply sum_congr rfl
  intro j _
  have hk' := A.key_measurable (N:=N) (J:=J) D hk ω v s j.val h (z j) p
  change word A D hk z s ω p j=word A D hk z s v p j at hk'
  rw [hk']
  exact congrArg (fun x : ℝ=>GeometricMass.radius A.R A.q j.val*x)
    (heavyValue_measurable A D hk z j t ω v (HiddenFlow.refines_le D t s hts ω v h) _ p)

theorem expected_drift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    average D.weight (fun ω=>frozenPotential A D hk z t (t+1) ω-frozenPotential A D hk z t t ω) ≤
      average D.weight (fun ω=>(6/5)*132*A.q*coordinateCost A D hk z t ω+
        (driftLog k/3)*dist (D.position t ω (D.chosen t ω)) (D.request t ω)) := by
  have he : average D.weight (fun ω=>frozenPotential A D hk z t (t+1) ω-frozenPotential A D hk z t t ω)=
      average D.weight (fun ω=>∑ a : Fin k,memberDrift A D hk z t ω a) := by
    have h1 := frozen_testing A D hk z t (t+1) (by omega)
    have h0 := frozen_testing A D hk z t t le_rfl
    simp only [average,mul_sub,sum_sub_distrib] at h1 h0 ⊢
    rw [h1,h0]
    simp only [memberDrift,mul_sub,sum_sub_distrib]
  rw [he]
  exact PilotEdits.average_mono D.weight _ _ (fun ω=>(D.positive ω).le)
    (fun ω=>members_drift A D hk z t ω hdiam)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorRelease
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Retained heavy-label release with the literal post-request law and held
size. The heavy test is extracted from the actual level input. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem actual_anchor_release (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ht : t<N) (ω : Ω) (l : LevelMap.HeavySlot X)
    (ho : l∈(heavyState A D hk z j t ω).present) (hn : l∈(heavyState A D hk z j (t+1) ω).present)
    (hm : (heavyState A D hk z j t ω).center l≠(heavyState A D hk z j (t+1) ω).center l) :
    GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) (t+1) ω/
      KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) (t+1) ω*
      (∑ p∈keyRegion A D hk z j (Sum.inl l) (t+1) ω,HiddenFlow.current D (t+1) ω p*
        (AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j (t+1) ω).center l) p-
         AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j t ω).center l) p))≤
       -(1/4)*GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) (t+1) ω := by
  let I := (A.input (N:=N) (J:=J) D hk ω).level j.val
  have hp : I.data.point t=D.request t ω := by
    dsimp only [LevelMap.Data.point]
    rw [dite_eq_left ht]
    rfl
  have hμ := (HiddenFlow.flow D).post_nonneg (t+1) ω
  have hr := GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j.val
  have hh : I.data.heavyFlag t→GeometricMass.mass (HiddenFlow.current D (t+1) ω) (I.data.point t)
      (51200*I.data.r)≤(1+A.P.deltaH)*GeometricMass.mass (HiddenFlow.current D (t+1) ω)
        (I.data.point t) (A.P.gammaH*I.data.r) := by
    intro hh
    obtain ⟨ht',hh⟩ := hh
    rw [hp]
    exact hh
  have hH : 1≤GeometricMass.mass (HiddenFlow.current D (t+1) ω) (I.data.point t) (A.P.gammaH*I.data.r) := by
    rw [hp]
    exact (HiddenFlow.serving_mass D t ω).trans (GeometricMass.mass_center _ hμ _ _ (mul_nonneg A.P.gammaH_pos.le hr.le))
  have hd := (KeySizeTracker.comparisons (labelTracker A D hk z j (Sum.inl l)) (t+1) ω).2
  rw [labelTracker_size] at hd
  exact LevelMap.Data.anchor_release I.data I.order (z j) t l ho hn hm
    (HiddenFlow.current D (t+1) ω) hμ A.P.gammaH A.P.deltaH
    (labelPark A D hk z j (Sum.inl l) (t+1) ω)
    (KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) (t+1) ω)
    (by linarith [A.P.gammaH_small]) (by linarith [A.P.deltaH_small])
    (labelPark_nonneg A D hk z j (Sum.inl l) (t+1) ω)
    (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) (t+1) ω).1; linarith)
    hH hh hd

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorStep
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Complete per-slot anchor update, including deleted, newly born, unchanged,
and retained moving slots; then the faithful five-substep ledger. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def retainedMoving (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω) : Prop :=
  l∈(heavyState A D hk z j t ω).present ∧ l∈(heavyState A D hk z j (t+1) ω).present ∧
    (heavyState A D hk z j t ω).center l≠(heavyState A D hk z j (t+1) ω).center l

def anchorPayment (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω) : ℝ :=
  if retainedMoving A D hk z j l t ω then (1/4)*GeometricMass.radius A.R A.q j.val*
    labelPark A D hk z j (Sum.inl l) (t+1) ω else 0

theorem parameter_anchors (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ht : t<N) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    anchorTerm A D hk z j l (t+1) (t+1) (t+1) (t+1) ω-
      anchorTerm A D hk z j l (t+1) (t+1) (t+1) t ω+anchorPayment A D hk z j l t ω ≤
      (6/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| := by
  have hfree : 0 ≤ (6/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| :=
    mul_nonneg (mul_nonneg (by norm_num) (GeometricMass.radius_pos _ _ A.R_pos A.q_pos _).le) (abs_nonneg _)
  by_cases hn : l∈(heavyState A D hk z j (t+1) ω).present
  · by_cases ho : l∈(heavyState A D hk z j t ω).present
    · by_cases hm : (heavyState A D hk z j t ω).center l=(heavyState A D hk z j (t+1) ω).center l
      · have he : anchorIntegral A D hk z j l (t+1) (t+1) ω=anchorIntegral A D hk z j l (t+1) t ω := by
          dsimp only [anchorIntegral]; rw [hm]
        simp only [anchorTerm,he,sub_self,anchorPayment,retainedMoving,hm,ne_eq,not_true_eq_false,and_false,ite_false, if_false,add_zero]
        exact hfree
      · have h := actual_anchor_release A D hk z j t ht ω l ho hn hm
        have he : anchorTerm A D hk z j l (t+1) (t+1) (t+1) (t+1) ω-
            anchorTerm A D hk z j l (t+1) (t+1) (t+1) t ω=
            GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) (t+1) ω/
              KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) (t+1) ω*
              (∑ p∈keyRegion A D hk z j (Sum.inl l) (t+1) ω,HiddenFlow.current D (t+1) ω p*
                (AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j (t+1) ω).center l) p-
                 AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j t ω).center l) p)) := by
          simp only [anchorTerm,anchorIntegral,AnchorPotential.integral,mul_sub,sum_sub_distrib]
        rw [he,anchorPayment,ite_eq_left ⟨ho,hn,hm⟩]
        nlinarith only [h,hfree]
    · have hz := absent_park A D hk z j l t ω hdiam ho
      have hb := anchorTerm_bound A D hk z j l (t+1) (t+1) (t+1) ω
      have hp := anchorTerm_nonneg A D hk z j l (t+1) (t+1) (t+1) t ω
      rw [anchorPayment,ite_eq_right (by intro h; exact ho h.1),hz,sub_zero,
        abs_of_nonneg (labelPark_nonneg A D hk z j (Sum.inl l) (t+1) ω)]
      linarith
  · have hz := absent_park A D hk z j l (t+1) ω hdiam hn
    simp only [anchorTerm,hz,mul_zero,zero_div,zero_mul,sub_self,anchorPayment,retainedMoving,hn,false_and,and_false,ite_false, if_false,add_zero]
    simpa only [hz] using hfree

theorem anchor_slot_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ht : t<N) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    anchorTerm A D hk z j l (t+1) (t+1) (t+1) (t+1) ω-anchorTerm A D hk z j l t t t t ω+
      anchorPayment A D hk z j l t ω ≤
      (anchorTerm A D hk z j l t t (t+1) t ω-anchorTerm A D hk z j l t t t t ω)+
      GeometricMass.radius A.R A.q j.val*((6/5)*132)*KeySizeTracker.charge (labelTracker A D hk z j (Sum.inl l)) t ω+
      (12/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| := by
  have hf := parameter_reference A D hk z j l t ω hdiam
  have hp := (le_abs_self _).trans (parameter_parks A D hk z j l t ω)
  have ha := parameter_anchors A D hk z j l t ht ω hdiam
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualSizeBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The fixed-slot entropy refresh budget, instantiated with actual keys and
counted coupled hidden members, independent of the number of time steps. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry RankTracking TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem key_count_eq (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) :
    HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω=
      KeyCountVariation.count (fun a=>word A D hk z t ω (D.position t ω a) j) l := by
  simp only [HiddenFlow.regionCount,keyRegion,KeyCountVariation.count,KeyCountVariation.indicator,
    mem_filter,mem_univ,true_and]
  apply sum_congr rfl
  intro a _
  by_cases he : word A D hk z t ω (D.position t ω a) j=l <;> simp [he]

theorem key_count_variation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
       HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|)≤
      2*A.q*coordinateCost A D hk z t ω := by
  have h (j : Fin J) := KeyCountVariation.total
    (fun a=>word A D hk z (t+1) ω (D.position (t+1) ω a) j)
    (fun a=>word A D hk z t ω (D.position t ω a) j)
  calc
    _≤∑ j : Fin J,GeometricMass.radius A.R A.q j.val*(2*∑ a : Fin k,
      PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
      (word A D hk z t ω (D.position t ω a) j)) := by
        apply sum_le_sum
        intro j _
        simp only [key_count_eq]
        exact mul_le_mul_of_nonneg_left (h j) (GeometricMass.radius_pos _ _ A.R_pos A.q_pos _).le
    _=_ := by
      simp only [coordinateCost,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro j _
      simp only [GeometricMass.radius,radius,pow_succ]
      ring

def sizeRefresh (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
    ∑ t∈range H,average D.weight (KeySizeTracker.charge (labelTracker A D hk z j l) t)

theorem label_size_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (H : ℕ) :
    (∑ t∈range H,average D.weight (KeySizeTracker.charge (labelTracker A D hk z j l) t))≤
      144*KeySizeTracker.ell (k+1)*(∑ t∈range H,average D.weight (fun ω=>
        |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
         HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|))+
      288*(k+1)*(1+KeySizeTracker.ell (k+1)) :=
  KeySizePosterior.budget D _ (HiddenFlow.regionCount_range D _) H

theorem size_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) :
    sizeRefresh A D hk z H≤288*KeySizeTracker.ell (k+1)*A.q*
      integral (TreeCountData.data D (map A D hk z)) H (coordinateCost A D hk z)+sizeEndpoint A k J := by
  have h := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>
    mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun l _=>label_size_budget A D hk z j l H))
      (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le)
  have he : 0≤144*KeySizeTracker.ell (k+1) := by
    unfold KeySizeTracker.ell
    have hk' : (1:ℝ)≤k+1 := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
    have := Real.log_nonneg hk'
    positivity
  have hd := sum_le_sum (s:=range H) (fun t _=>average_mono (fun ω=>(D.positive ω).le)
    (key_count_variation A D hk z t))
  simp only [average_mul] at hd
  have hdm := mul_le_mul_of_nonneg_left hd he
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at h
  have hex := weighted_integral (fun j : Fin J=>GeometricMass.radius A.R A.q j.val) D.weight H
    (fun j l t ω=>|HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
      HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|)
  -- Reassociate constants, keeping the two finite Fubini identities explicit.
  change sizeRefresh A D hk z H≤_ at h
  have hrw : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
      (144*KeySizeTracker.ell (k+1)*(∑ l : Label X A.C k,∑ t∈range H,average D.weight (fun ω=>
        |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
          HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|))))=
      144*KeySizeTracker.ell (k+1)*(∑ t∈range H,average D.weight (fun ω=>
        ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
          |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
           HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|)) := by
    rw [←hex,mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  simp only [mul_add,sum_add_distrib] at h
  rw [hrw] at h
  simp only [←sum_mul,←mul_sum] at h hdm
  dsimp only [sizeEndpoint,integral,TreeCountData.data] at *
  simp only [card_univ] at h
  nlinarith only [h,hdm]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LabelParkVariation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Disjoint fixed-label fibers charge all grouped park variation to the literal
common-tree allocation, without a height factor. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

omit [MetricSpace X] in
theorem label_fiber_sum (A : ActualPartitions.Config X) (f : Vertex (size A k J)→ℝ) (j : Fin J) :
    (∑ l : Label X A.C k, ∑ v∈labelVertices A j l,f v)=
      ∑ v,if depth (shape A k J) v=j.val+1 then f v else 0 := by
  simp only [labelVertices,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hd : depth (shape A k J) v=j.val+1
  · simp only [hd,true_and,ite_true, if_true,sum_ite_eq,mem_univ]
  · simp only [hd,false_and,ite_false, if_false,sum_const_zero]

omit [MetricSpace X] in
theorem weighted_label_sum (A : ActualPartitions.Config X) (f : Vertex (size A k J)→ℝ) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      ∑ v∈labelVertices A j l,f v)=∑ v,if v=0 then 0 else weight A v*f v := by
  simp_rw [label_fiber_sum]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · subst v
    simp only [depth_root,mul_ite,mul_zero]
    have he (j : Fin J) : ¬(0=j.val+1) := by omega
    simp only [he,ite_false, if_false,sum_const_zero,ite_true, if_true]
  · rw [ite_eq_right hv]
    have hp := depth_positive A v hv
    have hb : depth (shape A k J) v ≤ J := PrefixTree.depth_bound v
    let j : Fin J := ⟨depth (shape A k J) v-1,by omega⟩
    calc
      _ = GeometricMass.radius A.R A.q j.val*
        (if depth (shape A k J) v=j.val+1 then f v else 0) := by
          apply sum_eq_single j
          · intro i _ hi
            have hne : depth (shape A k J) v≠i.val+1 := by
              intro he
              apply hi
              apply Fin.ext
              dsimp [j]
              omega
            rw [ite_eq_right hne,mul_zero]
          · intro hj; exact (hj (mem_univ _)).elim
      _ = _ := by
        have hd : depth (shape A k J) v=j.val+1 := by dsimp [j]; omega
        rw [ite_eq_left hd]
        have hr : GeometricMass.radius A.R A.q j.val=weight A v := by
          dsimp only [weight,radius,GeometricMass.radius]
          rw [hd]
        rw [hr]

theorem label_park_variation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      |labelPark A D hk z j l (t+1) ω-labelPark A D hk z j l t ω|) ≤
      (1+1/22)*variation (weight A)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω) := by
  let a := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω
  let b := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω
  have he : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      |labelPark A D hk z j l (t+1) ω-labelPark A D hk z j l t ω|) ≤
      ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
        ∑ v∈labelVertices A j l,|park (shape A k J) b.amount v-park (shape A k J) a.amount v| := by
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    apply sum_le_sum
    intro l _
    unfold labelPark
    rw [←sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _
  rw [weighted_label_sum] at he
  refine he.trans ((sum_le_sum fun v _=>?_).trans
    (TreeParking.weighted_variation a b (weight A) 22 (fun v=>radius_nonneg A _) (by norm_num) (weight_separated A)))
  by_cases hv : v=0
  · rw [ite_eq_left hv]
    exact mul_nonneg (radius_nonneg A _) (abs_nonneg _)
  · rw [ite_eq_right hv]

theorem heavy_park_variation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
      |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω|) ≤
      (1+1/22)*variation (weight A)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω) := by
  refine le_trans (sum_le_sum fun j _=>mul_le_mul_of_nonneg_left ?_
    (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le) (label_park_variation A D hk z t ω)
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (sum_nonneg fun l _=>abs_nonneg _)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorLedger
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The actual signed five-substep ledger summed over fixed persistent slots.
No event-restricted filtering or assumed travel bound is used. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def anchorPayments (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J, ∑ l : LevelMap.HeavySlot X, anchorPayment A D hk z j l t ω

def heavyParkChange (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
    |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω|

def refreshStep (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
    KeySizeTracker.charge (labelTracker A D hk z j l) t ω

theorem anchor_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ht : t<N) (ω : Ω) (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    frozenPotential A D hk z (t+1) (t+1) ω-frozenPotential A D hk z t t ω+
      anchorPayments A D hk z t ω ≤
      (frozenPotential A D hk z t (t+1) ω-frozenPotential A D hk z t t ω)+
      ((6/5)*132)*refreshStep A D hk z t ω+(12/5)*heavyParkChange A D hk z t ω := by
  have h := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>
    sum_le_sum (s:=univ) (fun l _=>anchor_slot_step A D hk z j l t ht ω hdiam))
  have hr : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
      KeySizeTracker.charge (labelTracker A D hk z j (Sum.inl l)) t ω) ≤ refreshStep A D hk z t ω := by
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    rw [Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (sum_nonneg fun l _=>sizeCharge_nonneg _ _ _)
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ (6/5:ℝ)*132 by norm_num)
  simp only [sum_add_distrib,sum_sub_distrib] at h
  dsimp only [frozenPotential,anchorPayments,heavyParkChange]
  simp only [mul_sum,mul_assoc,mul_comm] at h hm ⊢
  linarith only [h,hm]

theorem frozen_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (ω : Ω) : 0 ≤ frozenPotential A D hk z t s ω :=
  sum_nonneg fun j _=>sum_nonneg fun l _=>anchorTerm_nonneg A D hk z j l t t s t ω

omit [MetricSpace X] in
theorem weighted_parks (A : ActualPartitions.Config X) (a : Allocation (shape A k J) k) :
    (∑ v,weight A v*park (shape A k J) a.amount v) ≤ A.R*k := by
  calc
    _ ≤ ∑ v,A.R*park (shape A k J) a.amount v := by
      apply sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_right _ (a.park_nonneg v)
      have h := radius_antitone A (show 0 ≤ depth (shape A k J) v from Nat.zero_le _)
      simpa only [weight,radius,pow_zero,mul_one] using h
    _ = _ := by rw [←mul_sum,TreeParking.total]

theorem frozen_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : frozenPotential A D hk z t t ω ≤ (6/5)*A.R*k := by
  let a := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω
  have hb := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>
    sum_le_sum (s:=univ) (fun l _=>anchorTerm_bound A D hk z j l t t t ω))
  have hh : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
      labelPark A D hk z j (Sum.inl l) t ω) ≤ ∑ v,weight A v*park (shape A k J) a.amount v := by
    have he : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
        labelPark A D hk z j (Sum.inl l) t ω) ≤
        ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,labelPark A D hk z j l t ω := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_right (sum_nonneg fun l _=>labelPark_nonneg A D hk z j _ t ω)
    unfold labelPark at he
    rw [weighted_label_sum] at he
    refine he.trans (sum_le_sum fun v _=>?_)
    by_cases hv : v=0
    · rw [ite_eq_left hv]
      exact mul_nonneg (radius_nonneg A _) (a.park_nonneg v)
    · rw [ite_eq_right hv]
      exact le_rfl
  have hm := mul_le_mul_of_nonneg_left (hh.trans (weighted_parks A a)) (show (0:ℝ) ≤ 6/5 by norm_num)
  change frozenPotential A D hk z t t ω ≤ _ at hb
  simp only [←mul_sum,mul_assoc] at hb hm
  linarith only [hb,hm]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Telescoping the actual retained-anchor potential, retaining the literal
allocation and true key-coordinate costs until the final financing step. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem variation_integral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) :
    (∑ t∈range H,average D.weight (fun ω=>variation (weight A)
      (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
      (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω)))=
    TreeAllocationMovement.movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A) := by
  let d := TreeCountData.data D (map A D hk z)
  change integral d H (fun t ω=>variation (weight A) (TreeAllocator.allocation d (by omega) t ω)
    (TreeAllocator.allocation d (by omega) (t+1) ω))=_
  simp only [variation]
  rw [integral_sum]
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · simp only [hv,ite_true, if_true,integral,RankTracking.average,mul_zero,sum_const_zero]
  · simp only [ite_eq_right hv,nodeMove,integral,RankTracking.average,mul_sum]
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro ω _
    dsimp only [TreeAllocator.allocation,d]
    ring

theorem refresh_integral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) :
    (∑ t∈range H,average D.weight (refreshStep A D hk z t))=sizeRefresh A D hk z H :=
  (weighted_integral (fun j : Fin J=>GeometricMass.radius A.R A.q j.val) D.weight H
    (fun j l t ω=>KeySizeTracker.charge (labelTracker A D hk z j l) t ω)).symm

theorem park_change_integral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) :
    (∑ t∈range H,average D.weight (heavyParkChange A D hk z t)) ≤
    (1+1/22)*TreeAllocationMovement.movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A) := by
  have h := sum_le_sum (s:=range H) (fun t _=>PilotEdits.average_mono D.weight _ _
    (fun ω=>(D.positive ω).le) (heavy_park_variation A D hk z t))
  simp only [average_smul,←mul_sum,variation_integral] at h
  exact h

def payments (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) : ℝ := ∑ t∈range H,average D.weight (anchorPayments A D hk z t)

theorem payment_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    payments A D hk z N ≤
      ((6/5)*132)*A.q*integral (TreeCountData.data D (map A D hk z)) N (coordinateCost A D hk z)+
      (driftLog k/3)*(∑ t∈range N,average D.weight (fun ω=>dist (D.position t ω (D.chosen t ω)) (D.request t ω)))+
      ((6/5)*132)*sizeRefresh A D hk z N+
      (12/5)*(1+1/22)*TreeAllocationMovement.movement (TreeCountData.data D (map A D hk z)) (by omega) N (weight A)+
      (6/5)*A.R*k := by
  have hs (t : ℕ) (ht : t∈range N) := PilotEdits.average_mono D.weight _ _
    (fun ω=>(D.positive ω).le) (fun ω=>anchor_step A D hk z t (mem_range.mp ht) ω hdiam)
  have ht := sum_le_sum hs
  simp only [average_add,average_sub,average_smul,sum_add_distrib,←mul_sum] at ht
  have htel := sum_range_sub (fun t=>average D.weight (frozenPotential A D hk z t t)) N
  rw [htel,refresh_integral] at ht
  have hd := sum_le_sum (s:=range N) (fun t _=>expected_drift A D hk z t hdiam)
  simp only [average_add,average_sub,average_smul,←mul_sum,sum_add_distrib] at hd
  have hp := park_change_integral A D hk z N
  have hzero : 0 ≤ average D.weight (fun ω=>frozenPotential A D hk z N N ω) :=
    sum_nonneg fun ω _=>mul_nonneg (D.positive ω).le (frozen_nonneg A D hk z N N ω)
  have hinit : average D.weight (fun ω=>frozenPotential A D hk z 0 0 ω) ≤ (6/5)*A.R*k := by
    have h := PilotEdits.average_mono D.weight _ _ (fun ω=>(D.positive ω).le) (frozen_bound A D hk z 0)
    simpa only [average,←sum_mul,D.total,one_mul] using h
  dsimp only [payments,integral,TreeCountData.data] at *
  change (average D.weight (fun ω=>frozenPotential A D hk z N N ω)-
    average D.weight (fun ω=>frozenPotential A D hk z 0 0 ω))+_ ≤ _ at ht
  simp only [average,RankTracking.average] at ht hd hp hzero hinit ⊢
  nlinarith only [ht,hd,hp,hzero,hinit]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorTravel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Literal metric movement of retained heavy anchors, weighted by the new
parked mass. This is the travel used when projecting rounded tree servers. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def anchorTravel (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J, ∑ l : LevelMap.HeavySlot X,
    if retainedMoving A D hk z j l t ω then
      labelPark A D hk z j (Sum.inl l) (t+1) ω*
        dist ((heavyState A D hk z j t ω).center l) ((heavyState A D hk z j (t+1) ω).center l)
    else 0

theorem anchorTravel_le (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    anchorTravel A D hk z t ω ≤ 160*anchorPayments A D hk z t ω := by
  simp only [anchorTravel,anchorPayments,mul_sum]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro l _
  by_cases h : retainedMoving A D hk z j l t ω
  · rw [ite_eq_left h,anchorPayment,ite_eq_left h]
    have hd := LevelMap.Data.anchor_distance ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      (z j) t l h.1 h.2.1 h.2.2
    have hm := mul_le_mul_of_nonneg_left hd (labelPark_nonneg A D hk z j (Sum.inl l) (t+1) ω)
    change labelPark A D hk z j (Sum.inl l) (t+1) ω*
      dist ((heavyState A D hk z j t ω).center l) ((heavyState A D hk z j (t+1) ω).center l)
        ≤ _*(40*GeometricMass.radius A.R A.q j.val) at hm
    nlinarith only [hm]
  · simp only [ite_eq_right h,anchorPayment,mul_zero]
    exact le_rfl

def totalAnchorTravel (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) : ℝ := ∑ t∈range H,average D.weight (anchorTravel A D hk z t)

theorem totalAnchorTravel_le (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) : totalAnchorTravel A D hk z H ≤ 160*payments A D hk z H := by
  have h := sum_le_sum (s:=range H) (fun t _=>PilotEdits.average_mono D.weight _ _
    (fun ω=>(D.positive ω).le) (anchorTravel_le A D hk z t))
  simpa only [average_smul,←mul_sum,totalAnchorTravel,payments] using h

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CommonAnchorTravel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! The diagonal term of tree matching is genuine retained heavy-anchor travel.
No claim is made about an unsupported prefix. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def labelTravel (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) : Label X A.C k→ℝ
  | Sum.inl l => if retainedMoving A D hk z j l t ω then
      dist ((heavyState A D hk z j t ω).center l) ((heavyState A D hk z j (t+1) ω).center l) else 0
  | Sum.inr _ => 0

theorem labelTravel_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (l : Label X A.C k) :
    0≤labelTravel A D hk z j t ω l := by
  cases l <;> simp only [labelTravel]
  · split_ifs <;> first | exact dist_nonneg | exact le_rfl
  · exact le_rfl

omit [MetricSpace X] in
theorem all_label_sum (A : ActualPartitions.Config X) (f : Vertex (size A k J)→ℝ) (h0 : f 0=0) :
    (∑ j : Fin J,∑ l : Label X A.C k,∑ v∈labelVertices A j l,f v)=∑ v,f v := by
  simp_rw [label_fiber_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · subst v
    simp only [h0,ite_self,sum_const_zero]
  · have hp := depth_positive A v hv
    have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v
    let j : Fin J := ⟨depth (shape A k J) v-1,by omega⟩
    have hd : depth (shape A k J) v=j.val+1 := by dsimp [j]; omega
    calc
      _ = (if depth (shape A k J) v=j.val+1 then f v else 0) := by
        apply sum_eq_single j
        · intro i _ hi
          have hn : depth (shape A k J) v≠i.val+1 := by
            intro he; apply hi; apply Fin.ext; dsimp [j]; omega
          rw [ite_eq_right hn]
        · intro hj; exact (hj (mem_univ _)).elim
      _ = _ := ite_eq_left hd

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualRoundedStep
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Literal metric coupling of the actual consecutive allocated trees. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry BalancedStar
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem endpoint_anchor (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hJ : 0<J)
    (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) (p : X) :
    anchor A D hk z t ω ((map A D hk z).toLeaf t ω p)=p := by
  let v := (map A D hk z).toLeaf t ω p
  have hd : depth (shape A k J) v=J := PrefixTree.depth_at _ J (le_refl _)
  have hv : v≠0 := by intro he; rw [he,depth_root] at hd; omega
  have hm : p∈region A D hk z t ω v := mem_filter.mpr ⟨mem_univ _,desc_refl _⟩
  have ha := anchor_distance A D hk z t ω v hv p hm
  rw [hd] at ha
  by_contra hn
  have hh := hsmall p (anchor A D hk z t ω v) (Ne.symm hn)
  linarith

theorem rounded_serves (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hJ : 0<J)
    (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q)
    (s : State (shape A k J) k) (hs : Rounded (actualAllocation A D hk z (t+1) ω) s.value) :
    ∃ i,anchor A D hk z (t+1) ω (s.realization.tuple i)=D.request t ω := by
  obtain ⟨i,hi⟩ := realized_leaf_occupied (actualAllocation A D hk z (t+1) ω) s hs
    ((map A D hk z).toLeaf (t+1) ω (D.request t ω)) ((map A D hk z).leaf _ _ _)
    (TreeCountData.serves D (map A D hk z) (by omega) t ω)
  refine ⟨i,?_⟩
  rw [hi]
  exact endpoint_anchor A D hk z (t+1) ω hJ hsmall _

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Horizon-independent financing of literal retained-anchor metric travel.
All quantities here are expectations under the actual independent finite tape. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

local instance ixAF_r76ef31_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAF_r76ef31_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem coordinate_integral_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k) :
    (tapeLaw A N k J).expect (fun z=>integral (TreeCountData.data D (map A D hk z)) N
      (coordinateCost A D hk z))=totalCoordinate (N:=N) (J:=J) A D hk := by
  change (tapeLaw A N k J).expect (fun z=>∑ t∈range N,average D.weight (coordinateCost A D hk z t))=_
  rw [Law.expect_sum]
  exact sum_congr rfl (fun t _=>expect_average _ _ _)

theorem size_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k) :
    (tapeLaw A N k J).expect (fun z=>sizeRefresh A D hk z N) ≤
      288*KeySizeTracker.ell (k+1)*A.q*totalCoordinate (N:=N) (J:=J) A D hk+sizeEndpoint A k J := by
  have h := (tapeLaw A N k J).expect_mono _ _ (fun z=>size_budget A D hk z N)
  simpa only [Law.expect_add,Law.expect_const,Law.expect_mul,coordinate_integral_expect] using h

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteLawFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The assembled finite-law bound: the policy is a legal causal flow, the
coefficient is absolute squared-logarithmic, and the additive quantity knows
neither the horizon nor the request law. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.ixFF
local instance pairFF_r76ef31_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.PartitionTree.configEqFF
def lawFlow (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Data X (Fin k→X) (Fin k) :=
  RealFlow.mixture (R:=X) (C:=Fin k→X) (J:=Fin k) (Z:=Tape A k N J)
    (tapeLaw A N k J) (fun z=>componentFlow (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s)

end UniformKServer.PartitionTree

end

end OAI
end


