-- Prove2me | Definitions.Def_Q220Uk011
-- name    : Q220Uk011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:56:15.796308+00:00
-- url     : https://prove2.me/theorems/faaa3688-5bae-4162-8d5e-3522c02ef224
-- title:
--   Definitions bundle Q220Uk011 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 3 definitions and 24 theorems. The definitions and types are `OAI.UniformKServer.OffsetInstance.cap`, `OAI.UniformKServer.OffsetInstance.restart`, `OAI.UniformKServer.OffsetParameters.restart`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualPublicFlow`, `UniformKServer_ActualRoundingChain`, `UniformKServer_AnchorFinance`, `UniformKServer_CommonAnchorTravel`, `UniformKServer_FiniteLawFinance`, `UniformKServer_FiniteLawTheorem`, `UniformKServer_HorizonPolicy`, `UniformKServer_OfflineLaw`, `UniformKServer_OffsetExistence`, `UniformKServer_OffsetInstance`, `UniformKServer_OffsetParameters`, `UniformKServer_OffsetTable`, `UniformKServer_PublicFlow`, `UniformKServer_PublicRounding`, `UniformKServer_RoundingKernel`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`; the bundles `Q220Uk009` and `Q220Uk010` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.UniformKServer.ConstructorSearch.exists_certificate`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk009
import Definitions.Def_Q220Uk010

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

theorem common_label_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (j : Fin J) (l : Label X A.C k)
    (v : Vertex (size A k J)) (hv : v∈labelVertices A j l) :
    commonDistance (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)
      (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) v≤labelTravel A D hk z j t ω l := by
  unfold commonDistance
  split_ifs with hp
  · obtain ⟨p,hp'⟩ := park_witness A D hk z t ω v hp.1
    obtain ⟨q,hq'⟩ := park_witness A D hk z (t+1) ω v hp.2
    obtain ⟨_,hd,hl⟩ := mem_filter.mp hv
    have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
    have ho := last_region A D hk z t ω v h0 p hp'
    have hn := last_region A D hk z (t+1) ω v h0 q hq'
    have hi : (⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v h0; omega⟩ : Fin J)=j := by
      apply Fin.ext; change depth (shape A k J) v-1=j.val; omega
    rw [hi,hl] at ho hn
    rw [label_anchor A D hk z j l t ω v hv,label_anchor A D hk z j l (t+1) ω v hv]
    obtain he|⟨a,rfl,ha,hb⟩ := LevelMap.Data.supported_transition
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p q l ho.symm hn.symm
    · rw [he,dist_self]
      exact labelTravel_nonneg A D hk z j t ω l
    · change dist ((heavyState A D hk z j t ω).center a)
        ((heavyState A D hk z j (t+1) ω).center a)≤_
      by_cases he : (heavyState A D hk z j t ω).center a=(heavyState A D hk z j (t+1) ω).center a
      · rw [he,dist_self]; exact labelTravel_nonneg A D hk z j t ω (Sum.inl a)
      · change _ ≤ (if retainedMoving A D hk z j a t ω then _ else _)
        rw [ite_eq_left ⟨ha,hb,he⟩]
  · exact labelTravel_nonneg A D hk z j t ω l

theorem common_travel_le (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ v,park (shape A k J) (actualAllocation A D hk z (t+1) ω).amount v*
      commonDistance (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)
        (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) v)≤anchorTravel A D hk z t ω := by
  rw [←all_label_sum A _ (by simp [commonDistance,anchor,dist_self])]
  have he : anchorTravel A D hk z t ω=∑ j : Fin J,∑ l : Label X A.C k,
      labelPark A D hk z j l (t+1) ω*labelTravel A D hk z j t ω l := by
    simp only [anchorTravel,Fintype.sum_sum_type,labelTravel,mul_ite,mul_zero,sum_const_zero,add_zero]
  rw [he]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro l _
  change _≤(∑ v∈labelVertices A j l,park _ (actualAllocation A D hk z (t+1) ω).amount v)*_
  rw [sum_mul]
  exact sum_le_sum fun v hv=>mul_le_mul_of_nonneg_left (common_label_bound A D hk z t ω j l v hv)
    ((actualAllocation A D hk z (t+1) ω).park_nonneg v)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualRoundingChain
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Adapted rounded joint laws for the literal partition/allocation process,
with the exact financed movement bound. -/
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry FiniteProbability
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem roundingChain_cost (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (t : ℕ) (ω : Ω) :
    ((roundingChain A D hk z hdiam).joint t ω).expect
      (fun st=>stateDistance (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) st.1 st.2)≤
      15840*variation (weight A) (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)+
        anchorTravel A D hk z t ω := by
  have h := (roundingChain A D hk z hdiam).cost_bound t ω
  have hc := common_travel_le A D hk z t ω
  change _ ≤ 120*132*variation _ _ _+_ at h
  norm_num only [show (120:ℝ)*132=15840 by norm_num] at h
  exact h.trans (add_le_add (le_refl _) hc)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundingKernel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The adapted joint repair gives genuine conditional state transitions, with
both marginal identities and their exact transport expectation. -/
namespace UniformKServer.TreeRounding.ChainInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]
variable (D : ChainInput S k X Ω)

theorem first_law (t : ℕ) (ω : Ω) :
    (D.joint t ω).map Prod.fst=(D.distribution t ω).law := by
  apply FiniteProbability.Law.ext_expect
  intro f
  rw [Law.expect_map]
  exact D.first t ω f

theorem kernel_cost (t : ℕ) (ω : Ω) (f : State S k→State S k→ℝ) :
    (D.distribution t ω).law.expect (fun s=>(D.kernel t ω s).expect (f s))=
      (D.joint t ω).expect (fun st=>f st.1 st.2) := by
  have he (s : State S k) : (D.kernel t ω s).expect (f s)=
      ((D.joint t ω).conditional Prod.fst (D.joint t ω) s).expect (fun u=>f s u.2) :=
    Law.expect_map _ _ _
  simp_rw [he]
  rw [←D.first_law t ω]
  exact (D.joint t ω).disintegrate Prod.fst (D.joint t ω) (fun s st=>f s st.2)

theorem kernel_next (t : ℕ) (ω : Ω) :
    (D.distribution t ω).law.bind (D.kernel t ω)=(D.distribution (t+1) ω).law := by
  apply FiniteProbability.Law.ext_expect
  intro f
  rw [Law.expect_bind,D.kernel_cost t ω (fun _ u=>f u)]
  exact D.second t ω f

theorem kernel_rounded (t : ℕ) (ω : Ω) (s u : State S k)
    (hs : 0 < (D.distribution t ω).law.weight s) (hu : 0 < (D.kernel t ω s).weight u) :
    Rounded (D.allocation (t+1) ω) u.value := by
  rw [←D.first_law t ω] at hs
  obtain ⟨st,he,hst⟩ := map_positive _ Prod.snd u hu
  have hp := (D.joint t ω).conditional_positive Prod.fst (D.joint t ω) s hs st hst
  have hpos : 0 < ((D.joint t ω).map Prod.snd).weight u := by
    have hh := lt_of_lt_of_le hp.2 ((D.joint t ω).weight_le_map Prod.snd st)
    simpa only [he] using hh
  rw [D.second_law t ω] at hpos
  exact (D.distribution (t+1) ω).rounded u hpos

end UniformKServer.TreeRounding.ChainInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicRounding
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Causal rounded distributions are realized without exposing the hidden
trajectory. Only an observed request prefix selects the conditional rows. -/
namespace UniformKServer.TreeRounding
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]

namespace PublicInput
variable {D : ChainInput S k X Ω} (O : PublicInput D)

theorem process_marginal (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) :
    (((O.input.model hk).process (O.initial s) (O.trace t ω)).map Prod.fst)=
      (D.distribution t ω).law := by
  induction t with
  | zero => rw [O.trace_zero]; exact O.initial_first s ω
  | succ t ih =>
    rw [O.trace_snoc,MarkovFlow.Model.process_snoc,O.input.marginal_next hk,ih,O.kernel_trace,D.kernel_next]

theorem step (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω)
    (hcover : ∀ v : State S k,Rounded (D.allocation (t+1) ω) v.value →
      ∃ i,D.anchors (t+1) ω (v.realization.tuple i)=O.request t ω) :
    O.charge hk s t ω+O.potential hk s (t+1) ω≤O.potential hk s t ω+O.transport t ω := by
  let Q := (O.input.model hk).process (O.initial s) (O.trace t ω)
  have hh := O.input.step hk Q (O.trace t ω) (O.request t ω) (by
    intro v v' hv hv'
    rw [O.process_marginal hk s t ω] at hv
    rw [O.kernel_trace] at hv'
    rw [←O.trace_snoc,O.location_trace]
    exact hcover v' (D.kernel_rounded t ω v v' hv hv'))
  have hp : ((O.input.model hk).advance Q (O.trace t ω) (O.request t ω)).expect
      (O.input.potential (O.trace t ω++[O.request t ω]))=O.potential hk s (t+1) ω := by
    rw [potential,O.trace_snoc,MarkovFlow.Model.process_snoc]
  have ht : O.input.transport (Q.map Prod.fst) (O.trace t ω) (O.request t ω)=O.transport t ω := by
    unfold LazyMarkov.Input.transport
    rw [O.process_marginal hk s t ω,O.kernel_trace]
    simp_rw [O.location_trace t ω,←O.trace_snoc,O.location_trace (t+1) ω]
    rw [D.kernel_cost]
    rfl
  rw [hp,ht] at hh
  exact hh

theorem total_charge (hk : 0<k) (s : Fin k→X) (N : ℕ) (ω : Ω) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ)
    (hcover : ∀ t<N,∀ v : State S k,Rounded (D.allocation (t+1) ω) v.value →
      ∃ i,D.anchors (t+1) ω (v.realization.tuple i)=O.request t ω) :
    (∑ t∈range N,O.charge hk s t ω)≤(∑ t∈range N,O.transport t ω)+k*Δ := by
  have hh : (∑ t∈range N,O.charge hk s t ω)+O.potential hk s N ω≤
      (∑ t∈range N,O.transport t ω)+O.potential hk s 0 ω := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hh := ih (fun t ht=>hcover t (by omega))
      have hs := O.step hk s N ω (hcover N (by omega))
      simp only [sum_range_succ]
      linarith
  have h₀ := O.potential_initial hk s ω Δ hdiam
  have hn := O.potential_nonneg hk s N ω
  linarith

end PublicInput
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A rounded private process gives a literal nonnegative configuration/action
flow with legal zero-marginal rows and the same expected movement. -/
namespace UniformKServer.TreeRounding.PublicInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]
attribute [local instance] OAI.UniformKServer.TreeRounding.PublicInput.configEq
variable {D : ChainInput S k X Ω} (O : PublicInput D)

theorem flow_bound (hk : 0<k) (s : Fin k→X) (N : ℕ) (ω : Ω) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ)
    (hcover : ∀ t<N,∀ v : State S k,Rounded (D.allocation (t+1) ω) v.value →
      ∃ i,D.anchors (t+1) ω (v.realization.tuple i)=O.request t ω) :
    RealFlow.flowCost (O.flow hk s) (fun c r j=>dist (c j) r) [] (O.trace N ω)≤
      (∑ t∈range N,O.transport t ω)+k*Δ := by
  rw [O.flow_trace]
  exact O.total_charge hk s N ω Δ hdiam hcover

end UniformKServer.TreeRounding.PublicInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPublicFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Law-dependent but genuinely online configuration/action flows for the
actual pilot, partition, allocation, anchor, and rounding construction. -/

namespace UniformKServer.PartitionTree
open Finset FiniteProbability TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.configEq
theorem component_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J) (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) (ω : Ω) :
    RealFlow.flowCost (componentFlow A D hk z hdiam ω₀ hpublic s) (fun c r j=>dist (c j) r)
      [] (D.transcript N ω)≤
      15840*(∑ t∈range N,variation (weight A) (actualAllocation A D hk z t ω)
        (actualAllocation A D hk z (t+1) ω))+
      (∑ t∈range N,anchorTravel A D hk z t ω)+k*(40*A.R) := by
  have h := (publicInput A D hk z hdiam ω₀ hpublic).flow_bound (by omega) s N ω (40*A.R) hdiam
    (fun t _ v hv=>rounded_serves A D hk z t ω hJ hsmall v hv)
  have hsum := sum_le_sum (s:=range N) (fun t _=>roundingChain_cost A D hk z hdiam t ω)
  simp only [sum_add_distrib,←mul_sum] at hsum
  change _≤(∑ t∈range N,((roundingChain A D hk z hdiam).joint t ω).expect
    (fun st=>stateDistance (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) st.1 st.2))+_ at h
  change RealFlow.flowCost (componentFlow A D hk z hdiam ω₀ hpublic s) (fun c r j=>dist (c j) r) []
    (D.transcript N ω)≤_ at h
  linarith only [h,hsum]

end UniformKServer.PartitionTree

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

local instance ixAF_rba3ea7_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAF_rba3ea7_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem anchor_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    (tapeLaw A N k J).expect (fun z=>totalAnchorTravel A D hk z N) ≤
      anchorRate A k*(∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
        anchorEndpoint A k J := by
  have hp := (tapeLaw A N k J).expect_mono _ _ (fun z=>payment_budget A D hk z hdiam)
  simp only [Law.expect_add,Law.expect_const,Law.expect_mul,coordinate_integral_expect] at hp
  have hm : (∑ t∈range N,average D.weight (fun ω=>dist (D.position t ω (D.chosen t ω)) (D.request t ω)))=
      ∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t) := by
    apply sum_congr rfl
    intro t _
    simpa only [average,dist_comm] using (HiddenFlow.expected_mover_cost D t).symm
  rw [hm] at hp
  have hs := size_finance (N:=N) (J:=J) A D hk
  have hv := allocation_finance (N:=N) (J:=J) A D hk
  rw [add_assoc] at hv
  change _ ≤ allocationRate A k*_+allocationEndpoint A k J at hv
  have hc := coordinate_finance (N:=N) (J:=J) A D hk
  have he : 0 ≤ ((6/5:ℝ)*132)*(1+288*KeySizeTracker.ell (k+1)) := by
    have hl : 0 ≤ Real.log (k+1:ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
    unfold KeySizeTracker.ell
    positivity
  have hcm := mul_le_mul_of_nonneg_left hc he
  have ht := (tapeLaw A N k J).expect_mono _ _ (fun z=>totalAnchorTravel_le A D hk z N)
  rw [Law.expect_mul] at ht
  dsimp only [anchorRate,anchorEndpoint]
  nlinarith only [ht,hp,hs,hv,hcm]

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
local instance pairFF_rba3ea7_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.PartitionTree.configEqFF
theorem lawFlow_valid (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Valid (lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s)
      flowServe PublicInput.allowed s N :=
by
  apply RealFlow.mixture_valid
  intro z
  convert component_valid (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s using 1
  all_goals try with_reducible_and_instances rfl
  funext c r j a
  simp only [flowServe,Function.update_apply]

theorem component_average (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J) (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost (componentFlow (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      15840*movement (TreeCountData.data D (map A D hk z)) (by omega) N (weight A)+
      totalAnchorTravel A D hk z N+k*(40*A.R) := by
  have hh := average_mono D.weight _ _ (fun ω=>(D.positive ω).le)
    (component_bound (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s hJ hsmall)
  simp only [average_add,avg_constant _ D.total,average_smul,avg_range] at hh
  rw [show (∑t∈range N,average D.weight (fun ω=>variation (weight A)
      (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)))=
      movement (TreeCountData.data D (map A D hk z)) (by omega) N (weight A) from
        variation_integral A D hk z N] at hh
  convert hh using 1
  · apply congrArg (average D.weight)
    funext ω
    congr 1
    apply Subsingleton.elim
  · rfl

theorem lawFlow_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J) (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost (lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      (15840*allocationRate A k+anchorRate A k)*
        (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+flowEndpoint A k J := by
  have hh := (tapeLaw A N k J).expect_mono _ _ (fun z=>
    component_average (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s hJ hsmall)
  rw [expect_average] at hh
  simp only [Law.expect_add,Law.expect_mul,Law.expect_const] at hh
  have ha := allocation_finance (N:=N) (J:=J) A D hk
  rw [add_assoc] at ha
  change _≤allocationRate A k*_+allocationEndpoint A k J at ha
  have hb := anchor_finance (N:=N) (J:=J) A D hk hdiam
  simp only [lawFlow,RealFlow.mixture_cost]
  unfold flowEndpoint
  nlinarith only [hh,ha,hb]

theorem fixed_lawFlow_bound (R : ℝ) (hR : 0<R) (base : X)
    (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J)
    (hsmall : ∀ p q : X,p≠q → 20*radius (fixedConfig R hR base) J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost
      (lawFlow (N:=N) (J:=J) (fixedConfig R hR base) D hk hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      absoluteRate*(Real.log (k+1))^2*
        (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
      flowEndpoint (fixedConfig R hR base) k J := by
  have hh := lawFlow_bound (N:=N) (fixedConfig R hR base) D hk hdiam ω₀ hpublic s hJ hsmall
  have hm : 0≤∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t) :=
    sum_nonneg fun t _=>sum_nonneg fun ω _=>mul_nonneg (D.positive ω).le
      (sum_nonneg fun y _=>mul_nonneg ((HiddenFlow.flow D).mover_nonneg t ω y) dist_nonneg)
  have hc := mul_le_mul_of_nonneg_right (fixed_rate R hR base k (by omega)) hm
  linarith only [hh,hc]

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OfflineLaw
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! No hidden-trajectory hypothesis is added: an optimal finite serving history
is selected for each atom of an arbitrary finite request law. -/

namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeRounding
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.configEqOL
theorem literal_valid (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public) (s : Fin k→X) :
    RealFlow.Valid (lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s)
      (fun c r j=>Function.update c j r) PublicInput.allowed s N := by
  convert lawFlow_valid (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem literal_bound (R : ℝ) (hR : 0<R) (base : X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀p q : X,dist p q≤40*R) (ω₀ : Ω) (hpublic : D.Public) (s : Fin k→X)
    (hJ : 0<J) (hsmall : ∀p q : X,p≠q → 20*radius (fixedConfig R hR base) J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost
      (lawFlow (N:=N) (J:=J) (fixedConfig R hR base) D hk hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      absoluteRate*(Real.log (k+1))^2*(∑t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
        flowEndpoint (fixedConfig R hR base) k J := by
  convert fixed_lawFlow_bound (N:=N) (J:=J) R hR base D hk hdiam ω₀ hpublic s hJ hsmall using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (average D.weight)
  funext ω
  congr 1
  apply Subsingleton.elim

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteLawTheorem
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The finite-law theorem has arbitrary request atoms and literal offline OPT.
Its endpoint is fixed by the instance, before the law or horizon are chosen. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree PilotEdits TreeRounding
open scoped Classical
variable {n k : ℕ} [NeZero k]

attribute [local instance] OAI.UniformKServer.OfflineLaw.configEqFL
theorem finite_law (d : RationalMetric n) (s : Configuration n k) (hk : 2≤k) :
    ∃ B : ℝ,∀ (Ω : Type) [Fintype Ω] (N : ℕ) (word : Ω→List (Fin n)) (P : Law Ω),
      (∀ω,(word ω).length≤N) →
      ∃ F : RealFlow.Data (Fin n) (Configuration n k) (Fin k),
        RealFlow.Valid F serve PublicInput.allowed s N ∧
        P.expect (fun ω=>RealFlow.flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] (word ω))≤
          absoluteRate*(Real.log (k+1))^2*P.expect (fun ω=>offlineCost d s (word ω))+B := by
  let := d.metric
  let R := metricRadius (X:=Fin n)
  have hR : 0<R := metricRadius_pos
  let A := fixedConfig R hR (s 0)
  obtain ⟨J,hJ,hsmall⟩ := terminal_scale A
  refine ⟨flowEndpoint A k J,?_⟩
  intro Ω inst N word P hb
  let D := data d s word P
  let ω₀ : PositiveSupport.Support P.weight := Classical.choice (support_nonempty P)
  have hp : D.Public := data_public d s word P
  have hdiam : ∀p q : Fin n,dist p q≤40*A.R := metricRadius_bounds
  let F := lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hp s
  have hv : RealFlow.Valid F serve PublicInput.allowed s N := literal_valid A D hk hdiam ω₀ hp s
  refine ⟨F,hv,?_⟩
  have hbound := literal_bound (N:=N) (J:=J) R hR (s 0) D hk hdiam ω₀ hp s hJ hsmall
  have hcost := data_cost d s word P hb
  change (∑t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))=_ at hcost
  rw [hcost] at hbound
  have hpre (ω : PositiveSupport.Support P.weight) :
      RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω)≤
      RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (D.transcript N ω) := by
    apply RealFlow.flowCost_prefix hv _ (fun _ _ _=>dist_nonneg) _ _
      (by rw [D.transcript_length])
    rw [←data_trace d s word P ω]
    exact HiddenHistory.trace_prefix s _ _ _ (hb ω)
  have he : P.expect (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω))=
      average D.weight (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω)) :=
    (PositiveSupport.weighted_sum P.weight P.nonneg
      (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω))).symm
  change P.expect (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω))≤_
  rw [he]
  exact (average_mono D.weight _ _ (fun ω=>(D.positive ω).le) hpre).trans hbound

end UniformKServer.OfflineLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HorizonPolicy
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A single finite-horizon strongly lazy flow, now independent of the law. Its
additive endpoint is uniform over horizons and all words. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree FiniteFlowSpace RealFlow TreeRounding
open scoped Classical
variable {n k : ℕ} [NeZero k]

attribute [local instance] OAI.UniformKServer.OfflineLaw.configEqHP
theorem horizon_policy (d : RationalMetric n) (s : Configuration n k) (hk : 2≤k) :
    ∃ B : ℝ,∀ N : ℕ,∃ F : Data (Fin n) (Configuration n k) (Fin k),
      Valid F serve PublicInput.allowed s N ∧
      ∀w : List (Fin n),w.length≤N →
        flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] w≤
          absoluteRate*(Real.log (k+1))^2*offlineCost d s w+B := by
  obtain ⟨B,hB⟩ := finite_law d s hk
  refine ⟨B,?_⟩
  intro N
  let q : Word (Fin n) N→ℝ := fun v=>absoluteRate*(Real.log (k+1))^2*offlineCost d s (letters v)+B
  have hL (P : Law (Word (Fin n) N)) : ∃F : Data (Fin n) (Configuration n k) (Fin k),
      Valid F serve PublicInput.allowed s N ∧
      P.expect (fun v=>flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] (letters v))≤P.expect q := by
    obtain ⟨F,hF,hc⟩ := hB (Word (Fin n) N) N letters P letters_bound
    refine ⟨F,hF,?_⟩
    simpa only [q,Law.expect_add,Law.expect_mul,Law.expect_const] using hc
  obtain ⟨F,hF,hcost⟩ := eliminate serve PublicInput.allowed s
    (fun c r j=>(d.distance (c j) r : ℝ)) q hL
  refine ⟨F,hF,?_⟩
  intro w hw
  simpa only [q,letters_code] using hcost (code w hw)

end UniformKServer.OfflineLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetExistence
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Exact rational offset optimization with a bound fixed before the horizon.
The optimized offset, not an unproved zero-additive theorem, funds restarts. -/
namespace UniformKServer.OffsetLP
open EffectiveLP FourierMotzkin PartitionTree
open scoped Classical
variable {n k : ℕ} [NeZero k]

 theorem uniform_offset (d : RationalMetric n) (u : Config n k) (hk : 2≤k)
    (A : ℚ) (hA : absoluteRate*(Real.log (k+1))^2≤(A : ℝ)) :
    ∃ B : ℝ,0≤B ∧ ∀H : ℕ,∃x : Fin (Fintype.card (Variable n k H)+1)→ℚ,
      optimize (Fintype.card (Variable n k H)) (constraints d u A)=some x ∧
      Valid d u A (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) ∧
      ((FourierMotzkin.objective x : ℚ) : ℝ)≤B := by
  obtain ⟨B,hB⟩ := OfflineLaw.horizon_policy d u.val hk
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro H
  obtain ⟨F,hF,hc⟩ := hB H
  have hv : Valid d u A (restrict (H:=H) F) (max 0 B) :=
    restriction_valid d u A F _ hF (le_max_left _ _) (fun w hw=>by
      have hn : 0≤offlineCost d u.val w := by
        rw [OfflineDynamic.offline_eq_optRat]
        exact EffectiveLP.opt_nonneg d u.val w
      exact (hc w hw).trans (add_le_add (mul_le_mul_of_nonneg_right hA hn) (le_max_right _ _)))
  obtain ⟨x,hx,hv',hmin⟩ := rational_attainment d u A ⟨restrict F,max 0 B,hv⟩
  exact ⟨x,hx,hv',hmin _ _ hv⟩

end UniformKServer.OffsetLP

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetTable
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.OffsetTable
open EffectiveLP
open OffsetLP

theorem computed_uniform {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k)
    (hk : 2 ≤ k) (A : ℚ) (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀H : ℕ,
      OffsetLP.Valid d u A (flow (H:=H) d u A) (offset d u A H) ∧
      (offset d u A H : ℝ) ≤ B := by
  obtain ⟨B,hB,h⟩ := OffsetLP.uniform_offset d u hk A hA
  refine ⟨B,hB,?_⟩
  intro H
  obtain ⟨x,hx,hv,hv'⟩ := h H
  simpa only [flow,offset,assignment,hx,Option.getD_some] using And.intro hv hv'

end UniformKServer.OffsetTable

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                       
section

/-! Terminating rational search for the restart length. The uniform finite-law
endpoint is used only to prove termination, never supplied to the constructor. -/
namespace UniformKServer.OffsetParameters
open EffectiveLP ComputedInstance
variable {n k : ℕ} [NeZero k]

theorem search_exists (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ)
    (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) :
    ∃R : ℕ,acceptable hn d u A R := by
  obtain ⟨B,hB,hbound⟩ := OffsetTable.computed_uniform d u hk A hA
  obtain ⟨hD,hδ,hdiam,hsep,-⟩ := ComputedInstance.parameters hn (NeZero.pos k) d
  let W : ℝ := max ((k:ℝ)*(diameter hn d : ℝ)) B
  obtain ⟨R,hR⟩ := exists_nat_gt (W/(separation hn d : ℝ))
  have hW : 0 ≤ W := (by positivity : 0 ≤ ((k:ℝ)*(diameter hn d : ℝ))).trans (le_max_left _ _)
  have hpos : 0 < R := by
    have hg : (0:ℝ) < R := (div_nonneg hW hδ.le).trans_lt hR
    exact_mod_cast hg
  have hmul : W ≤ (R:ℝ)*(separation hn d : ℝ) :=
    ((div_lt_iff₀ hδ).mp hR).le
  refine ⟨R,hpos,?_,?_⟩
  · exact_mod_cast (le_max_left ((k:ℝ)*(diameter hn d : ℝ)) B).trans hmul
  · have he := (hbound (horizon k (cap (k:=k) hn d R))).2
    exact_mod_cast he.trans ((le_max_right _ _).trans hmul)

def restart (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ)
    (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) : ℕ :=
  Nat.find (search_exists hn hk d u A hA)

end UniformKServer.OffsetParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetInstance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

/-! Uniform absolute squared-log cost for the exact rational-search/dyadic
suffix, with arbitrary repeated starts and arbitrary finite activation delay.
The literal bit-machine implementation is deliberately not asserted here. -/
namespace UniformKServer.OffsetInstance

open EffectiveLP ComputedInstance
variable (mult : ℕ) (hm : PartitionTree.absoluteRate ≤ (mult : ℝ))
variable {n k : ℕ} [NeZero k]

def restart (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) : ℕ :=
  OffsetParameters.restart hn hk d (canonical hkn) (slope mult k) (rate_bound mult hm hk)

def cap (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) : ℕ :=
  OffsetParameters.cap (k:=k) hn d (restart mult hm hn hk hkn d)

end UniformKServer.OffsetInstance

end


end

end OAI
end


