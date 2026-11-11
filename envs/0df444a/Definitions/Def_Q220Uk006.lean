-- Prove2me | Definitions.Def_Q220Uk006
-- name    : Q220Uk006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:41:50.782202+00:00
-- url     : https://prove2.me/theorems/3e11d644-b3b1-413e-a4a2-d28789f28bd6
-- title:
--   Definitions bundle Q220Uk006 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 340 declarations of OpenAI's Lean: 104 definitions, 8 inductive types or structures and 228 theorems. The definitions and types are `OAI.UniformKServer.FineVariation.endpointVariation`, `OAI.UniformKServer.FiniteProbability.Law.bind`, `OAI.UniformKServer.FiniteProbability.Law.conditional`, `OAI.UniformKServer.FiniteProbability.Law.map`, `OAI.UniformKServer.FiniteProbability.Law.pure`, `OAI.UniformKServer.HiddenFlow.Data.Public`, `OAI.UniformKServer.HiddenFlow.Data.transcript`, `OAI.UniformKServer.HiddenFlow.regionCount`, `OAI.UniformKServer.LazyMarkov.Input`, `OAI.UniformKServer.LazyMarkov.Input.charge`, `OAI.UniformKServer.LazyMarkov.Input.model`, `OAI.UniformKServer.LazyMarkov.Input.potential`, `OAI.UniformKServer.LazyMarkov.Input.transport`, `OAI.UniformKServer.MarkovFlow.Model`, `OAI.UniformKServer.MarkovFlow.Model.actions`, `OAI.UniformKServer.MarkovFlow.Model.advance`, `OAI.UniformKServer.MarkovFlow.Model.evolve`, `OAI.UniformKServer.MarkovFlow.Model.flow`, `OAI.UniformKServer.MarkovFlow.Model.joint`, `OAI.UniformKServer.MarkovFlow.Model.process`, `OAI.UniformKServer.MarkovFlow.Model.successor`, `OAI.UniformKServer.ParkCoefficients.bad`, `OAI.UniformKServer.ParkCoefficients.inner`, `OAI.UniformKServer.ParkCoefficients.outer`, `OAI.UniformKServer.PartitionTree.absoluteRate`, `OAI.UniformKServer.PartitionTree.allocationRate`, `OAI.UniformKServer.PartitionTree.allocationScalar`, `OAI.UniformKServer.PartitionTree.anchorRate`, `OAI.UniformKServer.PartitionTree.fixedConfig`, `OAI.UniformKServer.PartitionTree.fixedExponent`, `OAI.UniformKServer.PartitionTree.fixedPilot`, `OAI.UniformKServer.PartitionTree.radius`, `OAI.UniformKServer.PartitionTree.rawRate`, `OAI.UniformKServer.PartitionTree.separationRate`, `OAI.UniformKServer.PrefixMovement.mark`, `OAI.UniformKServer.PrefixTree.atLevel`, `OAI.UniformKServer.PrefixTree.chart`, `OAI.UniformKServer.PrefixTree.endpoint`, `OAI.UniformKServer.PrefixTree.ranked`, `OAI.UniformKServer.PrefixTree.shape` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualAllocationBudget`, `UniformKServer_ActualCoordinateBudget`, `UniformKServer_ActualEditIntegration`, `UniformKServer_ActualPublicFlow`, `UniformKServer_ActualRoundedStep`, `UniformKServer_ActualSizeBudget`, `UniformKServer_AnchorFinance`, `UniformKServer_CurrentTesting`, `UniformKServer_Disintegration`, `UniformKServer_FineVariation`, `UniformKServer_FiniteFlow`, `UniformKServer_FiniteFlowCompact`, `UniformKServer_FiniteFlowMinimax`, `UniformKServer_FiniteFlowSpace`, `UniformKServer_FiniteSeparation`, `UniformKServer_FiniteTable`, `UniformKServer_GeometricMass`, `UniformKServer_HeavyAnchorGeometry`, `UniformKServer_HeavyKeyGeometry`, `UniformKServer_HeavyLabelParks`, `UniformKServer_HeavyRecordGeometry`, `UniformKServer_HiddenRegion`, `UniformKServer_HiddenTesting`, `UniformKServer_IntegerParks`, `UniformKServer_LaminarTransport`, `UniformKServer_LawKernel`, `UniformKServer_LawSupport`, `UniformKServer_LazyFinance`, `UniformKServer_LazyMarkov`, `UniformKServer_LevelAnchorContinuity`, `UniformKServer_LevelMap`, `UniformKServer_LevelParkCapacity`, `UniformKServer_MarkovFlow`, `UniformKServer_OfflineLaw`, `UniformKServer_OffsetRealization`, `UniformKServer_ParentScale`, `UniformKServer_ParkCapacity`, `UniformKServer_ParkScale`, `UniformKServer_ParkedTransport`, `UniformKServer_PartitionGeometry`, `UniformKServer_PartitionLaw`, `UniformKServer_PartitionMovement`, `UniformKServer_PrefixCounts`, `UniformKServer_PrefixMovement`, `UniformKServer_PrefixTree`, `UniformKServer_PublicRounding`, `UniformKServer_RankData`, `UniformKServer_RankFunctions`, `UniformKServer_RankedTree`, `UniformKServer_RealFlowMixture`, `UniformKServer_RoundedState`, `UniformKServer_RoundingChain`, `UniformKServer_SideFiniteInput`, `UniformKServer_SideParameterChanges`, `UniformKServer_SideRecurrence`, `UniformKServer_StarActualJumps`, `UniformKServer_StarAllocator`, `UniformKServer_StarBudget`, `UniformKServer_StarCaps`, `UniformKServer_StarConstants`, `UniformKServer_StarEnergy`, `UniformKServer_StarFeasibilityParameters`, `UniformKServer_StarIntegratedJumps`, `UniformKServer_StarLocalCharges`, `UniformKServer_StarLower`, `UniformKServer_StarMovementData`, `UniformKServer_StarOutputData`, `UniformKServer_StarRanks`, `UniformKServer_StarSchedules`, `UniformKServer_SwitchFinite`, `UniformKServer_TierLabeledKeys`, `UniformKServer_TierLabels`, `UniformKServer_TreeAllocationMovement`, `UniformKServer_TreeAncestry`, `UniformKServer_TreeCountData`, `UniformKServer_TreeCoverage`, `UniformKServer_TreeDistribution`, `UniformKServer_TreeLeaves`, `UniformKServer_TreeParking`, `UniformKServer_TreePosteriorRegions`, `UniformKServer_TreeRankData`, `UniformKServer_TreeRounding`, `UniformKServer_TreeTransport`, `UniformKServer_TypedStack`, `UniformKServer_UniformParameters`, `UniformKServer_UniformWrapper`, `UniformKServer_WrapperAlgebra`, `UniformKServer_WrapperInterpreter`, `UniformKServer_WrapperPrefix`, `UniformKServer_WrapperTransfer`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`; the bundles `Q220Uk000`, `Q220Uk001`, `Q220Uk002` and `Q220Uk003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk007` and `Q220Uk008`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk000
import Definitions.Def_Q220Uk001
import Definitions.Def_Q220Uk002
import Definitions.Def_Q220Uk003

section
-- module Solutions.Q220_UK.UniformKServer_RankFunctions
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

                                                                      
                                                          
noncomputable section
namespace UniformKServer.RankFunctions

theorem left_bound {β p : ℝ} (hβ : allowed β) (_hp : 0 ≤ p) (hpp : p ≤ pstar) :
    1/4 ≤ rank β p := by
  rw [rank, ite_eq_left hpp]
  have : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left hpp (by linarith [hβ.1])
  dsimp [pstar] at this
  nlinarith [hβ.2]

theorem sqrt_left {β p q : ℝ} (hβ : allowed β) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpp : p ≤ pstar) (hqq : q ≤ pstar) :
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*|p-q| := by
  have hlp := left_bound hβ hp hpp
  have hlq := left_bound hβ hq hqq
  have hsp : (1/2 : ℝ) ≤ Real.sqrt (rank β p) := by
    nlinarith [Real.sq_sqrt (rank_nonneg hβ (p := p)), Real.sqrt_nonneg (rank β p)]
  have hsq : (1/2 : ℝ) ≤ Real.sqrt (rank β q) := by
    nlinarith [Real.sq_sqrt (rank_nonneg hβ (p := q)), Real.sqrt_nonneg (rank β q)]
  calc
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ |rank β p-rank β q| :=
      sqrt_diff_aux (rank_nonneg hβ) (rank_nonneg hβ) (by linarith)
    _ = β*|p-q| := by
      simp only [rank, ite_eq_left hpp, ite_eq_left hqq]
      rw [show 1-β*p-(1-β*q) = -β*(p-q) by ring, abs_mul, abs_neg,
        abs_of_nonneg (by linarith [hβ.1] : 0 ≤ β)]
    _ ≤ 4*|p-q| := mul_le_mul_of_nonneg_right (by linarith [hβ.2]) (abs_nonneg _)

theorem sqrt_middle_eq (β p : ℝ) :
    Real.sqrt (middle β p) = h p*Real.sqrt (A β+B β*h p) := by
  have he : middle β p = (h p)^2*(A β+B β*h p) := by unfold middle; ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (h_nonneg _)]

end UniformKServer.RankFunctions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! Exact size rank and held core flags from companion §03. -/
noncomputable section
namespace UniformKServer.RankData
open RankFunctions

variable {Ω : Type*} [Fintype Ω]

variable {A : Type*} [Fintype A]

theorem core_decomposition (c : A → Bool) (β : ℝ) (p : A → ℝ)
    (hc : ∀ a, c a = true → p a ≤ pstar) :
    totalRank β p = coreCount c - β * coreMass c p + flex c β p := by
  unfold totalRank coreCount coreMass flex
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  cases he : c a with
  | true => simp [rank, hc a he]
  | false => simp

end UniformKServer.RankData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRecordGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! The actual center-set projection and common-label properties of the
finite-slot heavy-ball update. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ : Type*} [MetricSpace X] {r : ℝ}

variable [Fintype Λ]

theorem reused_distance (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (l : Λ) (ho : l ∈ S.present) (hn : l ∈ (insert S hr x R hR fresh hf).present) :
    dist (S.center l) ((insert S hr x R hR fresh hf).center l) ≤ 40*r := by
  by_cases he : l=chosen S x R fresh
  · subst l
    simp only [insert,Function.update_self]
    rcases chosen_cases S x R fresh with hh | ⟨he,_⟩
    · simpa only [dist_comm] using intersect_distance S x R _ hR.2 hh
    · exact (hf (he ▸ ho)).elim
  · simp only [insert,Function.update_of_ne he,dist_self]
    positivity

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabels
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Actual horizon/law independent pool sizes; labels remain reserved after a
record retires or becomes shadowed. All births are chronological identities. -/
noncomputable section
namespace UniformKServer.TierLabels
open Finset ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

omit [Fintype X] in
theorem reserved_zero (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) :
    reserved r K q c 0=∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  exact notMem_empty i (mem_filter.mp hi).1

omit [Fintype X] in
theorem birth_new (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) (n : Fin N)
    (hb : birth r K q c t=some n) : n∉reserved r K q c t := by
  have hn : n.val=t := by
    unfold birth at hb
    split_ifs at hb with ht hn
    · exact congrArg Fin.val (Option.some.inj hb).symm
  intro hi
  have hlt := TierSchedule.index_lt r K q c t n ((mem_filter.mp hi).1)
  omega

omit [Fintype X] in
theorem live_reserved (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) (τ : TierLifetimes.Tape N) :
    TierLifetimes.live r K q c t τ ⊆ reserved r K q c t :=
  (TierLifetimes.valid r K hK hq q c t).1 τ

end UniformKServer.TierLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabeledKeys
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance pairDecEq_rfac53c_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem key_witness (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (p : X) (l : Slot X K) (hl : key r K q c t τ ω p=some l) :
    ∃ i∈TierLabels.reserved r K q c t, TierKeyProcess.key r K q c t τ ω p=some i ∧
      (TierLabels.labels r K q c t).label i=l := by
  obtain ⟨i,hi,hlabel⟩ := Option.map_eq_some_iff.mp hl
  refine ⟨i,?_,hi,hlabel⟩
  exact TierLabels.live_reserved r K hK hq q c t τ
    ((mem_sort _).mp (TierKeys.key_mem _ _ _ c ω p i hi))

end UniformKServer.TierLabeledKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelMap
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! The literal level key: heavy precedence, then chronological tiers in their
fixed order, then singleton fallback. Its alphabet is fixed by the instance,
not by the finite law or horizon used to analyze the independent tape. -/
noncomputable section
namespace UniformKServer.LevelMap
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

namespace Data

local instance indexDecEq_rfac53c_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.LevelMap.tierDecEq
attribute [local instance] OAI.UniformKServer.LevelMap.pairDecEq
theorem first_witness {I J : Type*} (is : List I) (f : I → Option J) (j : J)
    (hj : FirstStructure.first is f=some j) : ∃ i∈is, f i=some j := by
  induction is with
  | nil => simp [FirstStructure.first] at hj
  | cons i is ih =>
    cases he : f i with
    | none =>
      have ht : FirstStructure.first is f=some j := by simpa only [FirstStructure.first,he,Option.none_or] using hj
      obtain ⟨a,ha,hf⟩ := ih ht
      exact ⟨a,List.mem_cons_of_mem _ ha,hf⟩
    | some k =>
      have hkj : k=j := Option.some.inj (by simpa only [FirstStructure.first,he,Option.some_or] using hj)
      exact ⟨i,List.mem_cons_self ..,hkj ▸ he⟩

theorem heavy_covers (D : Data X N H) (ω : Tape D) (t : ℕ) (p : X) (l : Label D)
    (hl : D.heavyKey ω t p=some l) : dist p (D.anchor ω t l)≤20*D.r := by
  obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hl
  have hc := (HeavyRecords.key_some _ D.positive.le p a).mp ha
  change dist p ((D.heavyState ω.1 t).center a)≤_
  rw [dist_comm]
  exact hc.2.trans ((D.heavyState ω.1 t).radius_bounds a hc.1).2

end Data
end UniformKServer.LevelMap

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_GeometricMass
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The actual geometric scales and the posterior ball masses at a request.
The shift comparison is proved from metric ball inclusion, rather than assumed
as an abstract scalar inequality. The scale count is independent of aspect. -/
noncomputable section
namespace UniformKServer.GeometricMass
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem mass_nonneg (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (a : ℝ) : 0 ≤ mass μ x a := by
  apply sum_nonneg
  intro y _
  split_ifs <;> [exact hμ y; exact le_rfl]

end UniformKServer.GeometricMass

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LawKernel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Exact push-forward and finite conditional kernels, including null rows. -/
noncomputable section
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ]

def Law.map (P : Law Ω) (f : Ω→Γ) : Law Γ where
  weight y := ∑ x,if f x=y then P.weight x else 0
  nonneg y := sum_nonneg (fun x _=>by split; exact P.nonneg x; exact le_rfl)
  total := by rw [sum_comm]; simp [P.total]

theorem Law.expect_map (P : Law Ω) (f : Ω→Γ) (g : Γ→ℝ) :
    (P.map f).expect g=P.expect (g ∘ f) := by
  simp only [Law.expect,Law.map,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

def Law.pure (x : Ω) : Law Ω where
  weight y := if y=x then 1 else 0
  nonneg y := by split <;> norm_num
  total := by simp

theorem Law.expect_pure (x : Ω) (f : Ω→ℝ) : (Law.pure x).expect f=f x := by simp [Law.expect,Law.pure]

def Law.bind (P : Law Ω) (K : Ω→Law Γ) : Law Γ where
  weight y := ∑ x,P.weight x*(K x).weight y
  nonneg y := sum_nonneg (fun x _=>mul_nonneg (P.nonneg x) ((K x).nonneg y))
  total := by rw [sum_comm]; simp only [←mul_sum,(K _).total,mul_one,P.total]

theorem Law.expect_bind (P : Law Ω) (K : Ω→Law Γ) (f : Γ→ℝ) :
    (P.bind K).expect f=P.expect (fun x=>(K x).expect f) := by
  simp only [Law.expect,Law.bind,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]

def Law.conditional (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (y : Γ) : Law Ω :=
  if h : 0<(P.map f).weight y then {
    weight x := (if f x=y then P.weight x else 0)/(P.map f).weight y
    nonneg x := div_nonneg (by split; exact P.nonneg x; exact le_rfl) h.le
    total := by rw [←sum_div]; exact div_self (ne_of_gt h) }
  else fallback

end UniformKServer.FiniteProbability

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LaminarTransport
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

                                                                              
                                                                           
                                            
noncomputable section
namespace UniformKServer.LaminarTransport
open Finset
open scoped Classical
variable {I V E : Type*} [Fintype I] [Fintype E] [DecidableEq V]

theorem no_opposite (C : E→Finset V) (a b : I→V) (hl : Laminar C)
    (π : Equiv.Perm I) (hπ : ∀ σ,objective C a b π≤objective C a b σ)
    (e : E) (i j : I) (hi : a i∈C e) (hbi : b (π i)∉C e)
    (hj : a j∉C e) (hbj : b (π j)∈C e) : False := by
  classical
  have hij : i≠j := by intro h; subst j; exact hj hi
  let σ := (Equiv.swap i j).trans π
  have hall : ∀ f,crossings (C f) a b σ ≤ crossings (C f) a b π := by
    intro f
    rw [crossings_swap _ _ _ _ _ _ hij]
    have h := cross_swap_le (hl e f) hi hbi hj hbj
    linarith
  have he : crossings (C e) a b σ < crossings (C e) a b π := by
    rw [crossings_swap _ _ _ _ _ _ hij]
    simp only [cross,bit,ite_eq_left hi,ite_eq_right hbi,ite_eq_right hj,ite_eq_left hbj]
    norm_num
  have hs : objective C a b σ<objective C a b π :=
    sum_lt_sum (fun f _=>hall f) ⟨e,mem_univ e,he⟩
  exact (not_lt_of_ge (hπ σ)) hs

theorem matching_exists (C : E→Finset V) (a b : I→V) (hl : Laminar C) :
    ∃ π : Equiv.Perm I,∀ e,crossings (C e) a b π=|mass (C e) a-mass (C e) b| := by
  classical
  obtain ⟨π,_,hπ⟩ := exists_min_image univ (objective C a b) (univ_nonempty : (univ : Finset (Equiv.Perm I)).Nonempty)
  refine ⟨π,fun e=>cut_identity (C e) a b π ?_⟩
  intro i j hi hbi hj hbj
  exact no_opposite C a b hl π (fun σ=>hπ σ (mem_univ σ)) e i j hi hbi hj hbj

end UniformKServer.LaminarTransport

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeRounding
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.TreeRounding
open UniformKServer.BalancedStar
noncomputable section

def Rounded {n k : ℕ} {S : Shape n} (a : Allocation S k)
    (x : Vertex n → ℤ) : Prop :=
  x 0 = k ∧ (∀ v, Balanced (a.amount v) (x v)) ∧
    ∀ v, Balanced (park S a.amount v) (intPark S x v)

structure Good {n k : ℕ} {S : Shape n} (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ) (s : ℕ) (E : Extension L n) : Prop where
  root : ∀ z, E.value z 0 = k
  balanced : ∀ u, assigned S s u → ∀ z, Balanced (b.amount u) (E.value z u)
  mean : ∀ u, assigned S s u → mean E.law (fun z => (E.value z u : ℝ)) = b.amount u
  parks : ∀ v, v.val < s → ∀ z,
    Balanced (park S b.amount v) (intPark S (E.value z) v)
  bound : ∀ v, v.val < s → localMovement S L X E v ≤
    32*localVariation a b v + 11*nodeMovement L X E v

theorem assign_child {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Children S v) :
    assignChildren S v old y u.val = y (.inl u) := by
  classical
  simp only [assignChildren, dite_eq_left u.property]
  congr 2

theorem assign_local {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ)
    (hy : ∑ i, y i = old v) :
    ∀ i, localInt S (assignChildren S v old y) v i = y i := by
  intro i
  cases i with
  | inl i => exact assign_child S v old y i
  | inr u =>
    cases u
    dsimp only [localInt,intPark]
    rw [assign_earlier S v old y v le_rfl]
    simp only [assign_child]
    rw [Fintype.sum_sum_type] at hy
    simp only [Fintype.sum_unique] at hy
    rw [sub_eq_iff_eq_add]
    simpa only [add_comm] using hy.symm

theorem good_zero {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ) :
    ∃ E : Extension L n, Good a b L X 0 E := by
  classical
  let E : Extension L n := {
    law := L, original := id, preserves := fun _ => rfl
    value := fun _ v => if v = 0 then (k:ℤ) else 0 }
  refine ⟨E,?_⟩
  constructor
  · intro z; simp [E]
  · intro u hu z
    have he : u=0 := hu.resolve_right (by omega)
    subst u
    simp only [E,b.root]
    unfold BalancedStar.Balanced
    exact Or.inl (by simp)
  · intro u hu
    have he : u=0 := hu.resolve_right (by omega)
    subst u
    simp only [E,b.root]
    exact mean_const L _
  · intro v hv; omega
  · intro v hv; omega

theorem weight_separation {n : ℕ} (S : Shape n) (w f : Vertex n → ℝ)
    (hsep : ∀ v, v ≠ 0 → 22*w v ≤ w (S.parent v))
    (hf : ∀ v, 0 ≤ f v) (hf0 : f 0 = 0) :
    22*(∑ v, w v*f v) ≤ ∑ v, if v=0 then 0 else w (S.parent v)*f v := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : v=0
  · simp [hv,hf0]
  · simp only [ite_eq_right hv]
    nlinarith [mul_le_mul_of_nonneg_right (hsep v hv) (hf v)]

end
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeParking
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Park conservation, subtree-cut capacities, and weighted park variation. -/
noncomputable section
namespace UniformKServer.TreeParking
open Finset TreeRounding
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem weighted_variation (a b : Allocation S k) (w : Vertex n → ℝ) (τ : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hτ : 0 < τ)
    (hsep : ∀ v, v ≠ 0 → τ*w v ≤ w (S.parent v)) :
    (∑ v, w v*|park S b.amount v-park S a.amount v|) ≤
      (1+1/τ)*variation w a b := by
  have h₁ : (∑ v, w v*|b.amount v-a.amount v|) ≤ (1/τ)*variation w a b := by
    unfold variation
    rw [mul_sum]
    apply sum_le_sum
    intro v _
    by_cases hv : v=0
    · simp [hv,a.root,b.root]
    · simp only [ite_eq_right hv]
      have hs : w v ≤ (1/τ)*w (S.parent v) := by
        have hh := (le_div_iff₀ hτ).2 (show w v*τ ≤ w (S.parent v) by simpa [mul_comm] using hsep v hv)
        simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh
      nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg (b.amount v-a.amount v))]
  calc
    _ ≤ ∑ v, w v*(|b.amount v-a.amount v|+∑ i : Children S v, |b.amount i.val-a.amount i.val|) :=
      sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (pointwise_variation a b v) (hw v)
    _ = (∑ v, w v*|b.amount v-a.amount v|)+variation w a b := by
      simp only [mul_add,sum_add_distrib]
      rw [weighted_children S w (fun v => |b.amount v-a.amount v|)]
      rfl
    _ ≤ _ := by linarith

end UniformKServer.TreeParking

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeAncestry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal ancestry in a finite ordered rooted tree, including all internal
parks and the root. -/
noncomputable section
namespace UniformKServer.TreeAncestry
open Finset TreeRounding TreeParking
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem depth_root : depth S 0=0 := by rw [depth,dite_eq_left rfl]
theorem depth_child (v : Vertex n) (hv : v ≠ 0) : depth S v=depth S (S.parent v)+1 := by rw [depth,dite_eq_right hv]

theorem desc_depth {u v : Vertex n} (h : descends S u v) : depth S u ≤ depth S v := by
  induction h with
  | refl => rfl
  | @tail v w h e ih => rw [depth_child w e.1,e.2]; omega

theorem desc_same_depth {u v : Vertex n} (h : descends S u v) (he : depth S u=depth S v) : u=v := by
  rcases h.cases_tail with hv | ⟨w,hw,e⟩
  · exact hv.symm
  · have hd := desc_depth hw
    rw [depth_child v e.1,e.2] at he
    omega

def ancestor (S : Shape n) (j : ℕ) (v : Vertex n) : Vertex n :=
  if _h : depth S v ≤ j then v else ancestor S j (S.parent v)
termination_by v.val
decreasing_by
  apply S.earlier
  intro he
  subst v
  exact _h (by rw [depth_root]; omega)

theorem ancestor_spec (j : ℕ) (v : Vertex n) (hj : j ≤ depth S v) :
    depth S (ancestor S j v)=j ∧ descends S (ancestor S j v) v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    rw [ancestor]
    split_ifs with hv
    · exact ⟨le_antisymm hv hj,desc_refl v⟩
    · have h0 : v ≠ 0 := by intro hh; subst v; exact hv (by rw [depth_root]; omega)
      have hp : j ≤ depth S (S.parent v) := by rw [depth_child v h0] at hj hv; omega
      have hh := ih (S.parent v) (S.earlier v h0) hp
      exact ⟨hh.1,desc_tail hh.2 h0 rfl⟩

theorem same_ancestor {u v w : Vertex n} (hu : descends S u w) (hv : descends S v w)
    (hd : depth S u=depth S v) : u=v := by
  induction w using WellFounded.induction (measure Fin.val).wf with
  | h w ih =>
    by_cases huw : u=w
    · subst u
      exact (desc_same_depth hv hd.symm).symm
    by_cases hvw : v=w
    · subst v
      exact desc_same_depth hu hd
    rcases hu.cases_tail with hw | ⟨p,hp,he⟩
    · exact (huw hw.symm).elim
    rcases hv.cases_tail with hw | ⟨q,hq,hf⟩
    · exact (hvw hw.symm).elim
    have hup : descends S u (S.parent w) := he.2.symm ▸ hp
    have hvp : descends S v (S.parent w) := hf.2.symm ▸ hq
    exact ih (S.parent w) (S.earlier w he.1) hup hvp

theorem ancestor_unique (j : ℕ) {u v : Vertex n} (h : descends S u v) (hd : depth S u=j) :
    ancestor S j v=u := by
  have ha := ancestor_spec j v (by rw [←hd]; exact desc_depth h)
  exact same_ancestor ha.2 h (ha.1.trans hd.symm)

end UniformKServer.TreeAncestry

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeLeaves
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Unique child on a leaf path and conservation of literal hidden counts. -/
noncomputable section
namespace UniformKServer.TreeLeaves
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {n : ℕ} {S : Shape n}

theorem child_path (v w : Vertex n) (hw : leaf (S:=S) w) (hv : Nonempty (Children S v))
    (h : descends S v w) : ∃! c : Children S v, descends S c.val w := by
  rcases h.cases_head with he | ⟨u,hu,huw⟩
  · subst w
    exact (hw (Classical.choice hv)).elim
  · let c : Children S v := ⟨u,hu⟩
    refine ⟨c,huw,?_⟩
    intro d hd
    apply Subtype.ext
    exact same_ancestor hd huw (by rw [depth_child _ d.property.1,depth_child _ hu.1,d.property.2,hu.2])

theorem indicator_root (w : Vertex n) : indicator (S:=S) 0 w=1 := ite_eq_left (root_descends w)

theorem indicator_children (v w : Vertex n) (hw : leaf (S:=S) w) (hv : Nonempty (Children S v)) :
    (∑ c : Children S v, indicator (S:=S) c.val w)=indicator (S:=S) v w := by
  by_cases h : descends S v w
  · obtain ⟨c,hc,hu⟩ := child_path v w hw hv h
    rw [sum_eq_single c]
    · simp only [indicator,ite_eq_left h,ite_eq_left hc]
    · intro d _ hdc
      exact ite_eq_right (fun hd => hdc (hu d hd))
    · simp
  · have hz (c : Children S v) : indicator (S:=S) c.val w=0 := by
      apply ite_eq_right
      intro hc
      exact h (hc.head c.property)
    rw [show indicator (S:=S) v w=0 from ite_eq_right h]
    exact sum_eq_zero (fun c _ => hz c)

theorem count_root {k : ℕ} (p : Fin k → Vertex n) : count (S:=S) p 0=k := by
  simp [count,indicator_root]

theorem count_children {k : ℕ} (p : Fin k → Vertex n) (hp : ∀ a, leaf (S:=S) (p a))
    (v : Vertex n) (hv : Nonempty (Children S v)) :
    (∑ c : Children S v, count (S:=S) p c.val)=count (S:=S) p v := by
  unfold count
  rw [sum_comm]
  simp only [indicator_children v _ (hp _) hv]

end UniformKServer.TreeLeaves

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeTransport
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The laminar cuts of the literal finite tree; exact matching transport and
an occupied-endpoint separating edge below a deepest common ancestor. -/
noncomputable section
namespace UniformKServer.TreeAncestry
open Finset TreeRounding
open scoped Classical
variable {n : ℕ} {S : Shape n}

theorem comparable_depth {u v w : Vertex n} (hu : descends S u w)
    (hv : descends S v w) (hd : depth S u≤depth S v) : descends S u v := by
  obtain ⟨he,ha⟩ := ancestor_spec (depth S u) v hd
  have hh := same_ancestor (ha.trans hv) hu he
  exact hh ▸ ha

theorem subtree_laminar : LaminarTransport.Laminar (subtree S) := by
  intro u v
  by_cases h : ∃ w,descends S u w ∧ descends S v w
  · obtain ⟨w,hu,hv⟩ := h
    rcases le_total (depth S u) (depth S v) with hd|hd
    · right; left
      intro x hx
      simp only [subtree,mem_filter,mem_univ,true_and] at hx ⊢
      exact (comparable_depth hu hv hd).trans hx
    · left
      intro x hx
      simp only [subtree,mem_filter,mem_univ,true_and] at hx ⊢
      exact (comparable_depth hv hu hd).trans hx
  · right; right
    apply disjoint_left.mpr
    intro w hu hv
    exact h ⟨w,(mem_filter.mp hu).2,(mem_filter.mp hv).2⟩

theorem matching {I : Type*} [Fintype I] (w : Vertex n→ℝ) (a b : I→Vertex n) :
    ∃ π : Equiv.Perm I,(∑ i,pathCost (S:=S) w (a i) (b (π i)))=
      ∑ c : Vertex n,if c=0 then 0 else w (S.parent c)*
        |LaminarTransport.mass (subtree S c) a-LaminarTransport.mass (subtree S c) b| := by
  obtain ⟨π,hπ⟩ := LaminarTransport.matching_exists (subtree S) a b subtree_laminar
  refine ⟨π,?_⟩
  unfold pathCost
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hc : c=0
  · simp [hc]
  · simp only [ite_eq_right hc,←mul_sum]
    rw [show (∑ i,LaminarTransport.cross (subtree S c) (a i) (b (π i)))=
      |LaminarTransport.mass (subtree S c) a-LaminarTransport.mass (subtree S c) b| from hπ c]

theorem separating_edge (u v : Vertex n) (hne : u≠v) :
    ∃ p c : Vertex n,descends S p u ∧ descends S p v ∧ c≠0 ∧
      depth S c=depth S p+1 ∧
      ((descends S c u ∧ ¬descends S c v) ∨ (descends S c v ∧ ¬descends S c u)) := by
  let F : Finset (Vertex n) := univ.filter (fun p=>descends S p u ∧ descends S p v)
  have hF : F.Nonempty := ⟨0,mem_filter.mpr ⟨mem_univ _,TreeLeaves.root_descends _,TreeLeaves.root_descends _⟩⟩
  obtain ⟨p,hp,hmax⟩ := exists_max_image F (depth S) hF
  have hpu := (mem_filter.mp hp).2.1
  have hpv := (mem_filter.mp hp).2.2
  have hdeep : depth S p<depth S u ∨ depth S p<depth S v := by
    have h₁ := desc_depth hpu
    have h₂ := desc_depth hpv
    by_contra h
    push Not at h
    exact hne ((desc_same_depth hpu (by omega)).symm.trans (desc_same_depth hpv (by omega)))
  have make (a b : Vertex n) (ha : descends S p a) (hb : descends S p b)
      (hd : depth S p<depth S a)
      (hm : ∀ c,descends S c a → descends S c b → depth S c≤depth S p) :
      ∃ c : Vertex n,c≠0 ∧ depth S c=depth S p+1 ∧ descends S c a ∧ ¬descends S c b := by
    let c := ancestor S (depth S p+1) a
    have hc := ancestor_spec (S:=S) (depth S p+1) a (by omega)
    have hcdepth : depth S c=depth S p+1 := hc.1
    have h0 : c≠0 := by intro he; have hz : depth S c=0 := he ▸ depth_root; dsimp [c] at hz; omega
    refine ⟨c,h0,hcdepth,hc.2,?_⟩
    intro hh
    have h := hm c hc.2 hh
    omega
  rcases hdeep with hd|hd
  · obtain ⟨c,h0,hc,ha,hb⟩ := make u v hpu hpv hd (fun c ha hb=>hmax c (mem_filter.mpr ⟨mem_univ _,ha,hb⟩))
    exact ⟨p,c,hpu,hpv,h0,hc,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨c,h0,hc,ha,hb⟩ := make v u hpv hpu hd (fun c ha hb=>hmax c (mem_filter.mpr ⟨mem_univ _,hb,ha⟩))
    exact ⟨p,c,hpu,hpv,h0,hc,Or.inr ⟨ha,hb⟩⟩

theorem edge_le_path (w : Vertex n→ℝ) (hw : ∀ c,0≤w c) (u v c : Vertex n)
    (hc : c≠0) (hcut : (descends S c u ∧ ¬descends S c v) ∨ (descends S c v ∧ ¬descends S c u)) :
    w (S.parent c)≤pathCost (S:=S) w u v := by
  have he : LaminarTransport.cross (subtree S c) u v=1 := by
    rcases hcut with ⟨hu,hv⟩|⟨hv,hu⟩ <;>
      simp [LaminarTransport.cross,LaminarTransport.bit,subtree,hu,hv]
  have h := single_le_sum (s:=(univ : Finset (Vertex n)))
    (fun a _=>show 0≤(if a=0 then 0 else w (S.parent a)*LaminarTransport.cross (subtree S a) u v) from by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw _) (abs_nonneg _)) (mem_univ c)
  simpa only [pathCost,ite_eq_right hc,he,mul_one] using h

end UniformKServer.TreeAncestry

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_IntegerParks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! A rounded, consistent hierarchy contains exactly k integer parks. Their
literal labeled enumeration has the prescribed subtree counts. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry BalancedStar
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem rounded_nonneg {a : Allocation S k} {x : Vertex n→ℤ}
    (hx : Rounded a x) (v : Vertex n) : 0≤x v :=
  (Int.floor_nonneg.mpr (a.nonneg v)).trans (balanced_bounds (hx.2.1 v)).1

theorem rounded_park_nonneg {a : Allocation S k} {x : Vertex n→ℤ}
    (hx : Rounded a x) (v : Vertex n) : 0 ≤ intPark S x v :=
  (Int.floor_nonneg.mpr (a.park_nonneg v)).trans (balanced_bounds (hx.2.2 v)).1

def integerAllocation (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x) : Allocation S k where
  amount v := x v
  nonneg v := by exact_mod_cast rounded_nonneg hx v
  park_nonneg v := by rw [park,←cast_intPark]; exact_mod_cast rounded_park_nonneg hx v
  root := by rw [hx.1]; simp

theorem intPark_total {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) :
    (∑ v : Vertex n,intPark S x v)=k := by
  have ht := TreeParking.total (integerAllocation a x hx)
  simp only [integerAllocation,park,←cast_intPark] at ht
  exact_mod_cast ht

theorem intPark_subtree {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x)
    (u : Vertex n) : (∑ v∈subtree S u,(intPark S x v:ℝ))=x u := by
  simpa only [integerAllocation,park,←cast_intPark] using subtree_total (integerAllocation a x hx) u

theorem intPark_nat_total {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) :
    (∑ v : Vertex n,(intPark S x v).toNat)=k := by
  have h : (∑ v : Vertex n,((intPark S x v).toNat:ℤ))=(k:ℤ) := by
    simp only [Int.toNat_of_nonneg (rounded_park_nonneg hx _)]
    exact intPark_total hx
  exact_mod_cast h

theorem realization_exists {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) :
    Nonempty (Realization (k:=k) (S:=S) x) := by
  let T := (v : Vertex n) × Fin (intPark S x v).toNat
  have hcard : Fintype.card T=k := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using intPark_nat_total hx
  let e : T≃Fin k := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fun i=>(e.symm i).1,?_,?_⟩⟩
  · intro f
    calc
      (∑ i,f (e.symm i).1)=∑ t : T,f t.1 := Equiv.sum_comp e.symm (fun t=>f t.1)
      _=∑ v,(intPark S x v:ℝ)*f v := by
        rw [Fintype.sum_sigma]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        apply sum_congr rfl
        intro v _
        congr 1
        exact_mod_cast Int.toNat_of_nonneg (rounded_park_nonneg hx v)
  · intro i
    have hp : 0<(intPark S x (e.symm i).1).toNat := Nat.zero_lt_of_lt (e.symm i).2.isLt
    have hz := Int.toNat_of_nonneg (rounded_park_nonneg hx (e.symm i).1)
    omega

def realize (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x) : Realization (k:=k) (S:=S) x :=
  Classical.choice (realization_exists hx)

theorem Realization.subtree {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) (u : Vertex n) :
    LaminarTransport.mass (TreeAncestry.subtree S u) R.tuple=x u := by
  rw [LaminarTransport.mass,R.sum]
  simp only [LaminarTransport.bit,mul_ite,mul_one,mul_zero,←sum_filter]
  simpa only [filter_mem_eq_inter,univ_inter] using intPark_subtree hx u

theorem Realization.valid {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) (i : Fin k) : 0<park S a.amount (R.tuple i) := by
  have hp := R.positive i
  have hb := (balanced_bounds (hx.2.2 (R.tuple i))).2
  by_contra he
  have hz := le_antisymm (not_lt.mp he) (a.park_nonneg _)
  rw [hz,Int.ceil_zero] at hb
  omega

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkedTransport
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! The literal one-step matching realization of joint tree rounding. The
coincident-label charge is restricted to labels occupied at both times. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [PseudoMetricSpace X]

theorem parked_matching (a b : Allocation S k) (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*pathCost (S:=S) w u v)
    {x y : Vertex n→ℤ} (hx : Rounded a x) (hy : Rounded b y)
    (R : Realization (k:=k) (S:=S) x) (T : Realization (k:=k) (S:=S) y) :
    ∃ π : Equiv.Perm (Fin k),
      (∑ i,dist (f (R.tuple i)) (g (T.tuple (π i))))≤
      G*(∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(y v:ℝ)-x v|)+
      ∑ v,(intPark S y v:ℝ)*commonDistance a b f g v := by
  obtain ⟨π,hπ⟩ := matching (S:=S) w R.tuple T.tuple
  refine ⟨π,?_⟩
  have hmatch : (∑ i,pathCost (S:=S) w (R.tuple i) (T.tuple (π i)))=
      ∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(y v:ℝ)-x v| := by
    rw [hπ]
    apply sum_congr rfl
    intro v _
    rw [R.subtree hx,T.subtree hy,abs_sub_comm]
  have hpoint (i : Fin k) : dist (f (R.tuple i)) (g (T.tuple (π i)))≤
      G*pathCost (S:=S) w (R.tuple i) (T.tuple (π i))+
        commonDistance a b f g (T.tuple (π i)) := by
    have hu := R.valid hx i
    have hv := T.valid hy (π i)
    by_cases he : R.tuple i=T.tuple (π i)
    · rw [he] at hu ⊢
      simp only [commonDistance]
      rw [ite_eq_left (And.intro hu hv)]
      have hn : 0≤pathCost (S:=S) w (T.tuple (π i)) (T.tuple (π i)) := by
        apply sum_nonneg
        intro v _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hw _) (abs_nonneg _)
      linarith [mul_nonneg hG hn]
    · exact (hgeo _ _ hu hv he).trans (le_add_of_nonneg_right (commonDistance_nonneg a b f g _))
  calc
    _≤∑ i,(G*pathCost (S:=S) w (R.tuple i) (T.tuple (π i))+
      commonDistance a b f g (T.tuple (π i))) := sum_le_sum (fun i _=>hpoint i)
    _=G*(∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(y v:ℝ)-x v|)+
      ∑ v,(intPark S y v:ℝ)*commonDistance a b f g v := by
        rw [sum_add_distrib,←mul_sum,hmatch]
        congr 1
        exact (T.permute π).sum _

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundedState
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! A fixed finite state space for the causal rounding kernels. It records
only bounded integer subtree counts, not an assumed distribution. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem rounded_le {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) (u : Vertex n) :
    x u≤k := by
  have hs : (∑ v∈subtree S u,(intPark S x v:ℝ))≤∑ v : Vertex n,(intPark S x v:ℝ) := by
    exact sum_le_univ_sum_of_nonneg (fun v=>by exact_mod_cast rounded_park_nonneg hx v)
  rw [intPark_subtree hx] at hs
  have ht : (∑ v : Vertex n,(intPark S x v:ℝ))=k := by exact_mod_cast intPark_total hx
  rw [ht] at hs
  exact_mod_cast hs

def stateOf (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) : State S k := by
  let c : Vertex n→Fin (k+1) := fun v=>⟨(x v).toNat,by have h₁ := rounded_nonneg hx v; have h₂ := rounded_le hx v; omega⟩
  have he : bounded c=x := by funext v; exact Int.toNat_of_nonneg (rounded_nonneg hx v)
  exact ⟨(c,R.tuple),by rw [he]; exact ⟨R.sum,R.positive⟩⟩

theorem stateOf_value (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) :
    (stateOf a x hx R).value=x := by
  funext v
  exact Int.toNat_of_nonneg (rounded_nonneg hx v)

theorem stateOf_tuple (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) :
    (stateOf a x hx R).realization.tuple=R.tuple := rfl

structure Distribution (a : Allocation S k) where
  law : FiniteProbability.Law (State S k)
  rounded : ∀ s,0<law.weight s → Rounded a s.value
  mean : ∀ v,law.expect (fun s=>(s.value v:ℝ))=a.amount v

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeDistribution
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Initial and next rounded configurations live in one fixed finite alphabet;
conditional extension states are eliminated by exact finite push-forward. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n}

def Law.finiteLaw (L : Law) : FiniteProbability.Law L.State := ⟨L.mass,L.nonneg,L.total⟩

def Distribution.supportLaw {a : Allocation S k} (P : Distribution a) : Law where
  State := PositiveSupport.Support P.law.weight
  finite := inferInstance
  mass s := P.law.weight s
  nonneg s := P.law.nonneg s
  total := PositiveSupport.total P.law.weight P.law.nonneg P.law.total

theorem Distribution.support_mean {a : Allocation S k} (P : Distribution a)
    (f : State S k→ℝ) : TreeRounding.mean P.supportLaw (fun s=>f s.val)=P.law.expect f :=
  PositiveSupport.weighted_sum P.law.weight P.law.nonneg f

theorem map_positive {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : FiniteProbability.Law Ω) (f : Ω→Γ) (y : Γ) (hy : 0<(P.map f).weight y) :
    ∃ x,f x=y ∧ 0<P.weight x := by
  by_contra he
  have hz (x : Ω) : (if f x=y then P.weight x else 0)=0 := by
    split_ifs with hx
    · exact le_antisymm (not_lt.mp (fun hp=>he ⟨x,hx,hp⟩)) (P.nonneg x)
    · rfl
  have hzero : (P.map f).weight y=0 := by simp only [FiniteProbability.Law.map,hz,sum_const_zero]
  linarith

variable {X : Type} [PseudoMetricSpace X]

structure Coupling (a b : Allocation S k) (P : Distribution a) where
  joint : FiniteProbability.Law (State S k × State S k)
  first : ∀ F : State S k→ℝ,joint.expect (F ∘ Prod.fst)=P.law.expect F
  next : Distribution b
  second : ∀ F : State S k→ℝ,joint.expect (F ∘ Prod.snd)=next.law.expect F

end UniformKServer.TreeRounding

end


end

end OAI
end

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

theorem Distribution.ext {a : Allocation S k} {P Q : Distribution a}
    (h : P.law=Q.law) : P=Q := by cases P; cases Q; cases h; rfl

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankedTree
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! A finite ranked rooted tree is enumerated in increasing rank and converted
to the ordered finite shapes used by the allocator and rounding proofs. -/
noncomputable section
namespace UniformKServer.RankedTree
open TreeRounding TreeAncestry
open scoped Classical

variable {V : Type*} [Fintype V]

def shape (T : Data V) : Shape (size T) where
  parent := fun v => if v=0 then 0 else (chart T).symm (T.parent (chart T v))
  earlier := by
    intro v hv
    simp only [ite_eq_right hv]
    have hn : chart T v ≠ T.root := by
      intro hh
      have he := congrArg (chart T).symm hh
      exact hv (by simpa only [Equiv.symm_apply_apply,root_vertex] using he)
    have hs := vertex_less T (T.parent (chart T v)) (chart T v) (by have hh := T.step _ hn; omega)
    simpa only [Fin.lt_def, Equiv.symm_apply_apply] using hs

theorem shape_parent (T : Data V) (v : Vertex (size T)) (hv : v ≠ 0) :
    (shape T).parent v=(chart T).symm (T.parent (chart T v)) := ite_eq_right hv

theorem depth_eq (T : Data V) (v : Vertex (size T)) : depth (shape T) v=T.level (chart T v) := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v
      rw [depth_root,chart_zero,T.level_root]
    · have hn : chart T v ≠ T.root := by
        intro hh
        exact hv (by simpa only [Equiv.symm_apply_apply,root_vertex] using congrArg (chart T).symm hh)
      rw [depth_child v hv,ih _ ((shape T).earlier v hv),shape_parent T v hv,Equiv.apply_symm_apply]
      exact T.step _ hn

end UniformKServer.RankedTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PrefixTree
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The full fixed finite wordPrefix universe. Its vertices include every formal
wordPrefix, without deleting presently empty branches. -/
noncomputable section
namespace UniformKServer.PrefixTree
open TreeRounding TreeAncestry TreeLeaves
open scoped Classical

variable {A : Type*} [Fintype A] {J : ℕ}

def ranked (A : Type*) [Fintype A] (J : ℕ) : RankedTree.Data (Word A J) where
  root := root
  parent := parent
  level := fun v => v.1.val
  level_root := rfl
  level_zero := by
    rintro ⟨d,p⟩ hd
    have he : d=0 := Fin.ext hd
    subst d
    change (⟨0,p⟩ : Word A J)=⟨0,Fin.elim0⟩
    exact congrArg (fun f : Fin 0 → A => (⟨0,f⟩ : Word A J)) (funext fun i => Fin.elim0 i)
  step := by
    intro v hv
    have hn : v.1.val ≠ 0 := by
      intro hz
      apply hv
      rcases v with ⟨d,p⟩
      have he : d=0 := Fin.ext hz
      subst d
      change (⟨0,p⟩ : Word A J)=⟨0,Fin.elim0⟩
      exact congrArg (fun f : Fin 0 → A => (⟨0,f⟩ : Word A J)) (funext fun i => Fin.elim0 i)
    simp only [parent,dite_eq_right hn]
    omega

abbrev size (A : Type*) [Fintype A] (J : ℕ) := RankedTree.size (ranked A J)
def shape (A : Type*) [Fintype A] (J : ℕ) : Shape (size A J) := RankedTree.shape (ranked A J)
def chart (A : Type*) [Fintype A] (J : ℕ) : Vertex (size A J) ≃ Word A J := RankedTree.chart (ranked A J)

def atLevel (p : Fin J → A) (d : ℕ) (hd : d ≤ J) : Vertex (size A J) :=
  (chart A J).symm (wordPrefix p d hd)
def endpoint (p : Fin J → A) : Vertex (size A J) := atLevel p J le_rfl

theorem depth_chart (v : Vertex (size A J)) : depth (shape A J) v=(chart A J v).1.val :=
  RankedTree.depth_eq (ranked A J) v

theorem depth_at (p : Fin J → A) (d : ℕ) (hd : d ≤ J) : depth (shape A J) (atLevel p d hd)=d := by
  rw [depth_chart]
  simp only [atLevel,Equiv.apply_symm_apply,wordPrefix]

theorem depth_bound (v : Vertex (size A J)) : depth (shape A J) v ≤ J := by
  rw [depth_chart]
  exact Nat.le_of_lt_succ (chart A J v).1.isLt

theorem at_nonzero (p : Fin J → A) (d : ℕ) (hd : d ≤ J) (hpos : 0 < d) : atLevel p d hd ≠ 0 := by
  intro hz
  have he := depth_at p d hd
  rw [hz,depth_root] at he
  omega

omit [Fintype A] in
theorem prefix_parent (p : Fin J → A) (d : ℕ) (hd : d+1 ≤ J) :
    parent (wordPrefix p (d+1) hd)=wordPrefix p d (by omega) := by
  unfold parent
  rw [dite_eq_right (show (wordPrefix p (d+1) hd).1.val ≠ 0 by change d+1 ≠ 0; omega)]
  rfl

theorem at_parent (p : Fin J → A) (d : ℕ) (hd : d+1 ≤ J) :
    (shape A J).parent (atLevel p (d+1) hd)=atLevel p d (by omega) := by
  unfold shape
  rw [RankedTree.shape_parent (ranked A J) _ (at_nonzero p (d+1) hd (by omega))]
  simp only [atLevel,chart,Equiv.apply_symm_apply]
  exact congrArg (RankedTree.chart (ranked A J)).symm (prefix_parent p d hd)

theorem at_descends (p : Fin J → A) (d e : ℕ) (he : e ≤ J) (hde : d ≤ e) :
    descends (shape A J) (atLevel p d (hde.trans he)) (atLevel p e he) := by
  induction e,hde using Nat.le_induction with
  | base => exact desc_refl _
  | succ e hde ih =>
    exact desc_tail (ih (by omega)) (at_nonzero p (e+1) he (by omega)) (at_parent p e he)

theorem endpoint_leaf (p : Fin J → A) : leaf (S:=shape A J) (endpoint p) := by
  intro c
  have hdep := depth_child (S:=shape A J) c.val c.property.1
  rw [c.property.2] at hdep
  have he : depth (shape A J) (endpoint p)=J := depth_at p J le_rfl
  rw [he] at hdep
  have hb := depth_bound c.val
  omega

theorem ancestor_endpoint (p : Fin J → A) (d : ℕ) (hd : d ≤ J) :
    ancestor (shape A J) d (endpoint p)=atLevel p d hd :=
  ancestor_unique d (at_descends p d J le_rfl hd) (depth_at p d hd)

theorem desc_endpoint (p : Fin J → A) (v : Vertex (size A J))
    (h : descends (shape A J) v (endpoint p)) :
    v=atLevel p (depth (shape A J) v) (depth_bound v) := by
  have he := ancestor_unique (depth (shape A J) v) h rfl
  rw [ancestor_endpoint p _ (depth_bound v)] at he
  exact he.symm

end UniformKServer.PrefixTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkCapacity
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Shared subtree capacity for parks at many depths. The geometry enters only
through nested regions, same-depth disjointness, and actual validity witnesses. -/
noncomputable section
namespace UniformKServer.ParkCapacity
open Finset TreeRounding TreeParking TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem grouped (a : Allocation S k) (T : Finset (Vertex n)) (j : ℕ)
    (hj : ∀ v ∈ T, j ≤ depth S v) :
    (∑ v ∈ T, park S a.amount v) ≤ ∑ u ∈ T.image (ancestor S j), a.amount u := by
  rw [←sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem (ancestor S j) hv)
    (fun v => park S a.amount v)]
  apply sum_le_sum
  intro u _
  rw [←subtree_total a u]
  apply sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨hv,he⟩ := mem_filter.mp hv
    simp only [subtree,mem_filter,mem_univ,true_and]
    rw [←he]
    exact (ancestor_spec j v (hj v hv)).2
  · intro v _ _
    exact a.park_nonneg v

variable {X : Type*} [Fintype X] [MetricSpace X]

theorem ancestor_region (G : Geometry S X) (j : ℕ) (y : X) (v : Vertex n)
    (hj : j ≤ depth S v) (z : X) (hz : z ∈ G.region v)
    (hzy : dist y z ≤ 27*G.radius (depth S v)) :
    G.region (ancestor S j v) ⊆ ball y (67*G.radius j) := by
  have ha := ancestor_spec j v hj
  have hza := G.nested _ _ ha.2 hz
  have hr := G.antitone hj
  intro x hx
  have hd := G.diameter (ancestor S j v) z hza x hx
  rw [ha.1] at hd
  simp only [ball,mem_filter,mem_univ,true_and]
  have ht := dist_triangle y z x
  nlinarith

theorem cumulative (a : Allocation S k) (G : Geometry S X) (μ : X → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ v, a.amount v ≤ C*mass μ (G.region v))
    (T : Finset (Vertex n)) (j : ℕ) (y : X)
    (hj : ∀ v ∈ T, j ≤ depth S v)
    (hw : ∀ v ∈ T, ∃ z ∈ G.region v, dist y z ≤ 27*G.radius (depth S v)) :
    (∑ v ∈ T, park S a.amount v) ≤ C*mass μ (ball y (67*G.radius j)) := by
  have hdepth : ∀ u ∈ T.image (ancestor S j), depth S u=j := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
    exact (ancestor_spec j v (hj v hv)).1
  have hsub : ∀ u ∈ T.image (ancestor S j), G.region u ⊆ ball y (67*G.radius j) := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
    obtain ⟨z,hz,hd⟩ := hw v hv
    exact ancestor_region G j y v (hj v hv) z hz hd
  calc
    _ ≤ ∑ u ∈ T.image (ancestor S j), a.amount u := grouped a T j hj
    _ ≤ ∑ u ∈ T.image (ancestor S j), C*mass μ (G.region u) := sum_le_sum fun u _ => hdom u
    _ = C*(∑ u ∈ T.image (ancestor S j), mass μ (G.region u)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (disjoint_mass μ hμ G _ j _ hdepth hsub) hC

end UniformKServer.ParkCapacity

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideParameterChanges
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! Prepared parameter jumps charged only to changed size coordinates (§04).
 Constants are independent of the number of children and of the smallest size. -/
noncomputable section
namespace UniformKServer.SideParameterChanges
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

def size (p : Config ι) : ι → ℝ := DomainTransport.extend p.active p.a

end UniformKServer.SideParameterChanges

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FineVariation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Fine endpoint movement is charged once, without the logarithmic weight
of the proportion potentials. Trackers continue through every epoch. -/
noncomputable section
namespace UniformKServer.FineVariation
open Finset RankFunctions RankData RankTracking FlexEstimates CoarseData
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def endpointVariation (I : A → Input Ω) (ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, (|estimate (I a) (rank 3) ξ (t+1) ω-estimate (I a) (rank 3) ξ t ω|+
    |estimate (I a) (rank (3+1/100)) ξ (t+1) ω-estimate (I a) (rank (3+1/100)) ξ t ω|)

end UniformKServer.FineVariation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParentScale
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Parent H is an actual persistent relative reference of the clipped sum
of persistent size trackers, not an oracle for the true size. -/
noncomputable section
namespace UniformKServer.ParentScale
open Finset RankData RankTracking CoarseData AllocationSchedule
open scoped Classical
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem estimate_change (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) :
    |estimateX I δ (t+1) ω-estimateX I δ t ω| ≤
      |sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω| := by
  unfold estimateX
  by_cases ha : cutoff ≤ sizeEstimate I δ (t+1) ω
  · rw [max_eq_left ha]
    by_cases hb : cutoff ≤ sizeEstimate I δ t ω
    · rw [max_eq_left hb]
    · rw [max_eq_right (le_of_not_ge hb),abs_of_nonneg (sub_nonneg.mpr ha),
        abs_of_nonneg (by linarith : 0 ≤ sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω)]
      linarith
  · rw [max_eq_right (le_of_not_ge ha)]
    by_cases hb : cutoff ≤ sizeEstimate I δ t ω
    · rw [max_eq_left hb,abs_of_nonpos (sub_nonpos.mpr hb),
        abs_of_nonpos (by linarith : sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω ≤ 0)]
      linarith
    · rw [max_eq_right (le_of_not_ge hb),sub_self,abs_zero]
      exact abs_nonneg _

end UniformKServer.ParentScale

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarRanks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! The actual rank processes of a finite hidden count law on its positive
support. No martingale or allocation estimate is part of the data. -/
noncomputable section
namespace UniformKServer.StarRanks
open Finset ConditionalLaw RankData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def flags (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) : Bool :=
  RankData.core (input d i j) t ω

def coreInput (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (fun j => (input d i j).posterior t ω) (flags d t ω i)

theorem child_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : d.count t ω i ≤ k :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (d.bound t ω)

theorem held_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ i, held d t ω i) ≤ 2*k := by
  have h : (∑ i, held d t ω i) ≤
      (11/10)*(∑ i, totalSize (fun j => (input d i j).posterior t ω)) := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => CoarseBridge.held_bound _ _ _
  have hs := size_sum d t ω
  have hp := parent_size_bound d t ω
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

end UniformKServer.StarRanks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarConstants
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! One absolute choice in the source's ordered smallness requirements.
All parameters remain independent of the star, k, law and horizon. -/
namespace UniformKServer.StarConstants
noncomputable section

theorem fine_error : rho+4*ParentBeta.cBeta*delta ≤ lam/4 := by
  norm_num [rho,ParentBeta.cBeta,delta,lam]
theorem fine_gap : 4*lam ≤ (ParentBeta.cBeta/50)/96 := by norm_num [lam,ParentBeta.cBeta]

end
end UniformKServer.StarConstants

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarSchedules
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The source star's actual causal data: persistent held sizes, parent refresh,
epochs, upper parameter and coarse dominant flexible-mass tracker. -/
noncomputable section
namespace UniformKServer.StarSchedules
open Finset StarRanks RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem refining (d : Data Ω ι k) {s t : ℕ} (hst : s ≤ t) {ω v : Ω}
    (h : (d.filtration t).r ω v) : (d.filtration s).r ω v := by
  induction hst with
  | refl => exact h
  | step hst ih => exact ih (d.refines _ _ _ h)

def parentRefresh (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : Bool :=
  decide (ParentScale.reference (parentInput d) δ (t+1) ω ≠ ParentScale.reference (parentInput d) δ t ω)

def upper (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ParentBeta.heldParam (parentInput d) δ k t ω

theorem upper_allowed (d : Data Ω ι k) {δ : ℝ} (hδ : 0 < δ) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    RankFunctions.allowed (upper d δ t ω) :=
  ParentBeta.held_allowed (parentInput d) hδ hk t ω (parent_size_bound d t ω)

end UniformKServer.StarSchedules

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

def factor (s : EpochGeometry.State ι) (k : ℕ) (i : ι) : ℝ :=
  if EpochGeometry.dominant s=some i then 1+StarConstants.lam/EpochAlpha.ell k
  else 1-StarConstants.lam/EpochAlpha.ell k

theorem tolerance (k : ℕ) :
    0 < StarConstants.rho/EpochAlpha.ell k ∧ StarConstants.rho/EpochAlpha.ell k < 1/2 := by
  have h := EpochAlpha.ell_one k
  have hp : 0 < EpochAlpha.ell k := by linarith
  refine ⟨div_pos StarConstants.rho_bounds.1 hp, (div_lt_iff₀ hp).2 ?_⟩
  linarith [StarConstants.rho_bounds.2]

theorem factor_range (s : EpochGeometry.State ι) (k : ℕ) (i : ι) :
    factor s k i ∈ Set.Icc (0:ℝ) 2 := by
  have h := EpochAlpha.ell_one k
  have hp : 0 < EpochAlpha.ell k := by linarith
  have h0 := div_nonneg StarConstants.lam_bounds.1.le hp.le
  have h1 : StarConstants.lam/EpochAlpha.ell k ≤ 1/4 := by
    apply (div_le_iff₀ hp).2
    linarith [StarConstants.lam_bounds.2]
  unfold factor
  split_ifs <;> constructor <;> linarith

end UniformKServer.StarCaps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarLower
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Actual lower requirements of a finite-count star.  This connects the
rank superadditivity to the output formulas, and proves the marked slack
from the logarithmic parameter gap (including zero side mass). -/
noncomputable section
namespace UniformKServer.StarLower
open Finset StarRanks RankData RankFunctions FlexEstimates
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def childBeta (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  ParentBeta.trueParam (input d i) k t ω

def parentBeta (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  ParentBeta.trueParam (parentInput d) k t ω

def lower (d : Data Ω ι k) (β : ℝ) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  totalRank β (fun j => (input d i j).posterior t ω)

def parentLower (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  totalRank (parentBeta d t ω) (fun j => (parentInput d j).posterior t ω)

theorem child_allowed (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    allowed (childBeta d t ω i) := by
  apply ParentBeta.true_allowed _ hk
  exact (StarParameters.child_le_parent d t ω i).trans (parent_size_bound d t ω)

theorem parent_allowed (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    allowed (parentBeta d t ω) :=
  ParentBeta.true_allowed _ hk _ _ (parent_size_bound d t ω)

theorem parameter_le (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    parentBeta d t ω ≤ childBeta d t ω i := by
  have hsize : ParentScale.trueX (input d i) t ω ≤ ParentScale.trueX (parentInput d) t ω :=
    max_le_max_right _ (StarParameters.child_le_parent d t ω i)
  have hpos := ParentScale.true_positive (input d i) t ω
  have hp := ParentScale.true_positive (parentInput d) t ω
  have hk0 : (0:ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hr := div_le_div_of_nonneg_left hk0.le hpos hsize
  have hl := Real.log_le_log (div_pos hk0 hp) hr
  have hc : 0 ≤ ParentBeta.cBeta/EpochAlpha.ell k :=
    div_nonneg (by norm_num [ParentBeta.cBeta]) (le_trans (by norm_num) (EpochAlpha.ell_one k))
  simpa [parentBeta,childBeta,ParentBeta.trueParam,ParentBeta.param,add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hl hc) 3

theorem decomposition (d : Data Ω ι k) (β : ℝ) (t : ℕ) (ω : Ω) (i : ι) :
    lower d β t ω i = coreCount (flags d t ω i)-β*coreInput d t ω i+
      trueFlex (input d i) β t ω := by
  apply core_decomposition
  intro j hj
  have h := core_small (input d i j) t ω hj
  norm_num [pstar] at h ⊢
  linarith

theorem inactive (d : Data Ω ι k) (β : ℝ) (t : ℕ) (ω : Ω) (i : ι)
    (hi : held d t ω i=0) :
    lower d β t ω i=0 ∧ trueFlex (input d i) β t ω=0 := by
  cases hb : CoarseData.activeState (input d i) t ω with
  | none =>
    have hz := CoarseData.inactive_zero (input d i) t ω β hb
    exact ⟨hz.2.1,hz.2.2⟩
  | some b =>
    have ha := CoarseData.active_accuracy (input d i) t ω hb
    change CoarseData.heldSize (input d i) t ω=0 at hi
    rw [CoarseBridge.held_some (input d i) t ω hb] at hi
    norm_num [CoarseData.cutoff] at ha
    exfalso
    nlinarith [ha.1,ha.2.2]

theorem lower_nonneg (d : Data Ω ι k) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ lower d β t ω i := by
  unfold lower totalRank
  exact sum_nonneg fun _ _ => rank_nonneg hβ

theorem core_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ coreInput d t ω i :=
  SyntheticCore.input_nonneg (fun j => ((input d i j).posterior_range t ω).1) _

theorem flex_mono (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    trueFlex (input d i) (childBeta d t ω i) t ω ≤
      trueFlex (input d i) (parentBeta d t ω) t ω := by
  have hg := (gap_bounds (input d i) (parent_allowed d hk t ω) t ω).1
  have hT := flex_nonneg (input d i) (parent_allowed d hk t ω) t ω
  have hgn : 0 ≤ flexGap (input d i) t ω := (div_nonneg hT (by norm_num)).trans hg
  rw [flex_affine (input d i) (parentBeta d t ω)]
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr (parameter_le d hk t ω i)) hgn)

/-- No active-size or positive side-mass hypothesis is used in this identity. -/
theorem lower_difference (d : Data Ω ι k) (β γ : ℝ) (t : ℕ) (ω : Ω) (i : ι) :
    lower d β t ω i-lower d γ t ω i =
      (γ-β)*(coreInput d t ω i+flexGap (input d i) t ω) := by
  rw [decomposition,decomposition,flex_affine (input d i) β γ]
  ring

end UniformKServer.StarLower

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideRecurrence
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Persistent causal selection of the two actual side minimizers. Empty side
 domains and D=0 use the same compact update, with the source's free deletion. -/
noncomputable section
namespace UniformKServer.SideRecurrence
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem zero_state (p : Config ι) : DomainTransport.domain p.active 11 (fun _ => 0) := by
  exact ⟨fun _ => le_rfl,fun _ _ => rfl,by simp⟩

end UniformKServer.SideRecurrence

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

def activeFlag (p : Config ι) : ι → Bool := fun i => decide (i ∈ p.active)

end UniformKServer.SideFiniteInput

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarFeasibilityParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                
section

/-! Explicit room for the actual held parameters in the two output rules.
The inequalities include arbitrarily small dominant side proportions. -/
noncomputable section
namespace UniformKServer.StarFeasibilityParameters
open Finset StarRanks StarSchedules StarLower
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem regular_room_algebra {β γ η h ell : ℝ} (hl : 0 < ell) (hh : 1 ≤ h)
    (hβ : 0 ≤ β) (hβ4 : β ≤ 4) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hηb : η ≤ StarConstants.ct*h/ell)
    (hgap : (ParentBeta.cBeta/50)/ell*h ≤ γ-β) :
    (β+4*StarConstants.eps/ell)*(1+η) ≤ γ := by
  have heta := (le_div_iff₀ hl).mp hηb
  have hg : (ParentBeta.cBeta/50)*h ≤ (γ-β)*ell := by
    apply (div_le_iff₀ hl).mp
    calc
      _ = (ParentBeta.cBeta/50)/ell*h := by ring
      _ ≤ _ := hgap
  have hp := mul_le_mul_of_nonneg_left heta hβ
  have hp' := mul_le_mul_of_nonneg_right hβ4 (mul_nonneg StarConstants.ct_pos.le (by linarith : 0 ≤ h))
  have he : 4*StarConstants.eps*(1+η) ≤ 8*StarConstants.eps*h := by
    norm_num [StarConstants.eps] at *
    nlinarith only [hh,hη1]
  have hid : ((β+4*StarConstants.eps/ell)*(1+η))*ell =
      β*ell+β*(η*ell)+4*StarConstants.eps*(1+η) := by field_simp
  apply (mul_le_mul_iff_left₀ hl).mp
  rw [hid]
  norm_num [StarConstants.ct,StarConstants.eps,ParentBeta.cBeta] at hg hp hp' he ⊢
  nlinarith only [hg,hp,hp',he,hh]

end UniformKServer.StarFeasibilityParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarOutputData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Concrete data for the output rules, including the signed total cap error.
All rank and tracker quantities are derived from the finite hidden law. -/
noncomputable section
namespace UniformKServer.StarOutputData
open Finset StarRanks StarSchedules StarLower
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def core (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  RankData.coreCount (flags d t ω i)
def mass (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := ∑ i, coreInput d t ω i
def parentFlex (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  FlexEstimates.trueFlex (input d i) (parentBeta d t ω) t ω
def childFlex (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  FlexEstimates.trueFlex (input d i) (childBeta d t ω i) t ω

theorem mass_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ mass d t ω :=
  sum_nonneg fun i _ => core_nonneg d t ω i

theorem parent_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    0 ≤ parentLower d t ω := by
  unfold parentLower RankData.totalRank
  exact sum_nonneg fun _ _ => RankFunctions.rank_nonneg (parent_allowed d hk t ω)

theorem child_expand (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    AllocationOutputs.lower (core d t ω) (coreInput d t ω) (childFlex d t ω)
      (childBeta d t ω) i=StarLower.lower d (childBeta d t ω i) t ω i :=
  (decomposition d (childBeta d t ω i) t ω i).symm

end UniformKServer.StarOutputData

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

structure Data (Ω ι R : Type*) [Fintype Ω] [Fintype ι] [Fintype R] where
  core : AlphaFiniteInput.Data Ω ι R
  deficit : ℕ → Ω → ℝ
  nonneg : ∀ t ω, 0 ≤ deficit t ω
  measurable : ∀ t ω v, (core.filtration t).r ω v → deficit t ω=deficit t v
  reset : ℕ → Ω → Bool
  reset_measurable : ∀ t ω v, (core.filtration (t+1)).r ω v → reset t ω=reset t v

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
open Finset StarRanks StarSchedules StarLower StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem lower_mono (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    lower d (childBeta d t ω i) t ω i ≤ lower d (parentBeta d t ω) t ω i := by
  rw [decomposition,decomposition]
  have h := mul_le_mul_of_nonneg_right (parameter_le d hk t ω i) (core_nonneg d t ω i)
  linarith [flex_mono d hk t ω i]

theorem childBeta_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (i : ι) : childBeta d t ω i=childBeta d t v i := by
  have hp : (fun j => (input d i j).posterior t ω)=(fun j => (input d i j).posterior t v) :=
    funext fun j => (input d i j).posterior_measurable t ω v h
  simp only [childBeta,ParentBeta.trueParam,ParentScale.trueX,hp]

theorem lower_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (i : ι) :
    lower d (childBeta d t ω i) t ω i=lower d (childBeta d t v i) t v i := by
  unfold lower
  rw [childBeta_measurable d t h i]
  congr 1
  funext j
  exact (input d i j).posterior_measurable t ω v h

end UniformKServer.StarAllocator

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeRankData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Fixed-tree finite count laws. Internal counts are exactly sums of child
counts; leaves keep their own counts. All operations depend on the observed
finite filtration only. -/
noncomputable section
namespace UniformKServer.TreeRankData
open Finset TreeRounding RankTracking RankData RankFunctions
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def single (d : Data Ω S k) (v : Vertex n) : StarRanks.Data Ω Unit k where
  weight := d.weight
  positive := d.positive
  total := d.total
  filtration := d.filtration
  refines := d.refines
  count := fun t ω _ => d.count t ω v
  bound := by intro t ω; simpa using d.bound t ω v

def star (d : Data Ω S k) (v : Vertex n) : StarRanks.Data Ω (Children S v) k where
  weight := d.weight
  positive := d.positive
  total := d.total
  filtration := d.filtration
  refines := d.refines
  count := fun t ω i => d.count t ω i.val
  bound := by
    intro t ω
    by_cases h : Nonempty (Children S v)
    · rw [d.conserves t ω v h]
      exact d.bound t ω v
    · have : IsEmpty (Children S v) := not_nonempty_iff.mp h
      simp

def input (d : Data Ω S k) (v : Vertex n) : Fin k → Input Ω := StarRanks.input (single d v) ()
def beta (d : Data Ω S k) (v : Vertex n) (t : ℕ) (ω : Ω) : ℝ := ParentBeta.trueParam (input d v) k t ω
def lower (d : Data Ω S k) (v : Vertex n) (t : ℕ) (ω : Ω) : ℝ :=
  totalRank (beta d v t ω) (fun j => (input d v j).posterior t ω)

theorem child_lower (d : Data Ω S k) (v : Vertex n) (i : Children S v) (t : ℕ) (ω : Ω) :
    StarLower.lower (star d v) (StarLower.childBeta (star d v) t ω i) t ω i=lower d i.val t ω := rfl

theorem parent_input (d : Data Ω S k) (v : Vertex n) (hv : Nonempty (Children S v)) :
    StarRanks.parentInput (star d v)=input d v := by
  have he : (fun t ω => ∑ i : Children S v, d.count t ω i.val)=(fun t ω => d.count t ω v) :=
    funext fun t => funext fun ω => d.conserves t ω v hv
  unfold StarRanks.parentInput input StarRanks.input
  simp only [star,single,he]

theorem parent_lower (d : Data Ω S k) (v : Vertex n) (hv : Nonempty (Children S v)) (t : ℕ) (ω : Ω) :
    StarLower.parentLower (star d v) t ω=lower d v t ω := by
  simp only [StarLower.parentLower,StarLower.parentBeta,parent_input d v hv,lower,beta]

theorem allowed (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    RankFunctions.allowed (beta d v t ω) := StarLower.child_allowed (single d v) hk t ω ()

theorem lower_nonneg (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    0 ≤ lower d v t ω := by
  unfold lower totalRank
  exact sum_nonneg fun j _ => rank_nonneg (allowed d hk v t ω)

theorem lower_bound (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    lower d v t ω ≤ k := by
  calc
    _ ≤ ∑ _ : Fin k, (1:ℝ) := sum_le_sum fun j _ =>
      rank_le_one (allowed d hk v t ω) ((input d v j).posterior_range t ω).1
    _ = _ := by simp

theorem empty_parent (d : Data Ω S k) (v : Vertex n) [IsEmpty (Children S v)] (t : ℕ) (ω : Ω) :
    StarLower.parentLower (star d v) t ω=0 := by
  have hp (j : Fin k) : (StarRanks.parentInput (star d v) j).posterior t ω=1 := by
    change ConditionalLaw.posterior d.weight (d.filtration t)
      (fun x => ConditionalRank.indicator (∑ i : Children S v, d.count t x i.val) j) ω=1
    simp only [sum_of_isEmpty,ConditionalRank.indicator,Nat.zero_le,ite_true, if_true,ConditionalLaw.posterior,mul_one]
    exact ConditionalRanks.normalized_kernel _ _ _ (ne_of_gt (StarRanks.mass_pos (star d v) t ω))
  unfold StarLower.parentLower totalRank
  simp only [hp]
  apply sum_eq_zero
  intro j _
  exact rank_beyond (by norm_num [sstar])

theorem parent_le_lower (d : Data Ω S k) (hk : 1 ≤ k) (v : Vertex n) (t : ℕ) (ω : Ω) :
    StarLower.parentLower (star d v) t ω ≤ lower d v t ω := by
  by_cases h : Nonempty (Children S v)
  · exact (parent_lower d v h t ω).le
  · have : IsEmpty (Children S v) := not_nonempty_iff.mp h
    rw [empty_parent]
    exact lower_nonneg d hk v t ω

end UniformKServer.TreeRankData

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

def mean (d : Data Ω S k) (t : ℕ) (ω : Ω) (v : Vertex n) : ℝ :=
  ConditionalLaw.posterior d.weight (d.filtration t) (fun x => (d.count t x v : ℝ)) ω

theorem child_size_bound (d : Data Ω S k) (v : Vertex n) (i : Children S v) (t : ℕ) (ω : Ω) :
    StarRanks.held (star d v) t ω i ≤ (11/10)*mean d t ω i.val := by
  apply (CoarseBridge.held_bound _ t ω).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ConditionalRanks.size_le_mean d.weight (fun x => (d.positive x).le) (d.filtration t) ω
    (ne_of_gt (StarRanks.mass_pos (star d v) t ω)) (fun x => d.count t x i.val) k
    (fun x => d.bound t x i.val)

theorem root_mean (d : Data Ω S k) (hroot : ∀ t x, d.count t x 0=k) (t : ℕ) (ω : Ω) :
    mean d t ω 0=k := by
  unfold mean ConditionalLaw.posterior
  simp only [hroot,←sum_mul]
  have hn : ∑ x, ConditionalLaw.kernel d.weight (d.filtration t) ω x=1 :=
    ConditionalRanks.normalized_kernel d.weight (d.filtration t) ω (ne_of_gt (StarRanks.mass_pos (single d 0) t ω))
  rw [hn,one_mul]

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

structure Map (D : HiddenFlow.Data X Ω k) (S : Shape n) where
  toLeaf : ℕ → Ω → X → Vertex n
  leaf : ∀ t ω x, TreeLeaves.leaf (S:=S) (toLeaf t ω x)
  causal : ∀ t ω v, (D.filtration t).r ω v → toLeaf t ω=toLeaf t v

def data (D : HiddenFlow.Data X Ω k) (M : Map D S) : TreeRankData.Data Ω S k where
  weight := D.weight
  positive := D.positive
  total := D.total
  filtration := D.filtration
  refines := D.refines
  count := fun t ω => TreeLeaves.count (S:=S) (fun a => M.toLeaf t ω (D.position t ω a))
  bound := fun _t _ω v => count_le _ v
  conserves := fun t ω v hv => count_children _ (fun _a => M.leaf t ω _) v hv

theorem root (D : HiddenFlow.Data X Ω k) (M : Map D S) (t : ℕ) (ω : Ω) :
    (data D M).count t ω 0=k := count_root _

theorem served_count (D : HiddenFlow.Data X Ω k) (M : Map D S) (t : ℕ) (ω v : Ω)
    (hv : (D.filtration (t+1)).r ω v) :
    1 ≤ (data D M).count (t+1) v (M.toLeaf (t+1) ω (D.request t ω)) := by
  have hpos : D.position (t+1) v (D.chosen t v)=D.request t v := by rw [D.update,ite_eq_left rfl]
  have hmap := M.causal (t+1) ω v hv
  have hreq := D.request_measurable t ω v hv
  have he : TreeLeaves.indicator (S:=S) (M.toLeaf (t+1) ω (D.request t ω))
      (M.toLeaf (t+1) v (D.position (t+1) v (D.chosen t v)))=1 := by
    rw [hpos,←hmap,←hreq]
    exact ite_eq_left (desc_refl _)
  conv_lhs => rw [←he]
  exact single_le_sum (f := fun a => TreeLeaves.indicator (S:=S) (M.toLeaf (t+1) ω (D.request t ω))
    (M.toLeaf (t+1) v (D.position (t+1) v a))) (fun _ _ => Nat.zero_le _) (mem_univ (D.chosen t v))

end UniformKServer.TreeCountData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreePosteriorRegions
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! True posterior counts are exactly the mass of the current causal tree
region. This is an identity, not an auxiliary estimate assumed of a law. -/
noncomputable section
namespace UniformKServer.TreePosteriorRegions
open Finset TreeRounding TreeAncestry TreeLeaves ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {n k : ℕ} {S : Shape n}

def region (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (t : ℕ) (ω : Ω)
    (u : Vertex n) : Finset X := univ.filter (fun x => descends S u (M.toLeaf t ω x))

omit [Fintype X] in
theorem atom_sum (x : X) (R : Finset X) :
    (∑ y ∈ R, HiddenFlow.atom x y)=if x ∈ R then 1 else 0 := by
  simp only [HiddenFlow.atom]
  rw [sum_ite_eq]

theorem raw_count (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (t : ℕ)
    (ω z : Ω) (u : Vertex n) :
    (TreeLeaves.count (S:=S) (fun a => M.toLeaf t ω (D.position t z a)) u:ℝ)=
      ∑ y ∈ region D M t ω u, HiddenFlow.counts D t z y := by
  unfold TreeLeaves.count HiddenFlow.counts
  rw [sum_comm]
  simp only [Nat.cast_sum,atom_sum]
  apply sum_congr rfl
  intro a _
  simp only [TreeLeaves.indicator,region,mem_filter,mem_univ,true_and]
  split_ifs <;> norm_num

theorem mean_mass (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (t : ℕ)
    (ω : Ω) (u : Vertex n) :
    TreeCoverage.mean (TreeCountData.data D M) t ω u=
      ParkCapacity.mass (HiddenFlow.current D t ω) (region D M t ω u) := by
  unfold TreeCoverage.mean posterior ParkCapacity.mass HiddenFlow.current
  change (∑ z, kernel D.weight (D.filtration t) ω z*(TreeCountData.data D M).count t z u)=_
  have hh : (∑ z, kernel D.weight (D.filtration t) ω z*((TreeCountData.data D M).count t z u:ℝ))=
      ∑ z, kernel D.weight (D.filtration t) ω z*(∑ y ∈ region D M t ω u, HiddenFlow.counts D t z y) := by
    apply sum_congr rfl
    intro z _
    by_cases hz : (D.filtration t).r ω z
    · have he := M.causal t ω z hz
      change _ * (TreeLeaves.count (S:=S) (fun a => M.toLeaf t z (D.position t z a)) u:ℝ)=_
      rw [←he,raw_count D M t ω z u]
    · simp only [kernel,ite_eq_right hz,zero_mul]
  rw [hh]
  simp only [mul_sum]
  rw [sum_comm]
  rfl

end UniformKServer.TreePosteriorRegions

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

namespace UniformKServer.FiniteProbability
open Finset
variable {Ω : Type*} [Fintype Ω] {I : Type*}
theorem Law.expect_sum (P : Law Ω) (s : Finset I) (f : I→Ω→ℝ) :
    P.expect (fun ω=>∑ i∈s,f i ω)=∑ i∈s,P.expect (f i) := by
  simp only [Law.expect,mul_sum]
  rw [sum_comm]
end UniformKServer.FiniteProbability

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

def radius (A : ActualPartitions.Config X) (d : ℕ) : ℝ := A.R*A.q^d

omit [Fintype X] [MetricSpace X] in
theorem radius_nonneg (A : ActualPartitions.Config X) (d : ℕ) : 0 ≤ radius A d :=
  mul_nonneg A.R_pos.le (pow_nonneg A.q_pos.le _)

omit [Fintype X] [MetricSpace X] in
theorem radius_antitone (A : ActualPartitions.Config X) : Antitone (radius A) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one A.q_pos.le (by linarith [A.q_small]) hij) A.R_pos.le

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PrefixMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Height-free deterministic conversion of coordinate-key disagreements into
weighted subtree-count variation on the literal full prefix universe. -/
noncomputable section
namespace UniformKServer.PrefixMovement
open Finset TreeRounding TreeAncestry TreeLeaves PrefixTree
open scoped Classical
variable {A : Type*} [Fintype A] {J : ℕ}

theorem prefix_ext (p q : Fin J → A) (d : ℕ) (hd : d ≤ J)
    (h : ∀ i : Fin J, i.val < d → p i=q i) : atLevel p d hd=atLevel q d hd := by
  apply (chart A J).injective
  simp only [atLevel,Equiv.apply_symm_apply,wordPrefix]
  congr 1
  funext i
  exact h _ i.isLt

theorem prefix_disagreement (p q : Fin J → A) (d : ℕ) (hd : d ≤ J) :
    diff (atLevel p d hd) (atLevel q d hd) ≤ ∑ i : Fin J, if i.val < d then diff (p i) (q i) else 0 := by
  by_cases he : atLevel p d hd=atLevel q d hd
  · rw [diff,ite_eq_left he]
    exact sum_nonneg fun i _ => by split_ifs; exact diff_nonneg _ _; exact le_rfl
  · have hn : ∃ i : Fin J, i.val < d ∧ p i ≠ q i := by
      by_contra hh
      push Not at hh
      exact he (prefix_ext p q d hd hh)
    obtain ⟨i,hi,hn⟩ := hn
    rw [diff,ite_eq_right he]
    calc
      _ = (if i.val < d then diff (p i) (q i) else 0) := by rw [ite_eq_left hi,diff,ite_eq_right hn]
      _ ≤ _ := single_le_sum (f:=fun j : Fin J => if j.val < d then diff (p j) (q j) else 0)
        (fun j _ => by split_ifs; exact diff_nonneg _ _; exact le_rfl) (mem_univ i)

def mark (v : Vertex (size A J)) (p : Fin J → A) : ℝ :=
  if descends (shape A J) v (endpoint p) then 1 else 0

theorem mark_nonneg (v : Vertex (size A J)) (p : Fin J → A) : 0 ≤ mark v p := by
  unfold mark; split_ifs <;> norm_num

theorem mark_iff (v : Vertex (size A J)) (p : Fin J → A) :
    descends (shape A J) v (endpoint p) ↔ v=atLevel p (depth (shape A J) v) (depth_bound v) := by
  constructor
  · exact desc_endpoint p v
  · intro h
    conv_lhs => rw [h]
    exact at_descends p _ J le_rfl (depth_bound v)

theorem level_mark (p : Fin J → A) (d : Fin (J+1)) :
    (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v p else 0)=1 := by
  rw [sum_eq_single (atLevel p d.val (by omega))]
  · rw [depth_at,ite_eq_left rfl,mark]
    exact ite_eq_left (at_descends p d.val J le_rfl (by omega))
  · intro v _ hv
    by_cases hd : depth (shape A J) v=d.val
    · rw [ite_eq_left hd,mark,ite_eq_right]
      intro hh
      apply hv
      have he := desc_endpoint p v hh
      simpa only [hd] using he
    · exact ite_eq_right hd
  · simp

theorem level_variation (p q : Fin J → A) (d : Fin (J+1)) :
    (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then |mark v p-mark v q| else 0) ≤
      2*diff (atLevel p d.val (by omega)) (atLevel q d.val (by omega)) := by
  by_cases he : atLevel p d.val (by omega)=atLevel q d.val (by omega)
  · rw [diff,ite_eq_left he,mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro v _
    by_cases hd : depth (shape A J) v=d.val
    · have hp : mark v p=mark v q := by
        unfold mark
        rw [mark_iff,mark_iff]
        simp only [hd,he]
      rw [ite_eq_left hd,hp,sub_self,abs_zero]
    · exact ite_eq_right hd
  · rw [diff,ite_eq_right he,mul_one]
    calc
      _ ≤ ∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v p+mark v q else 0 := by
        apply sum_le_sum
        intro v _
        split_ifs
        · exact abs_sub_le_iff.mpr ⟨by linarith [mark_nonneg v q],by linarith [mark_nonneg v p]⟩
        · exact le_rfl
      _ = (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v p else 0)+
          (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v q else 0) := by
        rw [←sum_add_distrib]
        apply sum_congr rfl
        intro v _
        split_ifs <;> ring
      _ = _ := by rw [level_mark,level_mark]; norm_num

theorem depth_sum (f : Vertex (size A J) → ℝ) :
    (∑ v, f v)=∑ d : Fin (J+1), ∑ v, if depth (shape A J) v=d.val then f v else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  symm
  rw [sum_eq_single (⟨depth (shape A J) v,by have := depth_bound v; omega⟩ : Fin (J+1))]
  · exact ite_eq_left rfl
  · intro d _ hd
    exact ite_eq_right (fun he => hd (Fin.ext he.symm))
  · simp

theorem path_variation (p q : Fin J → A) (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (∑ v : Vertex (size A J), w (depth (shape A J) v)*|mark v p-mark v q|) ≤
      2*∑ d : Fin (J+1), w d.val*diff (atLevel p d.val (by omega)) (atLevel q d.val (by omega)) := by
  rw [depth_sum]
  calc
    _ = ∑ d : Fin (J+1), w d.val * ∑ v : Vertex (size A J),
        if depth (shape A J) v=d.val then |mark v p-mark v q| else 0 := by
      apply sum_congr rfl
      intro d _
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      split_ifs with hd
      · rw [hd]
      · rw [mul_zero]
    _ ≤ ∑ d : Fin (J+1), w d.val*(2*diff (atLevel p d.val (by omega)) (atLevel q d.val (by omega))) :=
      sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (level_variation p q d) (hw d.val)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring

theorem tail_depths (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i)
    (i N : ℕ) : (∑ d ∈ range N, if i<d then r (d-1) else 0) ≤ 2*r i := by
  by_cases hi : N ≤ i+1
  · have hz : (∑ d ∈ range N, if i<d then r (d-1) else 0)=0 := by
      apply sum_eq_zero
      intro d hd
      exact ite_eq_right (by have := mem_range.mp hd; omega)
    rw [hz]
    exact mul_nonneg (by norm_num) (hr i)
  · have hN : N=(i+1)+(N-(i+1)) := by omega
    rw [hN,sum_range_add]
    have hz : (∑ d ∈ range (i+1), if i<d then r (d-1) else 0)=0 := by
      apply sum_eq_zero
      intro d hd
      exact ite_eq_right (by have := mem_range.mp hd; omega)
    rw [hz,zero_add]
    have he : (∑ d ∈ range (N-(i+1)), if i < i+1+d then r (i+1+d-1) else 0)=
        ∑ d ∈ range (N-(i+1)), r (i+d) := by
      apply sum_congr rfl
      intro d _
      rw [ite_eq_left (by omega)]
      congr 1; omega
    rw [he]
    exact tail_bound r hr hdec i _

theorem spatial_variation (p q : Fin J → A) (r : ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i) :
    (∑ v : Vertex (size A J), edgeWeight r (depth (shape A J) v)*|mark v p-mark v q|) ≤
      4*∑ i : Fin J, r i.val*diff (p i) (q i) := by
  have hw (d : ℕ) : 0 ≤ edgeWeight r d := by unfold edgeWeight; split_ifs; exact le_rfl; exact hr _
  have hp := path_variation p q (edgeWeight r) hw
  have hs := sum_le_sum (s:=univ) (fun d (_ : d ∈ (univ : Finset (Fin (J+1)))) =>
    mul_le_mul_of_nonneg_left (prefix_disagreement p q d.val (by omega)) (hw d.val))
  have he : (∑ d : Fin (J+1), edgeWeight r d.val * ∑ i : Fin J, if i.val<d.val then diff (p i) (q i) else 0)=
      ∑ i : Fin J, (∑ d : Fin (J+1), if i.val<d.val then r (d.val-1) else 0)*diff (p i) (q i) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro d _
    by_cases hd : i.val<d.val
    · rw [ite_eq_left hd,ite_eq_left hd,edgeWeight,ite_eq_right (by omega)]
    · rw [ite_eq_right hd,ite_eq_right hd,mul_zero,zero_mul]
  rw [he] at hs
  have ht (i : Fin J) : (∑ d : Fin (J+1), if i.val<d.val then r (d.val-1) else 0) ≤ 2*r i.val := by
    simpa only [←Fin.sum_univ_eq_sum_range] using tail_depths r hr hdec i.val (J+1)
  have hb := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_right (ht i) (diff_nonneg (p i) (q i)))
  simp only [mul_assoc,←mul_sum] at hb
  linarith

end UniformKServer.PrefixMovement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PrefixCounts
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal subtree-count costs are controlled by labeled coordinate-key edits,
without a tree-height or cardinality factor. -/
noncomputable section
namespace UniformKServer.PrefixMovement
open Finset TreeRounding TreeAncestry TreeLeaves PrefixTree
open scoped Classical
variable {A : Type*} [Fintype A] {J k : ℕ}

theorem count_cast (p : Fin k→Fin J→A) (v : Vertex (size A J)) :
    (TreeLeaves.count (S:=shape A J) (fun a => endpoint (p a)) v : ℝ)=∑ a,mark v (p a) := by
  simp only [TreeLeaves.count,Nat.cast_sum,TreeLeaves.indicator,mark]
  apply sum_congr rfl
  intro a _
  split_ifs <;> norm_num

theorem count_variation (p q : Fin k→Fin J→A) (r : ℕ→ℝ)
    (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i) :
    (∑ v : Vertex (size A J), edgeWeight r (depth (shape A J) v)*
      |(TreeLeaves.count (S:=shape A J) (fun a => endpoint (p a)) v : ℝ)-
       TreeLeaves.count (S:=shape A J) (fun a => endpoint (q a)) v|)≤
    4*∑ a,∑ i : Fin J,r i.val*diff (p a i) (q a i) := by
  have hw (v : Vertex (size A J)) : 0≤edgeWeight r (depth (shape A J) v) := by
    unfold edgeWeight; split_ifs; exact le_rfl; exact hr _
  calc
    _ ≤ ∑ v : Vertex (size A J),edgeWeight r (depth (shape A J) v)*
      ∑ a,|mark v (p a)-mark v (q a)| := by
        apply sum_le_sum
        intro v _
        rw [count_cast,count_cast,←sum_sub_distrib]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hw v)
    _ = ∑ a,∑ v : Vertex (size A J),edgeWeight r (depth (shape A J) v)*
      |mark v (p a)-mark v (q a)| := by simp only [mul_sum]; rw [sum_comm]
    _ ≤ ∑ a,4*∑ i : Fin J,r i.val*diff (p a i) (q a i) :=
      sum_le_sum fun a _ => spatial_variation (p a) (q a) r hr hdec
    _ = _ := (mul_sum _ _ _).symm

end UniformKServer.PrefixMovement

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
open Finset StarRanks StarSchedules StarLower StarOutputData StarAllocator
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem eps_bound (k : ℕ) : 0 ≤ StarConstants.eps/EpochAlpha.ell k ∧
    StarConstants.eps/EpochAlpha.ell k ≤ 1/100 := by
  have he := EpochAlpha.ell_one k
  have hp : 0 < EpochAlpha.ell k := by linarith
  refine ⟨div_nonneg (by norm_num [StarConstants.eps]) hp.le,(div_le_iff₀ hp).2 ?_⟩
  norm_num [StarConstants.eps]
  linarith

end UniformKServer.StarMovementData

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

def endpoints (d : Data Ω ι k) (ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i, FineVariation.endpointVariation (input d i) ξ t ω

theorem endpoints_nonneg (d : Data Ω ι k) (ξ : ℝ) (t : ℕ) (ω : Ω) : 0 ≤ endpoints d ξ t ω :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem coarse_flex_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    FlexEstimates.estimateFlex (input d i) 3 sizeTolerance t ω ≤ 120*held d t ω i := by
  have h := ActualFineCaps.cap_bound (input d i) (β:=3) (factor:=1)
    (by norm_num [RankFunctions.allowed]) (show 0 < sizeTolerance by norm_num [sizeTolerance])
    (show sizeTolerance ≤ 1/2 by norm_num [sizeTolerance]) (by norm_num) t ω
  have hn : 0 ≤ RankData.coreCount (flags d t ω i) := sum_nonneg fun j _ => by split_ifs <;> norm_num
  change RankData.coreCount (flags d t ω i)+1*FlexEstimates.estimateFlex (input d i) 3 sizeTolerance t ω ≤ _ at h
  change _ ≤ 120*held d t ω i at h
  linarith

end UniformKServer.StarLocalCharges

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

def alphaScale (k : ℕ) : ℝ := StarConstants.multiplier*EpochAlpha.ell k
def sideSlope (k : ℕ) : ℝ := 2000*(EpochAlpha.ell k/StarConstants.cw+1)

theorem scale_nonneg (k : ℕ) : 0 ≤ alphaScale k :=
  mul_nonneg (by norm_num [StarConstants.multiplier]) (le_trans (by norm_num) (EpochAlpha.ell_one k))

theorem slope_nonneg (k : ℕ) : 0 ≤ sideSlope k := by
  have he := EpochAlpha.ell_one k
  unfold sideSlope
  exact mul_nonneg (by norm_num) (add_nonneg (div_nonneg (by linarith) StarConstants.cw_pos.le) (by norm_num))

end UniformKServer.StarActualJumps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Uniform-in-law coarse charges of the actual input. In particular a parent
refresh pays for the entire old and new star without a factor of ell. -/
noncomputable section
namespace UniformKServer.StarBudget
open Finset StarRanks StarSchedules RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem total_held_parent (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ i, held d t ω i) ≤ (11/10)*ParentScale.trueX (parentInput d) t ω := by
  calc
    _ ≤ (11/10)*(∑ i, RankData.totalSize (fun j => (input d i j).posterior t ω)) := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => CoarseBridge.held_bound _ _ _
    _ ≤ (11/10)*RankData.totalSize (fun j => (parentInput d j).posterior t ω) :=
      mul_le_mul_of_nonneg_left (size_sum d t ω) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)

theorem total_held_reference (d : Data Ω ι k) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (t : ℕ) (ω : Ω) : (∑ i, held d t ω i) ≤ 5*ParentScale.reference (parentInput d) δ t ω := by
  have hx := ParentScale.reference_comparison (parentInput d) hδ t ω
  have hr : 0 ≤ ParentScale.reference (parentInput d) δ t ω := by
    have hp := ParentScale.true_positive (parentInput d) t ω
    have hf : 0 < (1+δ)^2 := sq_pos_of_pos (by linarith)
    exact le_of_lt (pos_of_mul_pos_right (lt_of_lt_of_le hp hx.1) hf.le)
  have hf : (1+δ)^2 ≤ (4:ℝ) := by nlinarith [sq_nonneg δ]
  have hm := mul_le_mul_of_nonneg_right hf hr
  linarith [total_held_parent d t ω,hx.1]

theorem parent_step (d : Data Ω ι k) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (t : ℕ) (ω : Ω) :
    (if parentRefresh d δ t ω then EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤
      5*AllocationSchedule.charge (ParentScale.reference (parentInput d) δ t ω)
        (ParentScale.reference (parentInput d) δ (t+1) ω) := by
  unfold parentRefresh AllocationSchedule.charge
  by_cases he : ParentScale.reference (parentInput d) δ t ω=ParentScale.reference (parentInput d) δ (t+1) ω
  · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,mul_zero,le_refl]
  · simp only [ne_eq,decide_eq_true_eq,Ne.symm he,he,↓reduceIte]
    change (∑ i, held d t ω i)+(∑ i, held d (t+1) ω i) ≤ _
    linarith [total_held_reference d hδ hδ' t ω,total_held_reference d hδ hδ' (t+1) ω]

end UniformKServer.StarBudget

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

def integral (d : Data Ω ι k) (H : ℕ) (f : ℕ → Ω → ℝ) : ℝ :=
  ∑ t ∈ range H, average d.weight (f t)

theorem integral_nonneg (d : Data Ω ι k) (H : ℕ) {f : ℕ → Ω → ℝ}
    (h : ∀ t ω, 0 ≤ f t ω) : 0 ≤ integral d H f :=
  sum_nonneg fun t _ => sum_nonneg fun ω _ => mul_nonneg (d.positive ω).le (h t ω)

def countMove (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := ∑ i, |(d.count (t+1) ω i:ℝ)-d.count t ω i|
def cost (d : Data Ω ι k) (H : ℕ) : ℝ := integral d H (countMove d)
def energy (d : Data Ω ι k) (H : ℕ) : ℝ := cost d H+allowance ι k

theorem cost_nonneg (d : Data Ω ι k) (H : ℕ) : 0 ≤ cost d H :=
  integral_nonneg d H fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem energy_nonneg (d : Data Ω ι k) (H : ℕ) : 0 ≤ energy d H :=
  add_nonneg (cost_nonneg d H) (allowance_bounds ι k).1

theorem cost_le_energy (d : Data Ω ι k) (H : ℕ) : cost d H ≤ energy d H :=
  le_add_of_nonneg_right (allowance_bounds ι k).1

theorem allowance_le_energy (d : Data Ω ι k) (H : ℕ) : allowance ι k ≤ energy d H :=
  le_add_of_nonneg_left (cost_nonneg d H)

end UniformKServer.StarEnergy

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
open StarActualJumps
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem slope_bound (k : ℕ) : sideSlope k ≤ (10:ℝ)^18*EpochAlpha.ell k := by
  have h := EpochAlpha.ell_one k
  norm_num [sideSlope,StarConstants.cw]
  linarith

end UniformKServer.StarIntegratedJumps

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
open Finset TreeRounding TreeRankData RankTracking
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def integral (d : Data Ω S k) (H : ℕ) (f : ℕ → Ω → ℝ) : ℝ :=
  ∑ t ∈ range H, average d.weight (f t)

theorem integral_nonneg (d : Data Ω S k) (H : ℕ) {f : ℕ → Ω → ℝ} (h : ∀ t ω, 0 ≤ f t ω) :
    0 ≤ integral d H f := StarEnergy.integral_nonneg (TreeRankData.single d 0) H h

def hiddenMove (d : Data Ω S k) (H : ℕ) (v : Vertex n) : ℝ :=
  integral d H (fun t ω => |(d.count (t+1) ω v:ℝ)-d.count t ω v|)

def hiddenCost (d : Data Ω S k) (H : ℕ) (w : Vertex n → ℝ) : ℝ :=
  ∑ v, if v=0 then 0 else w (S.parent v)*hiddenMove d H v

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

omit [Fintype X] [MetricSpace X] in
theorem radius_step (A : ActualPartitions.Config X) (d : ℕ) :
    22*radius A (d+1) ≤ radius A d := by
  have hq : 22*A.q≤1 := by linarith [A.shiftH,A.P.gammaH_small]
  have h := mul_le_mul_of_nonneg_left hq (radius_nonneg A d)
  dsimp only [radius] at h ⊢
  rw [pow_succ]
  nlinarith only [h]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HiddenTesting
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Conditional tests of the true labeled pre-request positions. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw PilotEdits
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

theorem counts_test (D : Data X Ω k) (t : ℕ) (ω : Ω) (b : X→ℝ) :
    (∑ p,counts D t ω p*b p)=∑ a : Fin k,b (D.position t ω a) := by
  simp only [counts,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [atom,ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ,ite_true, if_true]

theorem filtered_test (D : Data X Ω k) (t : ℕ) (b : Ω→X→ℝ)
    (hb : ∀ ω v,(D.filtration (t+1)).r ω v→b ω=b v) :
    average D.weight (fun ω=>∑ p,filtered D t ω p*b ω p)=
      average D.weight (fun ω=>∑ a : Fin k,b ω (D.position t ω a)) := by
  have hp (p : X) : (∑ ω,D.weight ω*(filtered D t ω p*b ω p))=
      ∑ ω,D.weight ω*(counts D t ω p*b ω p) := by
    have h := test_identity (fun v=>(D.positive v).le) (D.filtration (t+1))
      (fun ω=>b ω p) (fun ω=>counts D t ω p) (fun ω v hv=>congrFun (hb ω v hv) p)
    unfold filtered
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply sum_congr rfl <;> intro ω _ <;> ring)
  unfold average
  simp_rw [←counts_test D t]
  simp only [mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl (fun p _=>hp p)

end UniformKServer.HiddenFlow

end


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

theorem diff_indicator {B : Type*} (a b : B) : PrefixMovement.diff a b=FirstStructure.indicator b a := by
  unfold PrefixMovement.diff FirstStructure.indicator
  simp only [eq_comm]

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

local instance ixCB_rfac53c_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairCB_rfac53c_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
def separationRate (A : ActualPartitions.Config X) : ℝ :=
  8+(16*A.C+33)*(1+1/Real.log (1+A.P.deltaH))

omit [Fintype X] [MetricSpace X] in
theorem separationRate_nonneg (A : ActualPartitions.Config X) : 0 ≤ separationRate A := by
  have hδ : 0<Real.log (1+A.P.deltaH) := Real.log_pos (by linarith [A.P.deltaH_pos])
  have hC : 0≤16*A.C+33 := by linarith [A.C_one]
  unfold separationRate
  positivity

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

local instance ixAB_rfac53c_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAB_rfac53c_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem expect_average {Z : Type*} [Fintype Z] (P : Law Z) (w : Ω→ℝ) (f : Z→Ω→ℝ) :
    P.expect (fun z=>average w (f z))=average w (fun ω=>P.expect (fun z=>f z ω)) := by
  unfold Law.expect average
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro z _
  ring

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HiddenRegion
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Posterior counting mass of any genuinely causal finite region. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype Ω] {k : ℕ}

def regionCount (D : Data X Ω k) (R : ℕ→Ω→Finset X) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k,if D.position t ω a∈R t ω then 1 else 0

theorem regionCount_range (D : Data X Ω k) (R : ℕ→Ω→Finset X) (t : ℕ) (ω : Ω) :
    regionCount D R t ω∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact sum_nonneg (fun a _=>by split_ifs <;> norm_num)
  · calc
      _≤∑ a : Fin k,(1:ℝ) := sum_le_sum (fun a _=>by split_ifs <;> norm_num)
      _=_ := by simp

theorem regionCount_eq (D : Data X Ω k) (t : ℕ) (ω : Ω) (R : Finset X) :
    (∑ p∈R,counts D t ω p)=∑ a : Fin k,if D.position t ω a∈R then (1:ℝ) else 0 := by
  unfold counts
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [atom]

theorem region_posterior (D : Data X Ω k) (R : ℕ→Ω→Finset X)
    (hR : ∀ t ω v,(D.filtration t).r ω v→R t ω=R t v) (t : ℕ) (ω : Ω) :
    posterior D.weight (D.filtration t) (regionCount D R t) ω=
      ∑ p∈R t ω,current D t ω p := by
  unfold posterior
  have he (v : Ω) : kernel D.weight (D.filtration t) ω v*regionCount D R t v=
      kernel D.weight (D.filtration t) ω v*∑ p∈R t ω,counts D t v p := by
    by_cases hv : (D.filtration t).r ω v
    · rw [regionCount_eq, hR t ω v hv]
      rfl
    · simp only [kernel,ite_eq_right hv,zero_mul]
  simp_rw [he,mul_sum]
  rw [sum_comm]
  rfl

end UniformKServer.HiddenFlow

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

theorem weighted_integral {I L : Type*} [Fintype I] [Fintype L] (r : I→ℝ)
    (w : Ω→ℝ) (H : ℕ) (f : I→L→ℕ→Ω→ℝ) :
    (∑ i,r i*∑ l,∑ t∈range H,average w (f i l t))=
      ∑ t∈range H,average w (fun ω=>∑ i,r i*∑ l,f i l t ω) := by
  simp only [average,mul_sum]
  rw [sum_comm]
  conv_lhs => arg 2; ext l; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_comm]
  conv_lhs => arg 2; ext i; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro l _
  ring

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyKeyGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Heavy precedence, disjoint nearby anchors, and the actual inner ball. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

theorem key_heavy_iff (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p : X) (l : HeavySlot X) :
    D.key is z t p=Sum.inl l ↔ HeavyRecords.covers (D.heavyState z.1 t) l p := by
  rw [←HeavyRecords.key_some _ D.positive.le p l]
  cases hh : HeavyRecords.key (D.heavyState z.1 t) p with
  | some a => simp only [key,heavyKey,hh,Option.map_some,Option.some_or,Option.getD_some,Sum.inl.injEq,Option.some.injEq]
  | none =>
    simp only [key,heavyKey,hh,Option.map_none,Option.none_or]
    cases ht : FirstStructure.first is (fun i=>D.tierKey z t i p) with
    | none => simp
    | some b =>
      obtain ⟨i,hi,hb⟩ := first_witness is _ b ht
      obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hb
      simp

theorem inner_heavy (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (y p : X) (l : HeavySlot X)
    (hl : l∈(D.heavyState z.1 t).present)
    (hy : dist y ((D.heavyState z.1 t).center l)≤7*D.r) (hp : dist y p≤D.r) :
    D.key is z t p=Sum.inl l := by
  apply (key_heavy_iff D is z t p l).mpr
  refine ⟨hl,?_⟩
  have hr := ((D.heavyState z.1 t).radius_bounds l hl).1
  have ht := dist_triangle ((D.heavyState z.1 t).center l) y p
  rw [dist_comm _ y] at ht
  linarith [D.positive]

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkScale
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! The actual pointwise scale sum for parks, including points of zero posterior
 mass. Add one to each ball mass exactly as in the held-size denominator. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

def outer (μ : X→ℝ) (y : X) (R q : ℝ) (j : ℕ) : ℝ :=
  1+GeometricMass.mass μ y (67*GeometricMass.radius R q j)
def inner (μ : X→ℝ) (y : X) (R q : ℝ) (j : ℕ) : ℝ :=
  1+GeometricMass.mass μ y (GeometricMass.radius R q j)

def bad (μ : X→ℝ) (y : X) (R q : ℝ) (j : ℕ) : Prop :=
  2*inner μ y R q j<outer μ y R q j

theorem outer_one (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X) (R q : ℝ) (j : ℕ) :
    1≤outer μ y R q j := by
  unfold outer
  linarith [GeometricMass.mass_nonneg μ hμ y (67*GeometricMass.radius R q j)]

theorem inner_one (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X) (R q : ℝ) (j : ℕ) :
    1≤ inner μ y R q j := by
  unfold inner
  linarith [GeometricMass.mass_nonneg μ hμ y (GeometricMass.radius R q j)]

end UniformKServer.ParkCoefficients

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

theorem ball_mass (μ : X→ℝ) (y : X) (r : ℝ) :
    ParkCapacity.mass μ (ParkCapacity.ball y r)=GeometricMass.mass μ y r := by
  simp only [ParkCapacity.mass,ParkCapacity.ball,sum_filter,GeometricMass.mass]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelParkCapacity
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! A cumulative level sum retains the shared tree subtree capacity. Zero
parks require no fictitious nonempty region. -/
noncomputable section
namespace UniformKServer.ParkCapacity
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [Fintype X] [MetricSpace X]

theorem level_cumulative (a : Allocation S k) (G : Geometry S X) (μ : X→ℝ)
    (hμ : ∀ x,0≤μ x) (C : ℝ) (hC : 0≤C)
    (hdom : ∀ v,a.amount v≤C*mass μ (G.region v)) (V : ℕ→Finset (Vertex n))
    (J j : ℕ) (y : X)
    (hdepth : ∀ i<J,∀ v∈V i,depth S v=i+1)
    (hw : ∀ i<J,∀ v∈V i,0<park S a.amount v→
      ∃ x∈G.region v,dist y x≤27*G.radius (i+1)) :
    ParkCoefficients.tail (fun i=>∑ v∈V i,park S a.amount v) J j≤
      C*mass μ (ball y (67*G.radius (j+1))) := by
  let U : ℕ→Finset (Vertex n) := fun i=>(V i).filter (fun v=>0<park S a.amount v)
  have hdp : (Ico j J : Set ℕ).PairwiseDisjoint U := by
    intro i hi l hl hne
    apply Finset.disjoint_left.mpr
    intro v hv hu
    have hd1 := hdepth i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1
    have hd2 := hdepth l (mem_Ico.mp hl).2 v (mem_filter.mp hu).1
    omega
  have he : ParkCoefficients.tail (fun i=>∑ v∈V i,park S a.amount v) J j=
      ∑ v∈(Ico j J).biUnion U,park S a.amount v := by
    rw [sum_biUnion hdp]
    exact sum_congr rfl (fun i _=>(positive_sum a (V i)).symm)
  rw [he]
  apply cumulative a G μ hμ C hC hdom
  · intro v hv
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
    rw [hdepth i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1]
    exact Nat.add_le_add_right (mem_Ico.mp hi).1 1
  · intro v hv
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
    obtain ⟨x,hx,hd⟩ := hw i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    refine ⟨x,hx,?_⟩
    rw [hdepth i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1]
    exact hd

end UniformKServer.ParkCapacity

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CurrentTesting
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! All-time adapted testing of the literal hidden member positions. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw PilotEdits
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

theorem current_test (D : Data X Ω k) (t : ℕ) (b : Ω→X→ℝ)
    (hb : ∀ ω v,(D.filtration t).r ω v→b ω=b v) :
    average D.weight (fun ω=>∑ p,current D t ω p*b ω p)=
      average D.weight (fun ω=>∑ a : Fin k,b ω (D.position t ω a)) := by
  have hp (p : X) : (∑ ω,D.weight ω*(current D t ω p*b ω p))=
      ∑ ω,D.weight ω*(counts D t ω p*b ω p) := by
    have h := test_identity (fun v=>(D.positive v).le) (D.filtration t)
      (fun ω=>b ω p) (fun ω=>counts D t ω p) (fun ω v hv=>congrFun (hb ω v hv) p)
    unfold current
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply sum_congr rfl <;> intro ω _ <;> ring)
  unfold average
  simp_rw [←counts_test D t]
  simp only [mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl (fun p _=>hp p)

omit [Fintype X] in
theorem member_distance (D : Data X Ω k) [MetricSpace X] (t : ℕ) (ω : Ω) :
    (∑ a : Fin k,dist (D.position t ω a) (D.position (t+1) ω a))=
      dist (D.position t ω (D.chosen t ω)) (D.request t ω) := by
  calc
    _=dist (D.position t ω (D.chosen t ω)) (D.position (t+1) ω (D.chosen t ω)) := by
      apply sum_eq_single (D.chosen t ω)
      · intro a _ ha
        rw [D.update,ite_eq_right ha,dist_self]
      · intro ha
        exact (ha (mem_univ _)).elim
    _=_ := by rw [D.update,ite_eq_left rfl]

end UniformKServer.HiddenFlow

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyAnchorGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Literal moving-label geometry and potential release for one heavy update. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem geom_mass (μ : X→ℝ) (x : X) (R : ℝ) :
    AnchorRamp.mass μ (AnchorRamp.ball x R)=GeometricMass.mass μ x R := by
  simp only [AnchorRamp.mass,AnchorRamp.ball,sum_filter,GeometricMass.mass]

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelAnchorContinuity
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Cross-time witnesses for a literal fixed-alphabet key. Tier labels cannot
be reassigned on consecutive supported maps; only retained heavy labels move. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance ixAC_rfac53c_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAC_rfac53c_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem key_tier_witness (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p : X) (i : Fin H) (l : TierLabeledKeys.Slot X (D.K i))
    (hl : D.key is z t p=Sum.inr (Sum.inl ⟨i,l⟩)) :
    TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (z.2 i).1 (z.2 i).2 p=some l := by
  cases hh : D.heavyKey z t p with
  | some a =>
    obtain ⟨h,_,rfl⟩ := Option.map_eq_some_iff.mp hh
    simp only [key,hh,Option.some_or,Option.getD_some] at hl
    cases hl
  | none =>
    cases ht : FirstStructure.first is (fun j=>D.tierKey z t j p) with
    | none => simp [key,hh,ht] at hl
    | some a =>
      have ha : a=Sum.inr (Sum.inl ⟨i,l⟩) := by simpa only [key,hh,Option.none_or,ht,Option.getD_some] using hl
      obtain ⟨j,_,hj⟩ := first_witness is _ a ht
      obtain ⟨m,hm,he⟩ := Option.map_eq_some_iff.mp hj
      have he' : (Sigma.mk j m : (j : Fin H) × TierLabeledKeys.Slot X (D.K j))=⟨i,l⟩ :=
        Sum.inl.inj (Sum.inr.inj (he.trans ha))
      cases he'
      exact hm

end UniformKServer.LevelMap.Data

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

theorem realized_leaf_occupied {n : ℕ} {S : Shape n} (a : Allocation S k)
    (s : State S k) (hs : Rounded a s.value) (v : Vertex n) (hv : TreeLeaves.leaf (S:=S) v)
    (ha : 1≤a.amount v) : ∃ i,s.realization.tuple i=v := by
  have hsum : (∑ i : Children S v,s.value i.val)=0 := sum_eq_zero (fun i _=>(hv i).elim)
  have hx : 1 ≤ s.value v := by
    have hb := (balanced_bounds (hs.2.1 v)).1
    have hf : (1:ℤ)≤⌊a.amount v⌋ := Int.le_floor.mpr (by exact_mod_cast ha)
    omega
  have hp : 0 < intPark S s.value v := by rw [intPark,hsum]; omega
  have he := s.realization.sum (fun w=>if w=v then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true, if_true] at he
  by_contra hn
  have he' : (∑ i : Fin k,if s.realization.tuple i=v then (1:ℝ) else 0)=0 :=
    sum_eq_zero (fun i _=>ite_eq_right (fun hi=>hn ⟨i,hi⟩))
  rw [he'] at he
  have : (0:ℝ)<(intPark S s.value v:ℝ) := by exact_mod_cast hp
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Disintegration
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Exact finite disintegration, including all null fibers. -/
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem Law.ext {P Q : Law Ω} (h : P.weight=Q.weight) : P=Q := by
  cases P; cases Q; cases h; rfl

theorem Law.ext_expect {P Q : Law Ω} (h : ∀ f : Ω→ℝ,P.expect f=Q.expect f) : P=Q := by
  apply Law.ext
  funext x
  have := h (fun y=>if y=x then 1 else 0)
  simpa [Law.expect] using this

theorem Law.weighted_conditional (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (y : Γ) (g : Ω→ℝ) :
    (P.map f).weight y*(P.conditional f fallback y).expect g=
      ∑ x,if f x=y then P.weight x*g x else 0 := by
  by_cases hy : 0<(P.map f).weight y
  · simp only [Law.conditional,dite_eq_left hy,Law.expect,mul_sum]
    apply sum_congr rfl
    intro x _
    split_ifs
    · field_simp
    · simp
  · have hz := le_antisymm (not_lt.mp hy) ((P.map f).nonneg y)
    rw [hz,zero_mul]
    symm
    apply sum_eq_zero
    intro x _
    split_ifs with he
    · have hh : P.weight x≤(P.map f).weight y := by
        change _≤∑ z,if f z=y then P.weight z else 0
        have := single_le_sum (s:=(univ : Finset Ω))
          (f:=fun z=>if f z=y then P.weight z else 0)
          (fun z _=>by split; exact P.nonneg z; exact le_rfl) (mem_univ x)
        simpa only [ite_eq_left he] using this
      have hx := le_antisymm (hh.trans hz.le) (P.nonneg x)
      rw [hx,zero_mul]
    · rfl

theorem Law.disintegrate (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (g : Γ→Ω→ℝ) :
    (P.map f).expect (fun y=>(P.conditional f fallback y).expect (g y))=
      P.expect (fun x=>g (f x) x) := by
  unfold Law.expect
  have hr (y : Γ) := P.weighted_conditional f fallback y (g y)
  change ∑ y,(P.map f).weight y*(P.conditional f fallback y).expect (g y)=_
  simp_rw [hr]
  rw [sum_comm]
  simp

theorem Law.conditional_positive (P : Law Ω) (f : Ω→Γ) (fallback : Law Ω) (y : Γ)
    (hy : 0<(P.map f).weight y) (x : Ω) (hx : 0<(P.conditional f fallback y).weight x) :
    f x=y ∧ 0<P.weight x := by
  simp only [Law.conditional,dite_eq_left hy] at hx
  split_ifs at hx with he
  · exact ⟨he,(div_pos_iff.mp hx).resolve_right (fun h=>not_lt_of_ge hy.le h.2) |>.1⟩
  · simp at hx

theorem Law.weight_le_map (P : Law Ω) (f : Ω→Γ) (x : Ω) :
    P.weight x ≤ (P.map f).weight (f x) := by
  have h := single_le_sum (s:=(univ : Finset Ω))
    (f:=fun y=>if f y=f x then P.weight y else 0)
    (fun y _=>by split; exact P.nonneg y; exact le_rfl) (mem_univ x)
  simpa [Law.map] using h

end UniformKServer.FiniteProbability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LawSupport
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Expectations only charge positive support. -/
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem Law.expect_mono_support (P : Law Ω) (f g : Ω→ℝ)
    (h : ∀ x,0<P.weight x → f x≤g x) : P.expect f≤P.expect g := by
  apply sum_le_sum
  intro x _
  by_cases hx : 0<P.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) hx.le
  · have hz := le_antisymm (not_lt.mp hx) (P.nonneg x)
    rw [hz,zero_mul,zero_mul]

theorem Law.map_comp (P : Law Ω) (f : Ω→Γ) {Δ : Type*} [Fintype Δ] (g : Γ→Δ) :
    (P.map f).map g=P.map (g ∘ f) := by
  apply Law.ext_expect
  intro h
  simp only [Law.expect_map,Function.comp_assoc]

theorem Law.map_id (P : Law Ω) : P.map id=P := by
  apply Law.ext_expect
  intro h
  simp only [Law.expect_map,Function.comp_id]

theorem Law.expect_univ (P : Law Ω) (f : Γ→Ω→ℝ) :
    P.expect (fun ω=>∑ i,f i ω)=∑ i,P.expect (f i) := by
  simp only [Law.expect,mul_sum]
  rw [sum_comm]

end UniformKServer.FiniteProbability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LazyFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A literal labeled strongly-lazy simulation. Fixed-label mismatch suffices
for the movement telescope; no forbidden move or future request is used. -/
namespace UniformKServer.LazyFinance
open Finset
open scoped Classical
variable {X : Type*} [PseudoMetricSpace X] {k : ℕ}

omit [PseudoMetricSpace X] in
theorem lazy (hk : 0 < k) (a v : Fin k→X) (r : X) (h : ∃ i,a i=r) :
    a (choice hk a v r)=r := by
  rw [choice,dite_eq_left h]
  exact h.choose_spec

theorem step (hk : 0 < k) (a u v : Fin k→X) (r : X) (hv : ∃ i,v i=r) :
    dist (a (choice hk a v r)) r+mismatch (Function.update a (choice hk a v r) r) v ≤
      mismatch a u+mismatch u v := by
  by_cases ha : ∃ i,a i=r
  · have he := lazy hk a v r ha
    have hz : dist (a (choice hk a v r)) r=0 := by rw [he,dist_self]
    have hu : Function.update a (choice hk a v r) r=a := by
      conv_lhs => arg 3; rw [←he]
      exact Function.update_eq_self _ _
    rw [hz,zero_add,hu]
    exact mismatch_triangle a u v
  · have he : v (choice hk a v r)=r := by rw [choice,dite_eq_right ha,dite_eq_left hv]; exact hv.choose_spec
    rw [at_request a v r _ he]
    exact mismatch_triangle a u v

end UniformKServer.LazyFinance

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_MarkovFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Eliminate a finite private state by its exact configuration/action flows.
No private state or future observation is exposed in the resulting rows. -/
namespace UniformKServer.MarkovFlow
open Finset FiniteProbability
open scoped Classical
variable {R C J V : Type*} [Fintype C] [Fintype V]

structure Model (R C J V : Type*) [Fintype V] where
  kernel : List R→R→V×C→Law V
  choice : List R→R→V×C→V→J
  transition : C→R→J→C

namespace Model
variable (M : Model R C J V)

def successor (w : List R) (r : R) (q : (V×C)×V) : V×C :=
  (q.2,M.transition q.1.2 r (M.choice w r q.1 q.2))

def joint (P : Law (V×C)) (w : List R) (r : R) : Law ((V×C)×V) :=
  P.bind (fun s=>(M.kernel w r s).map (fun v=>(s,v)))

def advance (P : Law (V×C)) (w : List R) (r : R) : Law (V×C) :=
  (M.joint P w r).map (M.successor w r)

def evolve : List R→Law (V×C)→List R→Law (V×C)
  | _,P,[] => P
  | w,P,r::rs => evolve (w++[r]) (M.advance P w r) rs

def process (P : Law (V×C)) (w : List R) : Law (V×C) := M.evolve [] P w

theorem evolve_append (w u v : List R) (P : Law (V×C)) :
    M.evolve w P (u++v)=M.evolve (w++u) (M.evolve w P u) v := by
  induction u generalizing w P with
  | nil => simp [evolve]
  | cons r rs ih =>
    simpa only [evolve,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      (ih (w++[r]) (M.advance P w r))

theorem process_snoc (P : Law (V×C)) (w : List R) (r : R) :
    M.process P (w++[r])=M.advance (M.process P w) w r := by
  rw [process,M.evolve_append]
  rfl

theorem joint_first (P : Law (V×C)) (w : List R) (r : R) (f : V×C→ℝ) :
    (M.joint P w r).expect (f ∘ Prod.fst)=P.expect f := by
  simp only [joint,Law.expect_bind,Law.expect_map,Function.comp_def]
  simp only [Law.expect_const]

theorem advance_expect (P : Law (V×C)) (w : List R) (r : R) (f : V×C→ℝ) :
    (M.advance P w r).expect f=(M.joint P w r).expect (f ∘ M.successor w r) :=
  Law.expect_map _ _ _

variable [Fintype J]

def actions (P : Law (V×C)) (w : List R) (r : R) : Law (C×J) :=
  (M.joint P w r).map (fun q=>(q.1.2,M.choice w r q.1 q.2))

def flow (P : Law (V×C)) : RealFlow.Data R C J where
  mass w c := ((M.process P w).map Prod.snd).weight c
  flow w r c j := (M.actions (M.process P w) w r).weight (c,j)

theorem sum_row (P : Law (V×C)) (w : List R) (r : R) (c : C) :
    ∑ j,(M.actions P w r).weight (c,j)=(P.map Prod.snd).weight c := by
  have h₁ : (∑ j,(M.actions P w r).weight (c,j))=
      (M.actions P w r).expect (fun cj=>if cj.1=c then 1 else 0) := by
    simp only [Law.expect,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
    rw [sum_comm]
    simp only [sum_ite_eq',mem_univ,ite_true, if_true]
  rw [h₁,actions,Law.expect_map]
  change (M.joint P w r).expect ((fun s : V×C=>if s.2=c then 1 else 0) ∘ Prod.fst)=_
  rw [M.joint_first]
  simp only [Law.expect,Law.map,mul_ite,mul_one,mul_zero]

theorem action_cost (P : Law (V×C)) (w : List R) (r : R) (d : C→J→ℝ) :
    (∑ c,∑ j,(M.actions P w r).weight (c,j)*d c j)=
      (M.joint P w r).expect (fun q=>d q.1.2 (M.choice w r q.1 q.2)) := by
  have h := (M.joint P w r).expect_map (fun q=>(q.1.2,M.choice w r q.1 q.2)) (fun cj=>d cj.1 cj.2)
  simpa only [Law.expect,Fintype.sum_prod_type,actions,Function.comp_def] using h

theorem sum_inflow (P : Law (V×C)) (w : List R) (r : R) (c' : C) :
    (∑ c,∑ j,if M.transition c r j=c' then (M.actions P w r).weight (c,j) else 0)=
      ((M.advance P w r).map Prod.snd).weight c' := by
  have ha := M.action_cost P w r (fun c j=>if M.transition c r j=c' then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at ha
  rw [ha]
  have hn := (M.advance P w r).expect_map Prod.snd (fun c=>if c=c' then 1 else 0)
  have he := M.advance_expect P w r (fun s=>if s.2=c' then 1 else 0)
  have hz : ((M.advance P w r).map Prod.snd).expect (fun c=>if c=c' then 1 else 0)=
      ((M.advance P w r).map Prod.snd).weight c' := by simp [Law.expect]
  rw [hz] at hn
  exact (he.symm.trans hn.symm)

theorem action_support (P : Law (V×C)) (w : List R) (r : R)
    (allowed : C→R→J→Prop) (hc : ∀ s v,allowed s.2 r (M.choice w r s v))
    (c : C) (j : J) (hj : ¬allowed c r j) : (M.actions P w r).weight (c,j)=0 := by
  unfold actions Law.map
  apply sum_eq_zero
  intro q _
  split_ifs with he
  · have h₁ : q.1.2=c := congrArg Prod.fst he
    have h₂ : M.choice w r q.1 q.2=j := congrArg Prod.snd he
    have hh := hc q.1 q.2
    rw [h₁,h₂] at hh
    exact (hj hh).elim
  · rfl

theorem valid (P : Law (V×C)) (c₀ : C) (H : ℕ) (allowed : C→R→J→Prop)
    (hinit : P.map Prod.snd=Law.pure c₀)
    (hc : ∀ w r s v,allowed s.2 r (M.choice w r s v)) :
    RealFlow.Valid (M.flow P) M.transition allowed c₀ H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w _ c; exact ((M.process P w).map Prod.snd).nonneg c
  · intro w _; exact ((M.process P w).map Prod.snd).total
  · intro c
    change (P.map Prod.snd).weight c=_
    rw [hinit]
    rfl
  · intro w _ r c j; exact (M.actions (M.process P w) w r).nonneg (c,j)
  · intro w _ r c j hj; exact M.action_support _ _ _ allowed (hc w r) c j hj
  · intro w _ r c; exact M.sum_row _ _ _ c
  · intro w _ r c'
    change _=((M.process P (w++[r])).map Prod.snd).weight c'
    rw [M.process_snoc]
    exact M.sum_inflow _ _ _ c'

end Model
end UniformKServer.MarkovFlow

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LazyMarkov
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Strongly-lazy metric serving from finite private virtual states. The exact
old and new marginals, legal actions, and potential charge are all explicit. -/
namespace UniformKServer.LazyMarkov
open Finset FiniteProbability
open scoped Classical
variable {X V : Type*} [Fintype X] [MetricSpace X] [Fintype V] {k : ℕ}

structure Input (X V : Type*) [Fintype V] (k : ℕ) where
  kernel : List X→X→V→Law V
  location : List X→V→Fin k→X

namespace Input
variable (D : Input X V k) (hk : 0<k)

def model : MarkovFlow.Model X (Fin k→X) (Fin k) V where
  kernel w r s := D.kernel w r s.1
  choice w r s v := LazyFinance.choice hk s.2 (D.location (w++[r]) v) r
  transition c r j := Function.update c j r

def potential (w : List X) (s : V×(Fin k→X)) : ℝ :=
  LazyFinance.mismatch s.2 (D.location w s.1)

def transport (P : Law V) (w : List X) (r : X) : ℝ :=
  P.expect (fun v=>(D.kernel w r v).expect (fun v'=>
    LazyFinance.mismatch (D.location w v) (D.location (w++[r]) v')))

def charge (Q : Law (V×(Fin k→X))) (w : List X) (r : X) : ℝ :=
  ∑ c,∑ j,((D.model hk).actions Q w r).weight (c,j)*dist (c j) r

omit [MetricSpace X] in
theorem marginal_next (Q : Law (V×(Fin k→X))) (w : List X) (r : X) :
    ((D.model hk).advance Q w r).map Prod.fst=(Q.map Prod.fst).bind (D.kernel w r) := by
  apply Law.ext_expect
  intro f
  simp only [MarkovFlow.Model.advance,MarkovFlow.Model.joint,Law.expect_map,Law.expect_bind,
    MarkovFlow.Model.successor,model,Function.comp_def]

omit [Fintype X] [MetricSpace X] in
theorem legal (w : List X) (r : X) (s : V×(Fin k→X)) (v : V)
    (h : ∃ i,s.2 i=r) : s.2 ((D.model hk).choice w r s v)=r :=
  LazyFinance.lazy hk _ _ _ h

theorem step (Q : Law (V×(Fin k→X))) (w : List X) (r : X)
    (hcover : ∀ v v',0<(Q.map Prod.fst).weight v → 0<(D.kernel w r v).weight v' →
      ∃ i,D.location (w++[r]) v' i=r) :
    D.charge hk Q w r+((D.model hk).advance Q w r).expect (D.potential (w++[r])) ≤
      Q.expect (D.potential w)+D.transport (Q.map Prod.fst) w r := by
  have hs (s : V×(Fin k→X)) (hpos : 0<Q.weight s) :
      (D.kernel w r s.1).expect (fun v=>
        dist (s.2 (LazyFinance.choice hk s.2 (D.location (w++[r]) v) r)) r+
          LazyFinance.mismatch (Function.update s.2 (LazyFinance.choice hk s.2 (D.location (w++[r]) v) r) r)
            (D.location (w++[r]) v)) ≤
      D.potential w s+(D.kernel w r s.1).expect (fun v=>
        LazyFinance.mismatch (D.location w s.1) (D.location (w++[r]) v)) := by
    have hp : 0<(Q.map Prod.fst).weight s.1 := lt_of_lt_of_le hpos (Q.weight_le_map Prod.fst s)
    have hb := (D.kernel w r s.1).expect_mono_support _ _ (fun v hv=>
      LazyFinance.step hk s.2 (D.location w s.1) (D.location (w++[r]) v) r (hcover s.1 v hp hv))
    simpa only [Law.expect_add,Law.expect_const,potential] using hb
  have hh := Q.expect_mono_support _ _ hs
  rw [Law.expect_add] at hh
  have he : Q.expect (fun s=>(D.kernel w r s.1).expect (fun v=>
      LazyFinance.mismatch (D.location w s.1) (D.location (w++[r]) v)))=
      D.transport (Q.map Prod.fst) w r := by
    rw [transport,Law.expect_map]
    rfl
  rw [he] at hh
  have hc := (D.model hk).action_cost Q w r (fun c j=>dist (c j) r)
  change D.charge hk Q w r=_ at hc
  rw [hc,MarkovFlow.Model.advance,Law.expect_map,←Law.expect_add]
  simpa only [MarkovFlow.Model.joint,Law.expect_bind,Law.expect_map,
    MarkovFlow.Model.successor,model,Function.comp_def,potential] using hh

omit [MetricSpace X] in
theorem initial_marginal (P : Law V) (s : Fin k→X) :
    (P.map (fun v=>(v,s))).map Prod.snd=Law.pure s := by
  apply Law.ext_expect
  intro f
  simp only [Law.expect_map,Function.comp_def,Law.expect_const,Law.expect_pure]

theorem initial_potential (P : Law V) (s : Fin k→X) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ) :
    (P.map (fun v=>(v,s))).expect (D.potential [])≤k*Δ := by
  rw [Law.expect_map]
  exact (P.expect_mono _ _ (fun v=>LazyFinance.initial_bound s _ Δ hdiam)).trans_eq (P.expect_const _)

end Input
end UniformKServer.LazyMarkov

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

omit [Fintype X] in
theorem pick_trace (t : ℕ) (ω : Ω) : O.trace t (O.pick (O.trace t ω))=O.trace t ω := by
  have he : ∃ v,O.trace (O.trace t ω).length v=O.trace t ω := ⟨ω,by rw [O.trace_length]⟩
  unfold pick
  rw [dite_eq_left he]
  simpa only [O.trace_length] using he.choose_spec

omit [Fintype X] in
theorem pick_related (t : ℕ) (ω : Ω) : (D.filtration t).r (O.pick (O.trace t ω)) ω :=
  O.reflects t _ _ (O.pick_trace t ω)

end PublicInput
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RealFlowMixture
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Independent finite random seeds are eliminated by linear flow mixtures,
not by revealing them to the request law. -/
namespace UniformKServer.RealFlow
open Finset FiniteProbability
open scoped Classical
variable {R C J Z : Type*} [Fintype C] [Fintype J] [Fintype Z]

def mixture (P : Law Z) (F : Z→Data R C J) : Data R C J where
  mass w c := P.expect (fun z=>(F z).mass w c)
  flow w r c j := P.expect (fun z=>(F z).flow w r c j)

theorem mixture_valid (P : Law Z) (F : Z→Data R C J) (T : C→R→J→C)
    (allowed : C→R→J→Prop) (s : C) (H : ℕ)
    (hv : ∀ z,Valid (F z) T allowed s H) : Valid (mixture P F) T allowed s H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw c
    exact P.expect_nonneg _ (fun z=>(hv z).mass_nonneg w hw c)
  · intro w hw
    change (∑ c,P.expect (fun z=>(F z).mass w c))=1
    rw [←Law.expect_univ]
    simp only [(hv _).mass_total w hw,Law.expect_const]
  · intro c
    change P.expect (fun z=>(F z).mass [] c)=_
    simp only [(hv _).initial,Law.expect_const]
  · intro w hw r c j
    exact P.expect_nonneg _ (fun z=>(hv z).flow_nonneg w hw r c j)
  · intro w hw r c j hj
    change P.expect (fun z=>(F z).flow w r c j)=0
    simp only [(hv _).support w hw r c j hj,Law.expect_const]
  · intro w hw r c
    change (∑ j,P.expect (fun z=>(F z).flow w r c j))=P.expect _
    rw [←Law.expect_univ]
    exact congrArg P.expect (funext fun z=>(hv z).outflow w hw r c)
  · intro w hw r c'
    change (∑ c,∑ j,if T c r j=c' then P.expect (fun z=>(F z).flow w r c j) else 0)=P.expect _
    have he (c : C) (j : J) : (if T c r j=c' then P.expect (fun z=>(F z).flow w r c j) else 0)=
        P.expect (fun z=>if T c r j=c' then (F z).flow w r c j else 0) := by
      split_ifs <;> simp only [Law.expect_const]
    simp_rw [he]
    simp_rw [←Law.expect_univ]
    exact congrArg P.expect (funext fun z=>(hv z).inflow w hw r c')

theorem mixture_cost (P : Law Z) (F : Z→Data R C J) (d : C→R→J→ℝ) (w u : List R) :
    flowCost (mixture P F) d w u=P.expect (fun z=>flowCost (F z) d w u) := by
  induction u generalizing w with
  | nil => simp only [flowCost,Law.expect_const]
  | cons r rs ih =>
    rw [flowCost,ih]
    have hc : (∑ c,∑ j,(mixture P F).flow w r c j*d c r j)=
        P.expect (fun z=>∑ c,∑ j,(F z).flow w r c j*d c r j) := by
      have he (c : C) (j : J) : (mixture P F).flow w r c j*d c r j=
          P.expect (fun z=>(F z).flow w r c j*d c r j) := by
        simpa only [mixture,mul_comm] using (P.expect_mul (d c r j) (fun z=>(F z).flow w r c j)).symm
      simp_rw [he,←Law.expect_univ]
    rw [hc,←Law.expect_add]
    rfl

end UniformKServer.RealFlow

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
namespace UniformKServer.HiddenFlow.Data
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype Ω] {k : ℕ}

def transcript (D : Data X Ω k) (t : ℕ) (ω : Ω) : List X :=
  List.ofFn (fun i : Fin t=>D.request i.val ω)

theorem transcript_zero (D : Data X Ω k) (ω : Ω) : D.transcript 0 ω=[] := rfl

theorem transcript_snoc (D : Data X Ω k) (t : ℕ) (ω : Ω) :
    D.transcript (t+1) ω=D.transcript t ω++[D.request t ω] := by
  simp only [transcript,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]

theorem transcript_length (D : Data X Ω k) (t : ℕ) (ω : Ω) :
    (D.transcript t ω).length=t := by simp only [transcript,List.length_ofFn]

def Public (D : Data X Ω k) : Prop :=
  ∀ t ω v,D.transcript t ω=D.transcript t v → (D.filtration t).r ω v

end UniformKServer.HiddenFlow.Data

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

local instance ixAF_rfac53c_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAF_rfac53c_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
def allocationRate (A : ActualPartitions.Config X) (k : ℕ) : ℝ :=
  (8*(10:ℝ)^63/A.q)*(A.editBound+separationRate A)*EpochAlpha.ell k*(1+Real.log (k+1))
def anchorRate (A : ActualPartitions.Config X) (k : ℕ) : ℝ :=
  160*(((6/5)*132)*(1+288*KeySizeTracker.ell (k+1))*(A.editBound+separationRate A)*
    (1+Real.log (k+1))+driftLog k/3+(12/5)*(1+1/22)*allocationRate A k)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.FiniteFlow
variable {R C J : Type*} [Fintype C] [Fintype J] [DecidableEq C] [DecidableEq J]

variable (F : Data R C J) (T : C → R → J → C)
  (allowed : C → R → J → Prop) (initial : C) (H : ℕ)
  (fallback : C → R → J)
  (hF : Valid F T allowed initial H)

include hF

theorem mass_row (w : List R) (hw : w.length < H) (r : R) (c : C) (j : J) :
    F.mass w c * row F fallback H w r c j = F.flow w r c j := by
  by_cases hp : F.mass w c = 0
  · rw [hp, zero_mul, zero_flow F T allowed initial H hF w hw r c hp j]
  · rw [row, ite_eq_left ⟨hw, hp⟩]
    exact mul_div_cancel₀ _ hp

theorem row_sum (w : List R) (r : R) (c : C) :
    ∑ j, row F fallback H w r c j = 1 := by
  by_cases hh : w.length < H ∧ F.mass w c ≠ 0
  · simp only [row, ite_eq_left hh, ← Finset.sum_div, hF.outflow w hh.1 r c,
      div_self hh.2]
  · simp [row, hh]

theorem cost_average (d : C → R → J → ℚ) (rs w : List R)
    (hw : w.length + rs.length ≤ H) :
    (∑ c, F.mass w c * cost (row F fallback H) T d w c rs) = flowCost F d w rs := by
  induction rs generalizing w with
  | nil => simp [cost, flowCost]
  | cons r rs ih =>
    have hlen : w.length < H := by simp only [List.length_cons] at hw; omega
    have hnext : (w++[r]).length+rs.length ≤ H := by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    simp only [cost, Finset.mul_sum, ← mul_assoc]
    simp_rw [mass_row F T allowed initial H fallback hF w hlen r]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [inflow_average F T allowed initial H hF w hlen r (fun c => cost (row F fallback H) T d (w++[r]) c rs)]
    rw [ih (w++[r]) hnext]
    rfl



omit hF in
/-- The precise finite flow realization obligation. -/
theorem realization (F : Data R C J) (T : C → R → J → C)
    (allowed : C → R → J → Prop) (initial : C) (H : ℕ)
    (fallback : C → R → J) (hfallback : ∀ c r, allowed c r (fallback c r))
    (hF : Valid F T allowed initial H) :
    (∀ w r c j, 0 ≤ row F fallback H w r c j) ∧
    (∀ w r c, ∑ j, row F fallback H w r c j = 1) ∧
    (∀ w r c j, ¬allowed c r j → row F fallback H w r c j = 0) ∧
    (∀ d rs, rs.length ≤ H → cost (row F fallback H) T d [] initial rs = flowCost F d [] rs) := by
  refine ⟨row_nonneg F T allowed initial H fallback hF,
    row_sum F T allowed initial H fallback hF,
    row_support F T allowed initial H fallback hF hfallback, ?_⟩
  intro d rs hrs
  have hh := cost_average F T allowed initial H fallback hF d rs [] (by simpa using hrs)
  simpa only [hF.initial, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] using hh

end UniformKServer.FiniteFlow


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlowSpace
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A literal finite coordinate model of all horizon-H causal flows. Compactness
comes from their probability bounds, not from assuming a minimax input. -/
namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} {H : ℕ}

theorem decode_encode_mass (F : Data R C J) (w : List R) (hw : w.length≤H) (c : C) :
    (decode (H:=H) (encode F)).mass w c=F.mass w c := by
  simp only [decode,dite_eq_left hw,encode,letters_code]

theorem decode_encode_flow (F : Data R C J) (w : List R) (hw : w.length<H) (r : R) (c : C) (j : J) :
    (decode (H:=H) (encode F)).flow w r c j=F.flow w r c j := by
  simp only [decode,dite_eq_left hw,encode,letters_code,ite_eq_left hw]

section
variable [Fintype C] [Fintype J]

theorem decode_encode_valid (F : Data R C J) (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (hF : Valid F T allowed s H) : Valid (decode (H:=H) (encode F)) T allowed s H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw c; rw [decode_encode_mass F w hw]; exact hF.mass_nonneg w hw c
  · intro w hw; simp only [decode_encode_mass F w hw]; exact hF.mass_total w hw
  · intro c; rw [decode_encode_mass F [] (by simp)]; exact hF.initial c
  · intro w hw r c j; rw [decode_encode_flow F w hw]; exact hF.flow_nonneg w hw r c j
  · intro w hw r c j hj; rw [decode_encode_flow F w hw]; exact hF.support w hw r c j hj
  · intro w hw r c; simp only [decode_encode_flow F w hw,decode_encode_mass F w hw.le]; exact hF.outflow w hw r c
  · intro w hw r c'
    have hwr : (w++[r]).length≤H := by simp only [List.length_append,List.length_singleton]; omega
    simp only [decode_encode_flow F w hw,decode_encode_mass F (w++[r]) hwr]
    exact hF.inflow w hw r c'

end

theorem mass_continuous (w : List R) (c : C) :
    Continuous (fun x : Space R C J H=>(decode x).mass w c) := by
  by_cases hw : w.length≤H
  · simpa only [decode,dite_eq_left hw] using (continuous_apply (Sum.inl (code w hw,c) : Index R C J H) : Continuous (fun x : Space R C J H=>x (.inl (code w hw,c))))
  · simp only [decode,dite_eq_right hw]
    exact continuous_const

theorem flow_continuous (w : List R) (r : R) (c : C) (j : J) :
    Continuous (fun x : Space R C J H=>(decode x).flow w r c j) := by
  by_cases hw : w.length<H
  · simpa only [decode,dite_eq_left hw] using (continuous_apply (Sum.inr (code w hw.le,r,c,j) : Index R C J H) : Continuous (fun x : Space R C J H=>x (.inr (code w hw.le,r,c,j))))
  · simp only [decode,dite_eq_right hw]
    exact continuous_const

end UniformKServer.FiniteFlowSpace

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlowCompact
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} [Fintype C] [Fintype J] {H : ℕ}

theorem valid_closed (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) :
    IsClosed {x : Space R C J H | Valid (decode x) T allowed s H} := by
  have h₁ : IsClosed {x : Space R C J H | ∀w,w.length≤H → ∀c,0≤(decode x).mass w c} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun c=>
      isClosed_le continuous_const (mass_continuous w c)
  have h₂ : IsClosed {x : Space R C J H | ∀w,w.length≤H → ∑c,(decode x).mass w c=1} :=
    closed_forall _ fun w=>closed_forall _ fun _=>
      isClosed_eq (continuous_finsetSum _ fun c _=>mass_continuous w c) continuous_const
  have h₃ : IsClosed {x : Space R C J H | ∀c,(decode x).mass [] c=if c=s then 1 else 0} :=
    closed_forall _ fun c=>isClosed_eq (mass_continuous [] c) continuous_const
  have h₄ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c j,0≤(decode x).flow w r c j} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun r=>
      closed_forall _ fun c=>closed_forall _ fun j=>
        isClosed_le continuous_const (flow_continuous w r c j)
  have h₅ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c j,¬allowed c r j → (decode x).flow w r c j=0} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun r=>
      closed_forall _ fun c=>closed_forall _ fun j=>closed_forall _ fun _=>
        isClosed_eq (flow_continuous w r c j) continuous_const
  have h₆ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c,∑j,(decode x).flow w r c j=(decode x).mass w c} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun r=>
      closed_forall _ fun c=>
        isClosed_eq (continuous_finsetSum _ fun j _=>flow_continuous w r c j) (mass_continuous w c)
  have h₇ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c',
      (∑c,∑j,if T c r j=c' then (decode x).flow w r c j else 0)=(decode x).mass (w++[r]) c'} := by
    apply closed_forall _; intro w
    apply closed_forall _; intro hw
    apply closed_forall _; intro r
    apply closed_forall _; intro c'
    apply isClosed_eq _ (mass_continuous (w++[r]) c')
    apply continuous_finsetSum; intro c _
    apply continuous_finsetSum; intro j _
    by_cases he : T c r j=c'
    · simp only [ite_eq_left he]; exact flow_continuous w r c j
    · simp only [ite_eq_right he]; exact continuous_const
  convert h₁.inter (h₂.inter (h₃.inter (h₄.inter (h₅.inter (h₆.inter h₇)))) ) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact ⟨fun h=>⟨h.mass_nonneg,h.mass_total,h.initial,h.flow_nonneg,h.support,h.outflow,h.inflow⟩,
    fun ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩=>⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩⟩

theorem feasible_compact [Fintype R] (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) :
    IsCompact (feasible (H:=H) T allowed s) := isCompact_Icc.inter_right (valid_closed T allowed s)

theorem encode_feasible (F : Data R C J) (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (hF : Valid F T allowed s H) : encode F∈feasible (H:=H) T allowed s :=
  ⟨encode_bounds F T allowed s hF,decode_encode_valid F T allowed s hF⟩

theorem decode_encode_cost (F : Data R C J) (d : C→R→J→ℝ) (w u : List R) (hu : w.length+u.length≤H) :
    flowCost (decode (H:=H) (encode F)) d w u=flowCost F d w u := by
  induction u generalizing w with
  | nil => rfl
  | cons r u ih =>
    have hw : w.length<H := by simp only [List.length_cons] at hu; omega
    rw [flowCost,flowCost]
    congr 1
    · simp only [decode_encode_flow F w hw]
    · exact ih _ (by simp only [List.length_append,List.length_cons,List.length_nil] at *; omega)

theorem cost_continuous (d : C→R→J→ℝ) (w u : List R) :
    Continuous (fun x : Space R C J H=>flowCost (decode x) d w u) := by
  induction u generalizing w with
  | nil => exact continuous_const
  | cons r u ih =>
    apply Continuous.add _ (ih _)
    exact continuous_finsetSum _ fun c _=>continuous_finsetSum _ fun j _=>
      (flow_continuous w r c j).mul continuous_const

end UniformKServer.FiniteFlowSpace

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteSeparation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The exact finite separation step, with normalization and the empty-index
case handled from the stated hypotheses. No minimax theorem is assumed. -/
namespace UniformKServer.FiniteSeparation
open Finset FiniteProbability
open scoped Classical
variable {I : Type} [Fintype I]

theorem finite_minimax (K : Set (I→ℝ)) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hcompact : IsCompact K)
    (hlaw : ∀ P : Law I,∃x∈K,P.expect x≤0) :
    ∃x∈K,∀i,x i≤0 := by
  by_contra hn
  have hd : Disjoint (Set.Iic (0:I→ℝ)) K := by
    apply Set.disjoint_left.mpr
    intro x hx hK
    exact hn ⟨x,hK,hx⟩
  obtain ⟨f,u,v,hlo,huv,hhi⟩ := geometric_hahn_banach_closed_compact
    (convex_Iic (0:I→ℝ)) isClosed_Iic hconv hcompact hd
  have hu : 0<u := by simpa using hlo 0 (Set.mem_Iic.mpr le_rfl)
  let c : I→ℝ := fun i=>f (Pi.single i 1)
  have hc (i : I) : 0 ≤ c i := by
    by_contra hn
    have hn' : c i<0 := lt_of_not_ge hn
    let a : ℝ := (u+1)/(c i)
    have ha : a≤0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hn'.le
    have hm : a • Pi.single i (1:ℝ)∈Set.Iic (0:I→ℝ) := by
      intro j
      simp only [Pi.smul_apply,smul_eq_mul,Pi.single_apply,Pi.zero_apply]
      split_ifs <;> simp [ha]
    have hh := hlo _ hm
    rw [map_smul] at hh
    change a*c i<u at hh
    have he : a*c i=u+1 := div_mul_cancel₀ _ (ne_of_lt hn')
    rw [he] at hh
    linarith
  let total : ℝ := ∑i,c i
  have ht : 0<total := by
    have hnn : 0≤total := sum_nonneg fun i _=>hc i
    by_contra hn
    have hz : total=0 := le_antisymm (le_of_not_gt hn) hnn
    have hcz (i : I) : c i=0 := by
      have hs := single_le_sum (fun i _=>hc i) (mem_univ i)
      change c i≤total at hs
      rw [hz] at hs
      exact le_antisymm hs (hc i)
    obtain ⟨x,hx⟩ := hne
    have hh := hhi x hx
    rw [dual_sum] at hh
    change v<∑i,c i*x i at hh
    simp only [hcz,zero_mul,sum_const_zero] at hh
    linarith
  let P : Law I := ⟨fun i=>c i/total,fun i=>div_nonneg (hc i) ht.le,by
    rw [←sum_div]
    exact div_self (ne_of_gt ht)⟩
  obtain ⟨x,hx,hp⟩ := hlaw P
  have he : P.expect x=f x/total := by
    rw [dual_sum]
    simp only [Law.expect,P,div_mul_eq_mul_div,←sum_div]
    rfl
  rw [he] at hp
  have hh := hhi x hx
  have hf : f x≤0 := by simpa only [zero_mul] using (div_le_iff₀ ht).mp hp
  linarith

end UniformKServer.FiniteSeparation

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlowMinimax
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-law removal on the literal compact causal-flow polytope. -/
namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow FiniteProbability
open scoped Classical
variable {R C J : Type} [Fintype R] [Fintype C] [Fintype J] {H : ℕ}

omit [Fintype R] in
theorem costVector_continuous (d : C→R→J→ℝ) (q : Word R H→ℝ) :
    Continuous (costVector d q) :=
  continuous_pi fun v=>(cost_continuous d [] (letters v)).sub continuous_const

theorem eliminate (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (d : C→R→J→ℝ) (q : Word R H→ℝ)
    (hlaw : ∀P : Law (Word R H),∃ F : Data R C J,
      Valid F T allowed s H ∧
      P.expect (fun v=>flowCost F d [] (letters v))≤P.expect q) :
    ∃F : Data R C J,Valid F T allowed s H ∧
      ∀v : Word R H,flowCost F d [] (letters v)≤q v := by
  let K := costVector d q '' feasible (H:=H) T allowed s
  have hconv : Convex ℝ K := by
    intro u hu v hv a b ha hb hab
    obtain ⟨x,hx,rfl⟩ := hu
    obtain ⟨y,hy,rfl⟩ := hv
    exact ⟨a • x+b • y,feasible_convex T allowed s hx hy ha hb hab,costVector_combo d q a b hab x y⟩
  have hcompact : IsCompact K :=
    (feasible_compact T allowed s).image (costVector_continuous d q)
  have hp (P : Law (Word R H)) : ∃x∈K,P.expect x≤0 := by
    obtain ⟨F,hF,hcost⟩ := hlaw P
    refine ⟨costVector d q (encode F),⟨encode F,encode_feasible F T allowed s hF,rfl⟩,?_⟩
    have he : P.expect (costVector d q (encode F))=
        P.expect (fun v=>flowCost F d [] (letters v))-P.expect q := by
      unfold costVector
      rw [Law.expect_sub]
      congr 1
      apply congrArg P.expect
      funext v
      exact decode_encode_cost F d [] (letters v) (by simpa using letters_bound v)
    rw [he]
    linarith
  let P₀ : Law (Word R H) := ⟨fun v=>if v=code [] (by simp) then 1 else 0,
    by intro v; split_ifs <;> norm_num,by simp⟩
  obtain ⟨x,hx,_⟩ := hp P₀
  obtain ⟨y,hy,hneg⟩ := FiniteSeparation.finite_minimax K ⟨x,hx⟩ hconv hcompact hp
  obtain ⟨z,hz,rfl⟩ := hy
  refine ⟨decode z,hz.2,?_⟩
  intro v
  have := hneg v
  change flowCost (decode z) d [] (letters v)-q v≤0 at this
  linarith

end UniformKServer.FiniteFlowSpace

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteTable
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.FiniteTable
open EffectiveLP

theorem fallback_mem {n k : ℕ} [NeZero k] (c : Config n k) (r : Fin n) :
    fallback c r ∈ labels c r := by
  simp only [fallback, dite_eq_left (labels_nonempty c r)]
  exact Finset.min'_mem _ _

theorem flowCost_exact {n k H : ℕ} (d : RationalMetric n) (F : BoundedFlow n k H ℚ)
    (w : Word n H) :
    FiniteFlow.flowCost (globalFlow F) (charge d) [] w.val =
      ∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
        F.flow (prefixNode w i) w.val[i] c j * d.distance (c.val j.val) w.val[i] := by
  rw [flowCost_prefix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro c _
  have hi : (w.val.take i).length < H := (prefixNode w i).property
  simp only [globalFlow, List.nil_append, dite_eq_left hi, charge]
  rw [← sum_labels c w.val[i]]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [zero_mul]
  rfl

end UniformKServer.FiniteTable



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformParameters
attribute [-instance] _root_.OAI.UniformKServer.EpochControl.instFiniteBList _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The source's freely chosen small constants are fixed once and for all.
The parent construction has one absolute squared-log coefficient. -/
namespace UniformKServer.PartitionTree
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]

def fixedPilot : TierPilot.Parameters where
  sigma := 1/1000000
  gammaH := 1/1000
  gammaL := 1/100000000
  deltaH := 1/10000
  sigma_pos := by norm_num
  sigma_small := by norm_num
  sigma_gamma := by norm_num
  gammaH_small := by norm_num
  gammaL_pos := by norm_num
  gammaL_small := by norm_num
  deltaH_pos := by norm_num
  deltaH_small := by norm_num

def fixedExponent : ℝ := max 1 (TierInsertion.lifetimeExponent fixedPilot)

def fixedConfig (R : ℝ) (hR : 0<R) (base : X) : ActualPartitions.Config X where
  P := fixedPilot
  C := fixedExponent
  C_one := le_max_left _ _
  C_large := le_max_right _ _
  R := R
  R_pos := hR
  q := fixedShift
  q_pos := by norm_num [fixedShift]
  q_small := by norm_num [fixedShift]
  shiftH := by norm_num [fixedShift,fixedPilot]
  shiftL := by norm_num [fixedShift,fixedPilot]
  base := base

theorem terminal_scale (A : ActualPartitions.Config X) :
    ∃ J : ℕ,0<J ∧ ∀ x y : X,x≠y → 20*radius A J<dist x y := by
  have ht : Filter.Tendsto (fun J : ℕ=>20*radius A J) Filter.atTop (nhds 0) := by
    have hh := (tendsto_const_nhds (x:=20*A.R)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one A.q_pos.le (by linarith [A.q_small]))
    simpa only [mul_zero,radius,mul_assoc] using hh
  have he (x y : X) : ∀ᶠ J : ℕ in Filter.atTop,x≠y → 20*radius A J<dist x y := by
    by_cases h : x=y
    · exact Filter.Eventually.of_forall (fun _ hn=>(hn h).elim)
    · exact (ht.eventually (gt_mem_nhds (dist_pos.mpr h))).mono (fun _ hh _=>hh)
  have hh : ∀ᶠ J : ℕ in Filter.atTop,∀ x y : X,x≠y → 20*radius A J<dist x y :=
    Filter.eventually_all.mpr (fun x=>Filter.eventually_all.mpr (he x))
  obtain ⟨J,hJ,h⟩ := ((Filter.eventually_gt_atTop 0).and hh).exists
  exact ⟨J,hJ,h⟩

omit [Fintype X] [MetricSpace X]

def allocationScalar (A : ActualPartitions.Config X) : ℝ :=
  (8*(10:ℝ)^63/A.q)*(A.editBound+separationRate A)

def rawRate (A : ActualPartitions.Config X) : ℝ :=
  (15840+160*(12/5)*(1+1/22))*allocationScalar A+
    160*(289*((6/5)*132)*(A.editBound+separationRate A)+driftScalar/3)

theorem ell_log (k : ℕ) (hk : 1≤k) : EpochAlpha.ell k≤logFactor*Real.log (k+1) := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (2:ℝ)≤k+1 := by exact_mod_cast (show 2≤k+1 by omega)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) hk'
  have hh : 1≤Real.log (k+1)/Real.log 2 := (le_div_iff₀ h₂).mpr (by simpa using hl)
  unfold EpochAlpha.ell logFactor
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

/-- This coefficient contains only the fixed numerical parameters, never an
instance size, aspect ratio, tree height, hidden law, or horizon. -/
def absoluteRate : ℝ := rawRate (fixedConfig (X:=PUnit) 1 (by norm_num) PUnit.unit)*logFactor^2

theorem rawRate_fixed (R : ℝ) (hR : 0<R) (base : X) :
    rawRate (fixedConfig R hR base)=rawRate (fixedConfig (X:=PUnit) 1 (by norm_num) PUnit.unit) := rfl

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
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree PilotEdits
open scoped Classical
variable {n k N : ℕ} [NeZero k] {Ω : Type} [Fintype Ω]

theorem support_nonempty (P : Law Ω) : Nonempty (PositiveSupport.Support P.weight) := by
  by_contra hn
  have hz (ω : Ω) : P.weight ω=0 := by
    apply le_antisymm _ (P.nonneg ω)
    exact le_of_not_gt (fun h=>hn ⟨⟨ω,h⟩⟩)
  have hh := P.total
  simp only [hz,sum_const_zero] at hh
  norm_num at hh

end UniformKServer.OfflineLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetRealization
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

/-! Exact conditional rows for an additive-offset rational LP. -/
namespace UniformKServer.OffsetRealization
open EffectiveLP FiniteTable
theorem global_valid {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ) (A : ℚ)
    (hF : OffsetLP.Valid d u A F a) :
    FiniteFlow.Valid (globalFlow F) FiniteTable.next (fun c r j => j ∈ labels c r) u H := by
  rcases hF with ⟨ha,hn,ht,hi,hfn,ho,hii,hcost⟩
  constructor
  · intro w hw c
    simpa only [globalFlow, dite_eq_left hw] using hn ⟨w,(mem_words w).mpr hw⟩ c
  · intro w hw
    simpa only [globalFlow, dite_eq_left hw] using ht ⟨w,(mem_words w).mpr hw⟩
  · intro c
    change (if h : [].length ≤ H then F.mass ⟨[], (mem_words []).mpr h⟩ c else 0) = _
    split
    · exact hi c
    · rename_i h
      exact (h (Nat.zero_le H)).elim
  · intro w hw r c j
    simp only [globalFlow, dite_eq_left hw]
    split_ifs with hj
    · exact hfn ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c ⟨j,hj⟩
    · exact le_refl _
  · intro w hw r c j hj
    simp only [globalFlow, dite_eq_left hw, dite_eq_right hj]
  · intro w hw r c
    simp only [globalFlow, dite_eq_left hw, dite_eq_left hw.le, sum_labels]
    exact ho ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c
  · intro w hw r c'
    have hext : (w++[r]).length ≤ H := by simp only [List.length_append, List.length_singleton]; omega
    simp only [globalFlow, dite_eq_left hw, dite_eq_left hext]
    have hs (c : Config n k) :
        (∑ j, if FiniteTable.next c r j = c' then
          (if hj : j ∈ labels c r then F.flow ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c ⟨j,hj⟩ else 0)
          else 0) =
        ∑ j : Label c r, if EffectiveLP.step c r j = c' then
          F.flow ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c j else 0 := by
      rw [← sum_labels c r]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ labels c r
      · simp only [FiniteTable.next, dite_eq_left hj]
      · simp only [dite_eq_right hj, ite_self]
    simp only [hs]
    exact hii ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c'

theorem realize_proof {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ) (A : ℚ)
    (hF : OffsetLP.Valid d u A F a) :
    (∀ w r c j, 0 ≤ row F w r c j) ∧
    (∀ w r c, ∑ j, row F w r c j = 1) ∧
    (∀ w r c j, j ∉ labels c r → row F w r c j = 0) ∧
    (∀ w, w.length ≤ H →
      FiniteFlow.cost (row F) FiniteTable.next (FiniteTable.charge d) [] u w ≤
        A * OfflineDynamic.optRat d u.val w+a) := by
  have hv := global_valid d u F a A hF
  obtain ⟨hn,hs,hp,hc⟩ := FiniteFlow.realization (globalFlow F) next
    (fun c r j => j ∈ labels c r) u H fallback fallback_mem hv
  refine ⟨hn,hs,hp,?_⟩
  intro w hw
  let w' : Word n H := ⟨w,(mem_words w).mpr hw⟩
  calc
    FiniteFlow.cost (row F) FiniteTable.next (FiniteTable.charge d) [] u w =
        FiniteFlow.flowCost (globalFlow F) (FiniteTable.charge d) [] w := hc (FiniteTable.charge d) w hw
    _ = _ := flowCost_exact d F w'
    _ ≤ _ := hF.2.2.2.2.2.2.2 w'



end UniformKServer.OffsetRealization

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TypedStack
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open StackCompiler
open scoped Classical

variable {Q K : Type*} {g : ℕ}

def initial (P : Processor Q K g) (input : List Bool) : State Q K g :=
  ⟨P.start,BitTape.ofWord input,fun _=>[],[],false⟩
def run (P : Processor Q K g) (s : State Q K g) (coins : List Bool) : State Q K g :=
  coins.foldl (step P) s

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2
open TypedStack
open scoped Classical

inductive Key where
  | base (k : K') | pay | buf
  deriving DecidableEq,Fintype
abbrev main : Key := .base .main
abbrev digit (b : Bool) : Fin g := FlatTM2.letters (RawBits.letter b)
abbrev sep : Fin g := FlatTM2.letters Γ'.cons
abbrev Action (qc qa : ℕ) := TypedStack.Action (Control qc qa) Key g
abbrev State (qc qa : ℕ) := TypedStack.State (Control qc qa) Key g

variable {qc qa : ℕ}
def pass (q : Control qc qa) (y : Bool:=false) : Action qc qa :=
  {control:=q,yield:=y}
def write (q : Control qc qa) (k : Key) (a : Fin g) : Action qc qa :=
  {control:=q,stackOp:=fun j=>if j=k then .push a else .keep}
def pop (q : Control qc qa) (k : Key) (y : Bool:=false) : Action qc qa :=
  {control:=q,stackOp:=fun j=>if j=k then .pop else .keep,yield:=y}
def move (q : Control qc qa) (src dst : Key) (a : Fin g) : Action qc qa :=
  {control:=q,stackOp:=fun j=>if j=src then .pop else if j=dst then .push a else .keep}
def read (q exit : Control qc qa) (i : Option Bool) : Action qc qa :=
  match i with
  | none=>pass exit
  | some b=>{write q .buf (digit b) with inputMove:=.right}
def drain (q exit : Control qc qa) (src : Key) (h : Key→Option (Fin g)) : Action qc qa :=
  match h src with
  | none=>pass exit
  | some a=>move q src main a

def lift {q' : ℕ} (q : Control qc qa) (a : StackCompiler.Action q' (Fintype.card K') g) (y : Bool) : Action qc qa :=
  {control:=q,stackOp:=fun j=>match j with
    | .base k=>a.stackOp (FlatTM2.keys k)
    | _=>.keep,yield:=y}

def processor (C : StackCompiler.Processor qc (Fintype.card K') g)
    (A : StackCompiler.Processor qa (Fintype.card K') g) : TypedStack.Processor (Control qc qa) Key g where
  start:=.bootCons
  transition:=fun q inp h coin=>match q with
  | .bootCons=>write .bootOne main sep
  | .bootOne=>write .bootRead main (digit true)
  | .bootRead=>read .bootRead .bootDrain inp
  | .bootDrain=>match h .buf with
    | none=>pass (.construct C.start) true
    | some a=>move .bootDrain .buf main a
  | .construct c=>
    let a:=C.transition c none (fun i=>h (.base (FlatTM2.keys.symm i))) false
    lift (bif a.yield then .pad else .construct a.control) a true
  | .pad=>if h main=some sep then pop .sample main true else pop .pad main true
  | .sample=>if h main=some (digit false) then move .sample main .buf (digit coin)
    else pop .sampleSep main
  | .sampleSep=>pop .savePayload main
  | .savePayload=>if h main=some sep then pop .randomCons main
    else match h main with
    | none=>pass .randomCons
    | some a=>move .savePayload main .pay a
  | .randomCons=>write .randomOne main sep
  | .randomOne=>write .randomDrain main (digit true)
  | .randomDrain=>drain .randomDrain .requestCons .buf h
  | .requestCons=>write .requestRead main sep
  | .requestRead=>read .requestRead .requestOne inp
  | .requestOne=>write .requestDrain main (digit true)
  | .requestDrain=>drain .requestDrain .payloadCons .buf h
  | .payloadCons=>write .payloadDrain main sep
  | .payloadDrain=>drain .payloadDrain (.active A.start) .pay h
  | .active c=>
    let a:=A.transition c none (fun i=>h (.base (FlatTM2.keys.symm i))) false
    lift (bif a.yield then .emit else .active a.control) a false
  | .emit=>if h main=some sep then pop .sample main true
    else {pop .emit main with emit:=some (decide (h main=some (digit true)))}

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

def UniformRun (P : Processor Q K g) (s : State Q K g) (t : ℕ) (z : State Q K g) : Prop :=
  ∀bs : List Bool,bs.length=t → run P s bs=z

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}

def wordState (q : Control qc qa) (input : BitTape) (m p b : List (Fin g))
    (out : List Bool:=[]) (y : Bool:=false) : State qc qa :=
  ⟨q,input,(fun i=>match i with
    | .base .main=>m | .pay=>p | .buf=>b | _=>[]),out,y⟩

@[simp] theorem digit_ne_sep (b : Bool) : digit b≠sep := by
  intro h
  have he:=FlatTM2.letters.injective h
  cases b <;> cases he
@[simp] theorem sep_ne_digit (b : Bool) : sep≠digit b := Ne.symm (digit_ne_sep b)
@[simp] theorem digit_eq_digit (b c : Bool) : digit b=digit c ↔ b=c := by
  constructor
  · intro h;have he:=FlatTM2.letters.injective h;cases b <;> cases c <;> cases he <;> rfl
  · rintro rfl;rfl

theorem wordState_ext {s z : State qc qa} (hc : s.control=z.control) (hi : s.input=z.input)
    (hs : ∀k,s.store k=z.store k) (ho : s.outputRev=z.outputRev) (hy : s.yielded=z.yielded) : s=z := by
  cases s;cases z;simp_all only
  congr
  exact funext hs

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperInterpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa q' : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

def inside (q : Control qc qa) (i : BitTape)
    (s : StackCompiler.State q' (Fintype.card K') g) (y : Bool) : State qc qa :=
  ⟨q,i,fun k=>match k with | .base k=>s.store (FlatTM2.keys k) | _=>[],[],y⟩

def constructState (s : StackCompiler.State qc (Fintype.card K') g) (i : BitTape) : State qc qa :=
  inside (bif s.yielded then .pad else .construct s.control) i s true

def activeState (s : StackCompiler.State qa (Fintype.card K') g) (i : BitTape) : State qc qa :=
  inside (bif s.yielded then .emit else .active s.control) i s false

theorem construct_step (hC : StackPrimitive.Deterministic C)
    (s : StackCompiler.State qc (Fintype.card K') g) (hy : s.yielded=false)
    (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) {constructState (qa:=qa) s i with yielded:=false} coin=
      constructState (StackCompiler.step C s false) i := by
  unfold StackPrimitive.Deterministic at hC
  unfold TypedStack.step constructState inside
  simp only [hy,Bool.false_eq_true,↓reduceIte,Bool.cond_false,processor,lift,
    Equiv.apply_symm_apply,BitTape.shift,StackCompiler.step,hC]
  apply wordState_ext <;> try rfl
  intro k;cases k <;> rfl

theorem cap_succ (P : StackCompiler.Processor q' (Fintype.card K') g)
    (s : StackCompiler.State q' (Fintype.card K') g) (t : ℕ) :
    StackCompiler.run P s (List.replicate (t+1) false)=
      StackCompiler.step P (StackCompiler.run P s (List.replicate t false)) false := by
  rw [show t+1=t+1 from rfl,List.replicate_add,StackCompiler.run_append]
  rfl

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperPrefix
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

 def Prefix.append {P : Processor Q K g} {a b c : State Q K g} {d e : ℕ}
    (h : Prefix P a b d) (h' : Prefix P b c e) : Prefix P a c (d+e) := by
  let f:=fun j=>if j<d then h.state j else h'.state (j-d)
  refine ⟨f,?_,?_,?_⟩
  · dsimp [f]
    split_ifs with hd
    · exact h.start
    · have he : d=0:=by omega
      subst d
      simpa only [Nat.sub_self,h'.start] using h.finish.symm.trans h.start
  · simpa only [f,show ¬d+e<d by omega,↓reduceIte,Nat.add_sub_cancel_left] using h'.finish
  · intro j hj
    dsimp [f]
    by_cases hd : j<d
    · rw [ite_eq_left hd]
      by_cases hs : j+1<d
      · rw [ite_eq_left hs];exact h.next j hd
      · rw [ite_eq_right hs]
        have he : j+1=d:=by omega
        rw [he,Nat.sub_self,h'.start]
        have hh:=h.next j hd
        rw [he,h.finish] at hh
        exact hh
    · rw [ite_eq_right hd,ite_eq_right (by omega)]
      have he : j+1-d=(j-d)+1:=by omega
      rw [he]
      exact h'.next (j-d) (by omega)

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 def constructor_prefix (hC : StackPrimitive.Deterministic C)
    (s : StackCompiler.State qc (Fintype.card K') g) (t : ℕ)
    (ht : ∀j<t,(StackCompiler.run C s (List.replicate j false)).yielded=false) :
    Prefix (processor C A) (constructState s BitTape.blank)
      (constructState (StackCompiler.run C s (List.replicate t false)) BitTape.blank) t := by
  refine ⟨fun j=>constructState (StackCompiler.run C s (List.replicate j false)) BitTape.blank,rfl,rfl,?_⟩
  intro j hj
  refine ⟨rfl,rfl,?_⟩
  intro w coin
  rw [cap_succ]
  exact construct_step C A hC _ (ht j hj) (BitTape.ofWord w) coin

 theorem pad_digit (i : BitTape) (a : Bool) (m : List (Fin g)) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .pad i (digit a::m) [] []) coin=
      wordState .pad i m [] [] [] true := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_ne_sep,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem pad_sep (i : BitTape) (m : List (Fin g)) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .pad i (sep::m) [] []) coin=
      wordState .sample i m [] [] [] true := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 def padding_prefix (w : List Bool) (m : List (Fin g)) :
    Prefix (processor C A) (wordState .pad BitTape.blank (w.map digit++sep::m) [] [] [] true)
      (wordState .sample BitTape.blank m [] [] [] true) (w.length+1) := by
  induction w with
  | nil=>
    refine ⟨fun j=>if j=0 then wordState .pad BitTape.blank (sep::m) [] [] [] true
      else wordState .sample BitTape.blank m [] [] [] true,by simp,by simp,?_⟩
    intro j hj
    have he : j=0:=by simp only [List.length_nil] at hj;omega
    subst j
    simp only [↓reduceIte,Nat.zero_add,Nat.one_ne_zero]
    exact ⟨rfl,rfl,fun a b=>pad_sep C A (BitTape.ofWord a) m b⟩
  | cons b w ih=>
    have h : Prefix (processor C A)
        (wordState .pad BitTape.blank ((b::w).map digit++sep::m) [] [] [] true)
        (wordState .pad BitTape.blank (w.map digit++sep::m) [] [] [] true) 1 := by
      refine ⟨fun j=>if j=0 then wordState .pad BitTape.blank ((b::w).map digit++sep::m) [] [] [] true
        else wordState .pad BitTape.blank (w.map digit++sep::m) [] [] [] true,by simp,by simp,?_⟩
      intro j hj
      have he : j=0:=by omega
      subst j
      simp only [↓reduceIte,Nat.zero_add,Nat.one_ne_zero]
      exact ⟨rfl,rfl,fun a c=>pad_digit C A (BitTape.ofWord a) b (w.map digit++sep::m) c⟩
    convert h.append ih using 1
    all_goals try with_reducible_and_instances rfl
    simp [List.length_cons,Nat.add_comm]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

theorem buf_step (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (a : Fin g) (xs m p : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p (a::xs) out) coin=
      wordState q i (a::m) p xs out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,List.head?_cons,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

end UniformKServer.UniformWrapper

end

end OAI
end


