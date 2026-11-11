-- Prove2me | Definitions.Def_Q220Uk000
-- name    : Q220Uk000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:38:17.007578+00:00
-- url     : https://prove2.me/theorems/c3079b50-d83b-4ff5-b8de-a886ce55e3ef
-- title:
--   Definitions bundle Q220Uk000 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 638 declarations of OpenAI's Lean: 267 definitions, 17 inductive types or structures, 2 instances and 352 theorems. The definitions and types are `OAI.UniformKServer.ActualPartitions.Config`, `OAI.UniformKServer.ActualPartitions.Config.auxiliary`, `OAI.UniformKServer.ActualPartitions.Config.auxiliaryCap`, `OAI.UniformKServer.ActualPartitions.Config.editBound`, `OAI.UniformKServer.ActualPartitions.Config.editEndpoint`, `OAI.UniformKServer.ActualPartitions.Config.editRate`, `OAI.UniformKServer.ActualPartitions.Config.input`, `OAI.UniformKServer.ActualPartitions.Config.keyEditCost`, `OAI.UniformKServer.ActualPartitions.Config.pilotCharge`, `OAI.UniformKServer.ActualPartitions.Config.pilotParameter`, `OAI.UniformKServer.ActualPartitions.Config.totalPilotCharge`, `OAI.UniformKServer.ActualRoster.active`, `OAI.UniformKServer.ActualRoster.compulsory`, `OAI.UniformKServer.ActualRoster.next`, `OAI.UniformKServer.ActualRoster.rosterDecEq`, `OAI.UniformKServer.ActualRoster.survival`, `OAI.UniformKServer.ActualRoster.valid`, `OAI.UniformKServer.AllocationSchedule.compared`, `OAI.UniformKServer.AllocationSchedule.held`, `OAI.UniformKServer.AllocationSchedule.relativeUpdate`, `OAI.UniformKServer.AllocationSchedule.schedule`, `OAI.UniformKServer.AllocationSchedule.size`, `OAI.UniformKServer.AllocationSchedule.update`, `OAI.UniformKServer.ChronologicalRoster.age`, `OAI.UniformKServer.ChronologicalRoster.young`, `OAI.UniformKServer.CoarseData.activeState`, `OAI.UniformKServer.CoarseData.cutoff`, `OAI.UniformKServer.CoarseData.heldSize`, `OAI.UniformKServer.CoarseData.sizeEstimate`, `OAI.UniformKServer.CoarseData.sizeTolerance`, `OAI.UniformKServer.ConditionalLaw.kernel`, `OAI.UniformKServer.ConditionalLaw.mass`, `OAI.UniformKServer.ConditionalLaw.measurable`, `OAI.UniformKServer.ConditionalLaw.posterior`, `OAI.UniformKServer.ConditionalRank.indicator`, `OAI.UniformKServer.ConditionalRank.input`, `OAI.UniformKServer.ConditionalRanks.countInput`, `OAI.UniformKServer.ConditionalRanks.rankProbability`, `OAI.UniformKServer.CooldownLabels.Slot`, `OAI.UniformKServer.CooldownLabels.State` and 244 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualAuxiliary`, `UniformKServer_ActualEditCosts`, `UniformKServer_ActualEditFinance`, `UniformKServer_ActualFineCaps`, `UniformKServer_ActualLevelPilot`, `UniformKServer_ActualPartitions`, `UniformKServer_ActualPilot`, `UniformKServer_ActualRoster`, `UniformKServer_AllocationSchedule`, `UniformKServer_CausalHeavy`, `UniformKServer_CausalLevel`, `UniformKServer_CausalLevelAux`, `UniformKServer_CausalRosters`, `UniformKServer_CausalTier`, `UniformKServer_ChronologicalRoster`, `UniformKServer_CoarseBridge`, `UniformKServer_CoarseData`, `UniformKServer_ConditionalLaw`, `UniformKServer_ConditionalRank`, `UniformKServer_ConditionalRanks`, `UniformKServer_CooldownLabels`, `UniformKServer_DyadicTiers`, `UniformKServer_EpochAlpha`, `UniformKServer_EpochGeometry`, `UniformKServer_EpochParameters`, `UniformKServer_FineCaps`, `UniformKServer_FineVariation`, `UniformKServer_FinitePiLaw`, `UniformKServer_FiniteProbability`, `UniformKServer_FiniteThreshold`, `UniformKServer_FirstEdits`, `UniformKServer_FirstHit`, `UniformKServer_FirstHitSupport`, `UniformKServer_FirstStructure`, `UniformKServer_FlexEstimates`, `UniformKServer_GeometricMass`, `UniformKServer_HeavyEditPayment`, `UniformKServer_HeavyEditRamp`, `UniformKServer_HeavyFiniteLaw`, `UniformKServer_HeavyPilot`, `UniformKServer_HeavyProcess`, `UniformKServer_HeavyProcessEdits`, `UniformKServer_HeavyRadius`, `UniformKServer_HeavyRecordGeometry`, `UniformKServer_HeavyRecords`, `UniformKServer_HeavySchedule`, `UniformKServer_HeavyTape`, `UniformKServer_HiddenCausality`, `UniformKServer_HiddenFlow`, `UniformKServer_KeyEdits`, `UniformKServer_LevelAllowances`, `UniformKServer_LevelHeavy`, `UniformKServer_LevelHeavyEdits`, `UniformKServer_LevelKeyLedger`, `UniformKServer_LevelMap`, `UniformKServer_LevelMassLedger`, `UniformKServer_LevelSeparation`, `UniformKServer_LevelSerial`, `UniformKServer_LevelTierEdits`, `UniformKServer_LevelTierLedger`, `UniformKServer_ParameterGaps`, `UniformKServer_ParentBeta`, `UniformKServer_ParentScale`, `UniformKServer_PartitionCausal`, `UniformKServer_PartitionLevel`, `UniformKServer_PartitionScales`, `UniformKServer_PiFirstHit`, `UniformKServer_PiFresh`, `UniformKServer_PiIntegrate`, `UniformKServer_PilotCompact`, `UniformKServer_PilotCredits`, `UniformKServer_PilotEdits`, `UniformKServer_PilotFamily`, `UniformKServer_PilotSlope`, `UniformKServer_PilotTemplates`, `UniformKServer_RadiusFirstHit`, `UniformKServer_RadiusRoster`, `UniformKServer_RadiusTail`, `UniformKServer_RankData`, `UniformKServer_RankFunctions`, `UniformKServer_RankSuperadditivity`, `UniformKServer_RankTracking`, `UniformKServer_ShortRoster`, `UniformKServer_ShortRosterValidity`, `UniformKServer_SideParameters`, `UniformKServer_StarParameters`, `UniformKServer_StarRanks`, `UniformKServer_TierFrozen`, `UniformKServer_TierInsertion`, `UniformKServer_TierKeyEdits`, `UniformKServer_TierKeyProcess`, `UniformKServer_TierKeys`, `UniformKServer_TierLabeledKeys`, `UniformKServer_TierLabels`, `UniformKServer_TierLifetimes`, `UniformKServer_TierParameters`, `UniformKServer_TierPilot`, `UniformKServer_TierRadius`, `UniformKServer_TierRetirement`, `UniformKServer_TierSchedule`, `UniformKServer_TierShortSchedule`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk004`, `Q220Uk005` and `Q220Uk006`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.Q220_UK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConditionalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Finite posterior calculus for the finite-law construction.  All conditional
 laws are computed from fiber weights, including the zero-probability fibers.
 This supplies, rather than assumes, the all-step filtering identities. -/
namespace UniformKServer.ConditionalLaw
noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
variable {Ω : Type*} [Fintype Ω]

def mass (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) : ℝ :=
  ∑ v, if F.r ω v then w v else 0

def kernel (w : Ω → ℝ) (F : Setoid Ω) (ω v : Ω) : ℝ :=
  if F.r ω v then w v / mass w F ω else 0

def posterior (w : Ω → ℝ) (F : Setoid Ω) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ v, kernel w F ω v * X v

def measurable (F : Setoid Ω) (X : Ω → ℝ) : Prop :=
  ∀ ω v, F.r ω v → X ω = X v

theorem mass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω : Ω) :
    0 ≤ mass w F ω := sum_nonneg fun v _ => by
  split_ifs
  · exact hw v
  · exact le_rfl

theorem weight_le_mass {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω : Ω) :
    w ω ≤ mass w F ω := by
  have h := single_le_sum (f := fun v => if F.r ω v then w v else 0)
    (fun v (_ : v ∈ univ) => by split_ifs; exact hw v; exact le_rfl) (mem_univ ω)
  simpa only [mass,ite_eq_left (F.refl ω)] using h

theorem mass_eq (w : Ω → ℝ) (F : Setoid Ω) {ω v : Ω} (h : F.r ω v) :
    mass w F ω = mass w F v := by
  apply sum_congr rfl
  intro z _
  have he : F.r ω z ↔ F.r v z := ⟨fun h' => F.trans (F.symm h) h',fun h' => F.trans h h'⟩
  simp only [he]

theorem kernel_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω v : Ω) :
    0 ≤ kernel w F ω v := by
  unfold kernel
  split_ifs
  · exact div_nonneg (hw v) (mass_nonneg hw F ω)
  · rfl

theorem kernel_sum (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) :
    (∑ v, kernel w F ω v) = mass w F ω/mass w F ω := by
  calc
    _ = ∑ v, (if F.r ω v then w v else 0)/mass w F ω := by
      apply sum_congr rfl
      intro v _
      by_cases h : F.r ω v
      · simp only [kernel,ite_eq_left h]
      · simp only [kernel,ite_eq_right h,zero_div]
    _ = _ := by rw [←sum_div]; rfl

theorem balance (w : Ω → ℝ) (F : Setoid Ω) (ω v : Ω) :
    w ω*kernel w F ω v = w v*kernel w F v ω := by
  by_cases h : F.r ω v
  · simp only [kernel,ite_eq_left h,ite_eq_left (F.symm h),mass_eq w F h]
    ring
  · have h' : ¬F.r v ω := fun h' => h (F.symm h')
    simp only [kernel,ite_eq_right h,ite_eq_right h',mul_zero]

theorem weighted_kernel_sum {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (v : Ω) :
    (∑ ω, w ω*kernel w F ω v) = w v := by
  simp_rw [balance w F]
  rw [←mul_sum,kernel_sum]
  by_cases h : mass w F v = 0
  · have hz : w v = 0 := le_antisymm (by simpa only [h] using weight_le_mass hw F v) (hw v)
    simp only [hz,zero_mul]
  · rw [div_self h,mul_one]

theorem posterior_measurable (w : Ω → ℝ) (F : Setoid Ω) (X : Ω → ℝ) :
    measurable F (posterior w F X) := by
  intro ω v h
  apply sum_congr rfl
  intro z _
  have he : F.r ω z ↔ F.r v z := ⟨fun h' => F.trans (F.symm h) h',fun h' => F.trans h h'⟩
  simp only [kernel,he,mass_eq w F h]

/-- The finite conditional-expectation identity. The test function is old
 history measurable; no restriction to a later selected event is made. -/
theorem test_identity {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (a X : Ω → ℝ) (ha : measurable F a) :
    (∑ ω, w ω*a ω*posterior w F X ω) = ∑ ω, w ω*a ω*X ω := by
  simp only [posterior,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  have he (ω : Ω) : w ω*a ω*(kernel w F ω v*X v) =
      (a v*X v)*(w ω*kernel w F ω v) := by
    by_cases h : F.r ω v
    · rw [ha ω v h]; ring
    · simp only [kernel,ite_eq_right h,mul_zero,zero_mul]
  simp_rw [he]
  rw [←mul_sum,weighted_kernel_sum hw]
  ring

theorem filtering {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F G : Setoid Ω)
    (hGF : ∀ ω v, G.r ω v → F.r ω v) (a X : Ω → ℝ) (ha : measurable F a) :
    (∑ ω, w ω*a ω*(posterior w G X ω-posterior w F X ω)) = 0 := by
  simp only [mul_sub,sum_sub_distrib]
  rw [test_identity hw G a X (fun ω v h => ha ω v (hGF ω v h)),test_identity hw F a X ha,sub_self]

theorem posterior_nonneg {w X : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hX : ∀ ω, 0 ≤ X ω) (F : Setoid Ω) (ω : Ω) :
    0 ≤ posterior w F X ω := sum_nonneg fun v _ => mul_nonneg (kernel_nonneg hw F ω v) (hX v)

theorem posterior_le_one {w X : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hX : ∀ ω, X ω ≤ 1) (F : Setoid Ω) (ω : Ω) :
    posterior w F X ω ≤ 1 := by
  calc
    _ ≤ ∑ v, kernel w F ω v := sum_le_sum fun v _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hX v) (kernel_nonneg hw F ω v)
    _ ≤ 1 := by rw [kernel_sum]; exact div_self_le_one (mass w F ω)

end
end UniformKServer.ConditionalLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankTracking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

                                                                    
                                                                          
                                                                              
                                                                     
namespace UniformKServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

def average (μ : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, μ ω * X ω

def measurableAt (F : ℕ → Setoid Ω) (t : ℕ) (X : Ω → ℝ) : Prop :=
  ∀ ω ω', (F t).r ω ω' → X ω = X ω'

structure Input (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_total : ∑ ω, weight ω = 1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω ω', (filtration (t + 1)).r ω ω' → (filtration t).r ω ω'
  posterior : ℕ → Ω → ℝ
  filtered : ℕ → Ω → ℝ
  posterior_range : ∀ t ω, posterior t ω ∈ Set.Icc (0 : ℝ) 1
  filtered_range : ∀ t ω, filtered t ω ∈ Set.Icc (0 : ℝ) 1
  posterior_measurable : ∀ t, measurableAt filtration t (posterior t)
  filtering : ∀ t X, measurableAt filtration t X →
    average weight (fun ω => X ω * (filtered (t + 1) ω - posterior t ω)) = 0

noncomputable def reference (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) : ℕ → Ω → ℝ
  | 0, ω => I.posterior 0 ω
  | t + 1, ω =>
    if f (I.posterior (t + 1) ω) ≤ (1 + ξ) * f (reference I f ξ t ω) ∧
       f (reference I f ξ t ω) ≤ (1 + ξ) * f (I.posterior (t + 1) ω)
    then reference I f ξ t ω else I.posterior (t + 1) ω

noncomputable def estimate (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  f (reference I f ξ t ω)


theorem reference_range (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) :
    ∀ t ω, reference I f ξ t ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact I.posterior_range 0
  | succ t ih =>
    intro ω
    rw [reference]
    split
    · exact ih ω
    · exact I.posterior_range (t+1) ω

theorem estimate_spec (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) (hξ : 0 < ξ)
    (hf : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f p) (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹ * f (I.posterior t ω) ≤ estimate I f ξ t ω ∧
      estimate I f ξ t ω ≤ (1+ξ) * f (I.posterior t ω) := by
  have hpos : 0 < 1+ξ := by linarith
  have hself : f (I.posterior t ω) ≤ (1+ξ)*f (I.posterior t ω) := by
    have := hf _ (I.posterior_range t ω)
    nlinarith
  have hsym : f (I.posterior t ω) ≤ (1+ξ)*estimate I f ξ t ω ∧
      estimate I f ξ t ω ≤ (1+ξ)*f (I.posterior t ω) := by
    cases t with
    | zero => simpa [estimate, reference] using And.intro hself hself
    | succ t =>
      simp only [estimate, reference]
      split
      · assumption
      · exact ⟨hself, hself⟩
  constructor
  · have hdiv : f (I.posterior t ω) / (1+ξ) ≤ estimate I f ξ t ω :=
      (div_le_iff₀ hpos).mpr (by nlinarith [hsym.1])
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · exact hsym.2


/-- The held posterior used for the source's fixed-threshold core flags. -/
noncomputable def absoluteReference (I : Input Ω) (δ : ℝ) : ℕ → Ω → ℝ
  | 0, ω => I.posterior 0 ω
  | t + 1, ω =>
    if |I.posterior (t + 1) ω - absoluteReference I δ t ω| ≤ δ
    then absoluteReference I δ t ω else I.posterior (t + 1) ω

theorem absoluteReference_spec (I : Input Ω) (δ : ℝ) (hδ : 0 ≤ δ) (t : ℕ) (ω : Ω) :
    |I.posterior t ω - absoluteReference I δ t ω| ≤ δ := by
  cases t with
  | zero => simpa [absoluteReference] using hδ
  | succ t =>
    rw [absoluteReference]
    split
    · assumption
    · simpa using hδ

end UniformKServer.RankTracking

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConditionalRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Source §02/§03: the rank-tracker input is constructed from a hidden count,
 not obtained by assuming a martingale. Summed posterior rank drift is bounded
 by the actual count drift, with coefficient one. -/
namespace UniformKServer.ConditionalRank
noncomputable section
open Finset ConditionalLaw
variable {Ω : Type*} [Fintype Ω]

def indicator (n j : ℕ) : ℝ := if n ≤ j then 1 else 0

theorem indicator_range (n j : ℕ) : indicator n j ∈ Set.Icc (0:ℝ) 1 := by
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_sum {n k : ℕ} (hn : n ≤ k) :
    (∑ j ∈ range k, indicator n j) = (k:ℝ)-n := by
  induction k with
  | zero =>
    have : n=0 := by omega
    subst n
    simp
  | succ k ih =>
    by_cases hk : n ≤ k
    · rw [sum_range_succ,ih hk,indicator,ite_eq_left hk,Nat.cast_succ]
      ring
    · have he : n=k+1 := by omega
      subst n
      have hz : (∑ j ∈ range k, indicator (k+1) j) = 0 := by
        apply sum_eq_zero
        intro j hj
        have hj' := mem_range.mp hj
        simp only [indicator,ite_eq_right (by omega : ¬k+1 ≤ j)]
      rw [sum_range_succ,hz]
      simp only [indicator,ite_eq_right (by omega : ¬k+1 ≤ k),Nat.cast_add,Nat.cast_one]
      ring

/-- Actual finite posterior input for each child rank. -/
def input (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω=1)
    (F : ℕ → Setoid Ω) (hF : ∀ t ω v, (F (t+1)).r ω v → (F t).r ω v)
    (N : ℕ → Ω → ℕ) (j : ℕ) : RankTracking.Input Ω where
  weight := w
  weight_nonneg := hw
  weight_total := htotal
  filtration := F
  refines := hF
  posterior t := posterior w (F t) (fun ω => indicator (N t ω) j)
  filtered t := posterior w (F t) (fun ω => indicator (N (t-1) ω) j)
  posterior_range t ω := ⟨posterior_nonneg hw (fun v => (indicator_range (N t v) j).1) (F t) ω,
    posterior_le_one hw (fun v => (indicator_range (N t v) j).2) (F t) ω⟩
  filtered_range t ω := ⟨posterior_nonneg hw (fun v => (indicator_range (N (t-1) v) j).1) (F t) ω,
    posterior_le_one hw (fun v => (indicator_range (N (t-1) v) j).2) (F t) ω⟩
  posterior_measurable t := posterior_measurable w (F t) _
  filtering t a ha := by
    simp only [Nat.add_sub_cancel,RankTracking.average]
    have h := filtering hw (F t) (F (t+1)) (hF t) a (fun ω => indicator (N t ω) j) ha
    simpa only [mul_assoc] using h

end
end UniformKServer.ConditionalRank

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

                                                                      
                                                          
noncomputable section
namespace UniformKServer.RankFunctions

def pstar : ℝ := 1/24
def sstar : ℝ := 5/8
def rank (β p : ℝ) : ℝ :=
  if p ≤ pstar then 1-β*p
  else if p ≤ sstar then
    (sstar-p)^2 * (18/7-(β-3)*(6/49+1152/343*(p-pstar)))
  else 0

def gap (p : ℝ) : ℝ :=
  if p ≤ pstar then p
  else if p ≤ sstar then (sstar-p)^2*(6/49+1152/343*(p-pstar))
  else 0

def allowed (β : ℝ) : Prop := 3 ≤ β ∧ β ≤ 3+1/100

def A (β : ℝ) : ℝ := 18/7-(β-3)*102/49
def B (β : ℝ) : ℝ := (β-3)*1152/343
def h (p : ℝ) : ℝ := max (sstar-p) 0
def middle (β p : ℝ) : ℝ := A β*(h p)^2+B β*(h p)^3

theorem coeff_bounds {β : ℝ} (hβ : allowed β) :
    2 ≤ A β ∧ 0 ≤ B β ∧ B β ≤ 1/20 ∧ A β+B β*(7/12) ≤ 3 ∧
    2*A β*(7/12)+3*B β*(7/12)^2 = β := by
  dsimp [allowed] at hβ
  dsimp [A, B]
  constructor
  · linarith [hβ.2]
  constructor
  · linarith [hβ.1]
  constructor
  · linarith [hβ.2]
  constructor
  · linarith [hβ.1]
  · ring

theorem h_nonneg (p : ℝ) : 0 ≤ h p := le_max_right _ _
theorem h_antitone : Antitone h := by
  intro p q hpq
  apply max_le_max <;> linarith

theorem middle_match (β : ℝ) : middle β pstar = 1-β*pstar := by
  norm_num [middle, h, pstar, sstar, A, B]
  ring

theorem rank_middle {β p : ℝ} (hp : pstar ≤ p) : rank β p = middle β p := by
  by_cases he : p = pstar
  · subst p
    simp only [rank, le_refl, ↓reduceIte, middle_match]
  have hn : ¬p ≤ pstar := fun hh => he (le_antisymm hh hp)
  unfold rank
  rw [ite_eq_right hn]
  by_cases hs : p ≤ sstar
  · rw [ite_eq_left hs]
    unfold middle h
    rw [max_eq_left (sub_nonneg.mpr hs)]
    unfold A B sstar pstar
    ring
  · rw [ite_eq_right hs]
    simp [middle, h, max_eq_right (by linarith : sstar-p ≤ 0)]

theorem middle_antitone {β : ℝ} (hβ : allowed β) : Antitone (middle β) := by
  have hc := coeff_bounds hβ
  intro p q hpq
  unfold middle
  gcongr
  · linarith [hc.1]
  · exact h_nonneg q
  · exact h_antitone hpq
  · exact hc.2.1
  · exact h_nonneg q
  · exact h_antitone hpq

theorem rank_antitone {β : ℝ} (hβ : allowed β) : Antitone (rank β) := by
  intro p q hpq
  by_cases hq : q ≤ pstar
  · have hp : p ≤ pstar := hpq.trans hq
    simp only [rank, ite_eq_left hp, ite_eq_left hq]
    nlinarith [hβ.1]
  · rw [rank_middle (by linarith : pstar ≤ q)]
    by_cases hp : pstar ≤ p
    · rw [rank_middle hp]
      exact middle_antitone hβ hpq
    · calc
        middle β q ≤ middle β pstar := middle_antitone hβ (by linarith)
        _ = 1-β*pstar := middle_match β
        _ ≤ rank β p := by rw [rank, ite_eq_left (by linarith : p ≤ pstar)]; nlinarith [hβ.1]

theorem rank_zero (β : ℝ) : rank β 0 = 1 := by norm_num [rank, pstar]
theorem rank_beyond {β p : ℝ} (hp : sstar ≤ p) : rank β p = 0 := by
  rw [rank_middle (by dsimp [pstar, sstar] at * <;> linarith), middle]
  simp [h, max_eq_right (sub_nonpos.mpr hp)]

theorem rank_nonneg {β p : ℝ} (hβ : allowed β) : 0 ≤ rank β p := by
  by_cases hp : p ≤ pstar
  · rw [rank, ite_eq_left hp]
    have : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left hp (by linarith [hβ.1])
    dsimp [pstar] at this
    nlinarith [hβ.2]
  · rw [rank_middle (by linarith)]
    have hc := coeff_bounds hβ
    have ha : 0 ≤ A β := by linarith [hc.1]
    have hb := hc.2.1
    have hh := h_nonneg p
    unfold middle
    positivity

theorem rank_le_one {β p : ℝ} (hβ : allowed β) (hp : 0 ≤ p) : rank β p ≤ 1 := by
  simpa only [rank_zero] using rank_antitone hβ hp

theorem rank_affine (β p : ℝ) : rank β p = rank 3 p-(β-3)*gap p := by
  unfold rank gap
  split_ifs <;> ring

theorem gap_comparison {β p : ℝ} (hβ : allowed β) (hp : pstar/4 ≤ p) :
    rank β p/96 ≤ gap p ∧ gap p ≤ rank β p := by
  by_cases h₁ : p ≤ pstar
  · simp only [rank, gap, ite_eq_left h₁]
    have hp₀ : 0 ≤ p := by dsimp [pstar] at * <;> linarith
    have hlow : 0 ≤ β*p := mul_nonneg (by linarith [hβ.1]) hp₀
    have hu : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left h₁ (by linarith [hβ.1])
    dsimp [pstar] at hp h₁ hu
    constructor <;> nlinarith [hβ.2]
  · by_cases h₂ : p ≤ sstar
    · simp only [rank, gap, ite_eq_right h₁, ite_eq_left h₂]
      let c : ℝ := 6/49+1152/343*(p-pstar)
      have hc : 6/49 ≤ c ∧ c ≤ 102/49 := by
        dsimp [c, pstar, sstar] at *
        constructor <;> linarith
      have hz : 0 ≤ β-3 ∧ β-3 ≤ 1/100 := by constructor <;> linarith [hβ.1, hβ.2]
      have hprod : 0 ≤ (β-3)*c ∧ (β-3)*c ≤ (1/100)*(102/49) := by
        constructor
        · exact mul_nonneg hz.1 (by linarith [hc.1])
        · exact mul_le_mul hz.2 hc.2 (by linarith [hc.1]) (by norm_num)
      have hlo : (18/7-(β-3)*c)/96 ≤ c := by linarith [hc.1, hprod.1]
      have hhi : c ≤ 18/7-(β-3)*c := by linarith [hc.2, hprod.2]
      constructor
      · have := mul_le_mul_of_nonneg_left hlo (sq_nonneg (sstar-p))
        dsimp [c] at this; nlinarith only [this]
      · exact mul_le_mul_of_nonneg_left hhi (sq_nonneg (sstar-p))
    · simp [rank, gap, h₁, h₂]

end UniformKServer.RankFunctions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankData
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

def sizeRank (p : ℝ) : ℝ := (max (3/4-p) 0)^2 / (3/4)^2

theorem sizeRank_nonneg (p : ℝ) : 0 ≤ sizeRank p := by
  unfold sizeRank
  positivity

theorem sizeRank_one : sizeRank 1 = 0 := by norm_num [sizeRank]

theorem sizeRank_convex : ConvexOn ℝ Set.univ sizeRank := by
  have hlin : ConvexOn ℝ Set.univ (fun p : ℝ => 3/4-p) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  have hm := hlin.sup (convexOn_const 0 convex_univ)
  have hh := (hm.pow (fun p _ => le_max_right (3/4-p) 0) 2).smul
    (show (0 : ℝ) ≤ ((3/4)^2)⁻¹ by norm_num)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa [sizeRank, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.2 hx hy ha hb hab

theorem sizeRank_le_complement {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    sizeRank p ≤ 1-p := by
  by_cases h : p ≤ 3/4
  · rw [sizeRank, max_eq_left (sub_nonneg.mpr h)]
    norm_num
    nlinarith [mul_nonneg hp.1 (show 3/4-p ≥ 0 by linarith)]
  · rw [sizeRank, max_eq_right (by linarith : 3/4-p ≤ 0)]
    norm_num
    exact hp.2

theorem sizeRank_at_cutoff {p : ℝ} (hp : p ≤ sstar) :
    1/36 ≤ sizeRank p := by
  have hp' : p ≤ 5/8 := hp
  have hm : max (3/4-p) 0 = 3/4-p := max_eq_left (by linarith)
  rw [sizeRank, hm]
  norm_num
  nlinarith [sq_nonneg (5/8-p)]

variable {Ω : Type*} [Fintype Ω]
def core (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω) : Bool :=
  decide (RankTracking.absoluteReference I (pstar/8) t ω ≤ pstar/2)

theorem core_small (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (h : core I t ω = true) : I.posterior t ω ≤ 5*pstar/8 := by
  have hr : RankTracking.absoluteReference I (pstar/8) t ω ≤ pstar/2 := by
    simpa only [core, decide_eq_true_eq] using h
  have he := (abs_le.mp (RankTracking.absoluteReference_spec I (pstar/8)
    (by norm_num [pstar]) t ω)).2
  linarith

theorem noncore_large (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (h : core I t ω = false) : 3*pstar/8 < I.posterior t ω := by
  have hr : pstar/2 < RankTracking.absoluteReference I (pstar/8) t ω := by
    simpa only [core, decide_eq_false_iff_not, not_le] using h
  have he := (abs_le.mp (RankTracking.absoluteReference_spec I (pstar/8)
    (by norm_num [pstar]) t ω)).1
  linarith

variable {A : Type*} [Fintype A]
def coreCount (c : A → Bool) : ℝ := ∑ a, if c a then 1 else 0
def flex (c : A → Bool) (β : ℝ) (p : A → ℝ) : ℝ :=
  ∑ a, if c a then 0 else rank β (p a)
def totalRank (β : ℝ) (p : A → ℝ) : ℝ := ∑ a, rank β (p a)
def totalSize (p : A → ℝ) : ℝ := ∑ a, sizeRank (p a)

theorem rank_size_domination {β p : ℝ} (hβ : allowed β) (hp : 0 ≤ p) :
    rank β p ≤ 36 * sizeRank p := by
  by_cases hs : sstar ≤ p
  · rw [rank_beyond hs]
    exact mul_nonneg (by norm_num) (sizeRank_nonneg p)
  · have := sizeRank_at_cutoff (le_of_not_ge hs)
    linarith [rank_le_one hβ hp]

theorem core_flex_domination (c : A → Bool) (β : ℝ) (p : A → ℝ)
    (hβ : allowed β) (hp : ∀ a, 0 ≤ p a)
    (hc : ∀ a, c a = true → p a ≤ pstar) :
    coreCount c + flex c β p ≤ 36 * totalSize p := by
  unfold coreCount flex totalSize
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  cases he : c a with
  | false => simpa [he] using rank_size_domination hβ (hp a)
  | true =>
    have hs : p a ≤ sstar := by
      have := hc a he
      norm_num [pstar, sstar] at *
      linarith
    have := sizeRank_at_cutoff hs
    simp only [↓reduceIte, add_zero]
    linarith

theorem inactive_ranks (c : A → Bool) (β : ℝ) (p : A → ℝ)
    (hc : ∀ a, c a = true → p a ≤ pstar)
    (hm : totalSize p ≤ 10*(10:ℝ)^(-4:ℤ)) :
    coreCount c = 0 ∧ totalRank β p = 0 ∧ flex c β p = 0 := by
  have hlarge (a : A) : sstar < p a := by
    by_contra h
    have hsz := sizeRank_at_cutoff (le_of_not_gt h)
    have hle : sizeRank (p a) ≤ totalSize p :=
      Finset.single_le_sum (fun b _ => sizeRank_nonneg (p b)) (Finset.mem_univ a)
    norm_num at hm
    linarith
  have hzero (a : A) : rank β (p a) = 0 := rank_beyond (hlarge a).le
  have hfalse (a : A) : c a = false := by
    cases he : c a with
    | false => rfl
    | true =>
      have := hc a he
      have := hlarge a
      norm_num [pstar, sstar] at *
      linarith
  simp [coreCount, totalRank, flex, hfalse, hzero]

end UniformKServer.RankData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankSuperadditivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

                                                                            
                                                                                
namespace UniformKServer.RankSuperadditivity
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

structure Input (Ω ι : Type*) [Fintype Ω] [Fintype ι] (k : ℕ) where
  μ : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ μ ω
  total : ∑ ω, μ ω = 1
  N : Ω → ι → ℕ
  bound : ∀ ω, ∑ i, N ω i ≤ k

def countRank (μ : Ω → ℝ) (N : Ω → ℕ) (a : ℕ) : ℝ :=
  ∑ ω, μ ω * if N ω ≤ a then 1 else 0

def rankSum (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range k, f (countRank μ N a)


def hinge (b x : ℝ) : ℝ := max (b-x) 0

def interpolate (c d : ℝ) (L : List (ℝ × ℝ)) (x : ℝ) : ℝ :=
  c + d*x + (L.map (fun p => p.2 * hinge p.1 x)).sum

theorem interpolate_cons (c d : ℝ) (L : List (ℝ × ℝ)) (t w x : ℝ) :
    interpolate c d ((t,w)::L) x = interpolate c d L x + w*hinge t x := by
  simp [interpolate] <;> ring

theorem finite_convex_interpolation_aux (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (l : List ℝ)
    (hs : l.Pairwise (· < ·)) (hmem : ∀ x ∈ l, x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c d : ℝ, ∃ W : List (ℝ × ℝ),
      (∀ p ∈ W, 0 ≤ p.2) ∧ (∀ x ∈ l, f x = interpolate c d W x) ∧
      (∀ a b rest, l = a::b::rest → ∀ x, x ≤ a →
        interpolate c d W x = f a + ((f b-f a)/(b-a))*(x-a)) := by
  induction l with
  | nil =>
      refine ⟨0,0,[],by simp,by simp,?_⟩
      intro a b rest he; cases he
  | cons a l ih =>
      cases l with
      | nil =>
          refine ⟨f a,0,[],by simp,?_,?_⟩
          · simp [interpolate]
          · intro a' b rest he; cases he
      | cons b rest =>
          have hab : a < b := (List.pairwise_cons.mp hs).1 _ (by simp)
          have htail := (List.pairwise_cons.mp hs).2
          have hmTail : ∀ x ∈ b::rest, x ∈ Set.Icc (0 : ℝ) 1 :=
            fun x hx => hmem x (by simp [hx])
          have hid : ((f b-f a)/(b-a))*(b-a) = f b-f a :=
            div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
          cases rest with
          | nil =>
              refine ⟨f a-((f b-f a)/(b-a))*a, (f b-f a)/(b-a), [],by simp,?_,?_⟩
              · intro x hx
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl <;> simp only [interpolate, List.map_nil, List.sum_nil, add_zero]
                · ring
                · nlinarith [hid]
              · intro a' b' rest he x hx
                cases he
                simp only [interpolate, List.map_nil, List.sum_nil, add_zero]
                ring
          | cons b' rest =>
              obtain ⟨c,d,W,hW,heq,hleft⟩ := ih htail hmTail
              have hbb : b < b' := (List.pairwise_cons.mp htail).1 _ (by simp)
              let δ := (f b'-f b)/(b'-b) - (f b-f a)/(b-a)
              have hδ : 0 ≤ δ := sub_nonneg.mpr (hf.slope_mono_adjacent
                (hmem a (by simp)) (hmem b' (by simp)) hab hbb)
              refine ⟨c,d,(b,δ)::W,?_,?_,?_⟩
              · intro p hp
                simp only [List.mem_cons] at hp
                rcases hp with rfl | hp
                · exact hδ
                · exact hW p hp
              · intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · rw [interpolate_cons, hleft b b' rest rfl x hab.le]
                  rw [hinge, max_eq_left (sub_nonneg.mpr hab.le)]
                  dsimp only [δ]
                  nlinarith [hid]
                · have hbx : b ≤ x := by
                    rcases hx with rfl | hx
                    · exact le_rfl
                    · exact ((List.pairwise_cons.mp htail).1 x (by simpa using hx)).le
                  rw [interpolate_cons, ← heq x (by simp only [List.mem_cons]; exact hx)]
                  simp [hinge, max_eq_right (sub_nonpos.mpr hbx)]
              · intro a' b'' rest' hlist x hx
                cases hlist
                rw [interpolate_cons, hleft b b' rest rfl x (hx.trans hab.le)]
                rw [hinge, max_eq_left (sub_nonneg.mpr (hx.trans hab.le))]
                dsimp only [δ]
                nlinarith [hid]

theorem finite_convex_interpolation (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c d : ℝ, ∃ W : List (ℝ × ℝ),
      (∀ p ∈ W, 0 ≤ p.2) ∧ (∀ x ∈ S, f x = interpolate c d W x) := by
  classical
  obtain ⟨c,d,W,hW,heq,_⟩ := finite_convex_interpolation_aux f hf (S.sort (· ≤ ·))
    S.sortedLT_sort.pairwise (by simpa using hS)
  exact ⟨c,d,W,hW,by simpa using heq⟩


theorem countRank_bounds {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ) (a : ℕ) :
    countRank I.μ N a ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun ω _ => mul_nonneg (I.nonneg ω) (by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ ω, I.μ ω := Finset.sum_le_sum fun ω _ => by
        split_ifs <;> simp [I.nonneg ω]
      _ = 1 := I.total

theorem countRank_one {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ) (a : ℕ)
    (hN : ∀ ω, N ω ≤ a) : countRank I.μ N a = 1 := by
  simpa [countRank, hN] using I.total

theorem indicator_count (n m : ℕ) :
    (∑ a ∈ Finset.range n, if m ≤ a then (1 : ℕ) else 0) = n-m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      split_ifs <;> omega

theorem indicator_count_real (n m : ℕ) :
    (∑ a ∈ Finset.range n, if m ≤ a then (1 : ℝ) else 0) = max ((n : ℝ)-(m : ℝ)) 0 := by
  have he : (∑ a ∈ Finset.range n, if m ≤ a then (1 : ℝ) else 0) = ((n-m : ℕ) : ℝ) := by
    exact_mod_cast indicator_count n m
  rw [he]
  by_cases h : m ≤ n
  · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    simp only [Nat.cast_zero]
    exact (max_eq_right (sub_nonpos.mpr (by exact_mod_cast (show n ≤ m by omega)))).symm

def deficit (μ : Ω → ℝ) (N : Ω → ℕ) (n : ℕ) : ℝ :=
  ∑ ω, μ ω * max ((n : ℝ)-(N ω : ℝ)) 0

theorem deficit_eq_sum_rank (μ : Ω → ℝ) (N : Ω → ℕ) (n : ℕ) :
    deficit μ N n = ∑ a ∈ Finset.range n, countRank μ N a := by
  simp only [deficit, ← indicator_count_real, Finset.mul_sum, countRank]
  rw [Finset.sum_comm]

theorem selected_count_lower (A : Finset ℕ) (m : ℕ) :
    max ((A.card : ℝ) - (m : ℝ)) 0 ≤ ∑ a ∈ A, if m ≤ a then (1 : ℝ) else 0 := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := A) (p := fun a => m ≤ a)
  have hle : (A.filter (fun a => ¬ m ≤ a)).card ≤ m := by
    calc
      _ ≤ (Finset.range m).card := Finset.card_le_card fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
        omega
      _ = m := Finset.card_range _
  have hn : A.card ≤ m + (A.filter (fun a => m ≤ a)).card := by omega
  rw [Finset.sum_boole]
  apply max_le
  · have hn' : (A.card : ℝ) ≤ (m : ℝ) + ((A.filter (fun a => m ≤ a)).card : ℝ) := by exact_mod_cast hn
    linarith
  · positivity

theorem selected_rank_lower {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ) (A : Finset ℕ) :
    deficit I.μ N A.card ≤ ∑ a ∈ A, countRank I.μ N a := by
  unfold deficit countRank
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun ω _ => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (selected_count_lower A (N ω)) (I.nonneg ω)

noncomputable def activeRanks (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (b : ℝ) : Finset ℕ :=
  (Finset.range k).filter (fun a => countRank μ N a < b)

theorem hinge_selection (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (b : ℝ) :
    rankSum μ N k (hinge b) = (activeRanks μ N k b).card*b -
      ∑ a ∈ activeRanks μ N k b, countRank μ N a := by
  classical
  have he : ∀ a, hinge b (countRank μ N a) =
      if countRank μ N a < b then b-countRank μ N a else 0 := by
    intro a
    split_ifs with h
    · exact max_eq_left (sub_nonneg.mpr h.le)
    · exact max_eq_right (sub_nonpos.mpr (by linarith))
  simp only [rankSum, he, ← Finset.sum_filter]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, activeRanks]

theorem hinge_dual {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) (b : ℝ) (hb : b ≤ 1) (n : ℕ) :
    (n : ℝ)*b - deficit I.μ N n ≤ rankSum I.μ N k (hinge b) := by
  have hfirst : (n : ℝ)*b - deficit I.μ N n ≤ rankSum I.μ N n (hinge b) := by
    rw [deficit_eq_sum_rank]
    calc
      _ = ∑ a ∈ Finset.range n, (b-countRank I.μ N a) := by simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun a _ => le_max_left _ _
  apply hfirst.trans
  dsimp [rankSum]
  by_cases hnk : n ≤ k
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnk) (fun a _ _ => le_max_right _ _)
  · have hkn : k ≤ n := by omega
    apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono hkn)
    intro a ha hnot
    have hka : k ≤ a := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [countRank_one I N a (fun ω => (hN ω).trans hka)]
    exact max_eq_right (sub_nonpos.mpr hb)

theorem deficit_subadditive {k : ℕ} (I : Input Ω ι k) (n : ι → ℕ) :
    deficit I.μ (fun ω => ∑ i, I.N ω i) (∑ i, n i) ≤
      ∑ i, deficit I.μ (fun ω => I.N ω i) (n i) := by
  simp only [deficit]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (I.nonneg ω)
  apply max_le
  · simp only [Nat.cast_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => le_max_left _ _
  · exact Finset.sum_nonneg fun i _ => le_max_right _ _

theorem hinge_superadditivity {k : ℕ} (I : Input Ω ι k) (b : ℝ) (hb : b ≤ 1) :
    (∑ i, rankSum I.μ (fun ω => I.N ω i) k (hinge b)) ≤
      rankSum I.μ (fun ω => ∑ i, I.N ω i) k (hinge b) := by
  let n : ι → ℕ := fun i => (activeRanks I.μ (fun ω => I.N ω i) k b).card
  have hchild (i : ι) : rankSum I.μ (fun ω => I.N ω i) k (hinge b) ≤
      (n i : ℝ)*b - deficit I.μ (fun ω => I.N ω i) (n i) := by
    rw [hinge_selection]
    exact sub_le_sub_left (selected_rank_lower I _ _) _
  calc
    _ ≤ ∑ i, ((n i : ℝ)*b - deficit I.μ (fun ω => I.N ω i) (n i)) :=
      Finset.sum_le_sum fun i _ => hchild i
    _ = (∑ i, n i : ℕ)*b - ∑ i, deficit I.μ (fun ω => I.N ω i) (n i) := by
      simp [Finset.sum_sub_distrib, Finset.sum_mul]
    _ ≤ (∑ i, n i : ℕ)*b - deficit I.μ (fun ω => ∑ i, I.N ω i) (∑ i, n i) :=
      sub_le_sub_left (deficit_subadditive I n) _
    _ ≤ _ := hinge_dual I _ I.bound b hb _


def mean (μ : Ω → ℝ) (N : Ω → ℕ) : ℝ := ∑ ω, μ ω * (N ω : ℝ)
def risk (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  rankSum μ N k f - (k : ℝ)*f 1

theorem sum_rank_eq {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) :
    (∑ a ∈ Finset.range k, countRank I.μ N a) = (k : ℝ) - mean I.μ N := by
  rw [← deficit_eq_sum_rank]
  simp only [deficit, max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr (hN _))),
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, I.total, one_mul, mean]

theorem component_bound {k : ℕ} (I : Input Ω ι k) (i : ι) (ω : Ω) : I.N ω i ≤ k := by
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (I.bound ω)

theorem mean_parent {k : ℕ} (I : Input Ω ι k) :
    mean I.μ (fun ω => ∑ i, I.N ω i) = ∑ i, mean I.μ (fun ω => I.N ω i) := by
  simp only [mean, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem risk_hinge_large {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) (b : ℝ) (hb : 1 ≤ b) : risk I.μ N k (hinge b) = mean I.μ N := by
  have hp (a : ℕ) : hinge b (countRank I.μ N a) = b-countRank I.μ N a :=
    max_eq_left (sub_nonneg.mpr ((countRank_bounds I N a).2.trans hb))
  simp only [risk, rankSum]
  simp_rw [hp]
  simp only [hinge, max_eq_left (sub_nonneg.mpr hb), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [sum_rank_eq I N hN]
  ring

theorem risk_hinge_superadditive {k : ℕ} (I : Input Ω ι k) (b : ℝ) :
    (∑ i, risk I.μ (fun ω => I.N ω i) k (hinge b)) ≤
      risk I.μ (fun ω => ∑ i, I.N ω i) k (hinge b) := by
  rcases le_total b 1 with hb | hb
  · simpa only [risk, hinge, max_eq_right (sub_nonpos.mpr hb), mul_zero, sub_zero]
      using hinge_superadditivity I b hb
  · simp_rw [risk_hinge_large I _ (component_bound I _) b hb]
    rw [risk_hinge_large I _ I.bound b hb, mean_parent]

theorem risk_congr {k : ℕ} (μ : Ω → ℝ) (N : Ω → ℕ) {f g : ℝ → ℝ}
    (h : ∀ a < k, f (countRank μ N a) = g (countRank μ N a)) (h1 : f 1 = g 1) :
    risk μ N k f = risk μ N k g := by
  unfold risk rankSum
  rw [h1]
  congr 1
  exact Finset.sum_congr rfl fun a ha => h a (Finset.mem_range.mp ha)

theorem risk_add (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (f g : ℝ → ℝ) :
    risk μ N k (fun x => f x+g x) = risk μ N k f + risk μ N k g := by
  simp only [risk, rankSum, Finset.sum_add_distrib]
  ring

theorem risk_smul (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (w : ℝ) (f : ℝ → ℝ) :
    risk μ N k (fun x => w*f x) = w*risk μ N k f := by
  simp only [risk, rankSum, ← Finset.mul_sum]
  ring

theorem risk_affine {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) (c d : ℝ) :
    risk I.μ N k (fun x => c+d*x) = -d*mean I.μ N := by
  simp only [risk, rankSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_rank_eq I N hN]
  ring

theorem interpolation_superadditive {k : ℕ} (I : Input Ω ι k)
    (c d : ℝ) (W : List (ℝ × ℝ)) (hW : ∀ p ∈ W, 0 ≤ p.2) :
    (∑ i, risk I.μ (fun ω => I.N ω i) k (interpolate c d W)) ≤
      risk I.μ (fun ω => ∑ i, I.N ω i) k (interpolate c d W) := by
  induction W with
  | nil =>
      have he : interpolate c d [] = (fun x => c+d*x) := by funext x; simp [interpolate]
      rw [he]
      simp_rw [risk_affine I _ (component_bound I _) c d]
      rw [risk_affine I _ I.bound c d, mean_parent, Finset.mul_sum]
  | cons p W ih =>
      have hp : 0 ≤ p.2 := hW p (by simp)
      have ht : ∀ q ∈ W, 0 ≤ q.2 := fun q hq => hW q (by simp [hq])
      have he : interpolate c d (p::W) = (fun x => interpolate c d W x + p.2*hinge p.1 x) := by
        funext x; exact interpolate_cons c d W p.1 p.2 x
      simp_rw [he, risk_add, risk_smul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (ih ht) (mul_le_mul_of_nonneg_left (risk_hinge_superadditive I p.1) hp)

theorem rank_superadditivity {k : ℕ} (I : Input Ω ι k) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (h1 : f 1 = 0) :
    (∑ i, rankSum I.μ (fun ω => I.N ω i) k f) ≤
      rankSum I.μ (fun ω => ∑ i, I.N ω i) k f := by
  classical
  let N : Option ι → Ω → ℕ := fun j ω => match j with
    | none => ∑ i, I.N ω i
    | some i => I.N ω i
  let S : Finset ℝ := insert 1 ((Finset.univ : Finset (Option ι × Fin k)).image
    (fun q => countRank I.μ (N q.1) q.2))
  have hS : ∀ x ∈ S, x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨q,rfl⟩
    · exact ⟨by norm_num, le_rfl⟩
    · exact countRank_bounds I _ _
  obtain ⟨c,d,W,hW,heq⟩ := finite_convex_interpolation f hf S hS
  have hEq (j : Option ι) : risk I.μ (N j) k f = risk I.μ (N j) k (interpolate c d W) := by
    apply risk_congr I.μ (N j)
    · intro a ha
      apply heq
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(j,⟨a,ha⟩),Finset.mem_univ _,rfl⟩
    · exact heq 1 (Finset.mem_insert_self _ _)
  have hineq := interpolation_superadditive I c d W hW
  have hchild (i : ι) := hEq (some i)
  have hpar := hEq none
  dsimp only [N] at hchild hpar
  simp_rw [← hchild] at hineq
  rw [← hpar] at hineq
  simpa only [risk, h1, mul_zero, sub_zero] using hineq

end UniformKServer.RankSuperadditivity

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConditionalRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The source rank and size inequalities for the actual finite conditional
 law, with normalization proved on every positive-ConditionalLaw.mass history.  Null histories
 are not silently assigned a normalized law. -/
noncomputable section
namespace UniformKServer.ConditionalRanks
open Finset ConditionalLaw RankData
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def rankProbability (w : Ω → ℝ) (F : Setoid Ω) (N : Ω → ℕ) (ω : Ω) (j : ℕ) : ℝ :=
  posterior w F (fun v => ConditionalRank.indicator (N v) j) ω

theorem normalized_kernel (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) : ∑ v, kernel w F ω v = 1 := by
  rw [kernel_sum,div_self hm]

def countInput (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ) (hN : ∀ v, ∑ i, N v i ≤ k) :
    RankSuperadditivity.Input Ω ι k where
  μ := kernel w F ω
  nonneg := kernel_nonneg hw F ω
  total := normalized_kernel w F ω hm
  N := N
  bound := hN

theorem conditional_convex_superadditivity (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F : Setoid Ω) (ω : Ω) (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ)
    (hN : ∀ v, ∑ i, N v i ≤ k) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f) (h1 : f 1=0) :
    (∑ i, ∑ j : Fin k, f (rankProbability w F (fun v => N v i) ω j)) ≤
      ∑ j : Fin k, f (rankProbability w F (fun v => ∑ i, N v i) ω j) := by
  have h := RankSuperadditivity.rank_superadditivity (countInput w hw F ω hm N k hN) f hf h1
  simp only [RankSuperadditivity.rankSum,countInput] at h
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

theorem size_superadditivity (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F : Setoid Ω) (ω : Ω) (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ)
    (hN : ∀ v, ∑ i, N v i ≤ k) :
    (∑ i, totalSize (fun j : Fin k => rankProbability w F (fun v => N v i) ω j)) ≤
      totalSize (fun j : Fin k => rankProbability w F (fun v => ∑ i, N v i) ω j) := by
  exact conditional_convex_superadditivity w hw F ω hm N k hN sizeRank
    (sizeRank_convex.subset (Set.subset_univ _) (convex_Icc _ _)) sizeRank_one

theorem sum_complements (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ℕ) (k : ℕ) (hN : ∀ v, N v ≤ k) :
    (∑ j : Fin k, (1-rankProbability w F N ω j)) = posterior w F (fun v => (N v:ℝ)) ω := by
  have hn := normalized_kernel w F ω hm
  calc
    _ = ∑ j ∈ range k, ∑ v, kernel w F ω v*(1-ConditionalRank.indicator (N v) j) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro j _
      simp only [rankProbability,posterior,mul_sub,mul_one,sum_sub_distrib,hn]
    _ = ∑ v, kernel w F ω v*(∑ j ∈ range k, (1-ConditionalRank.indicator (N v) j)) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      unfold posterior
      apply sum_congr rfl
      intro v _
      rw [sum_sub_distrib,ConditionalRank.indicator_sum (hN v)]
      simp

theorem size_le_mean (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ℕ) (k : ℕ) (hN : ∀ v, N v ≤ k) :
    totalSize (fun j : Fin k => rankProbability w F N ω j) ≤
      posterior w F (fun v => (N v:ℝ)) ω := by
  rw [←sum_complements w F ω hm N k hN]
  apply sum_le_sum
  intro j _
  exact sizeRank_le_complement ⟨posterior_nonneg hw
    (fun v => (ConditionalRank.indicator_range (N v) j).1) F ω,
    posterior_le_one hw (fun v => (ConditionalRank.indicator_range (N v) j).2) F ω⟩

end UniformKServer.ConditionalRanks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

                                                                               
                                                                            
namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]


/-! Local optimality construction. -/
def ballMass (r a : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ p, if dist x p ≤ a*r then μ p else 0


end
end UniformKServer.PilotCompact
end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
def localSlopeConstant (σ L : ℝ) : ℝ :=
  (L+1024/σ)*(514+8/σ)+1024*(5+L)/σ^2

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCredits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- The constant in companion Lemma pilot-drift. -/
def driftConstant (σ γ δ L : ℝ) (p : ℕ) : ℝ :=
  2056/γ + 8224/σ + 2*(L+1026/σ)*p/(δ*Real.log 2) +
    2*localSlopeConstant σ L*((p:ℝ)/Real.log 2+2*γ)

end
end UniformKServer.PilotCompact



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.PilotEdits

section
open PilotCompact
attribute [local instance] Classical.propDecidable

/-- A fixed admissible pilot template, independent of the input law and horizon. -/
structure Template where
  sigma : ℝ
  R : ℝ
  gamma : ℝ
  delta : ℝ
  L : ℝ
  shift : ℕ
  sigma_pos : 0 < sigma
  sigma_le_one : sigma ≤ 1
  R_large : 256 ≤ R
  L_nonneg : 0 ≤ L
  gamma_pos : 0 < gamma
  gamma_sigma : gamma ≤ sigma/64
  gamma_L : gamma ≤ 1/(1+L)
  delta_pos : 0 < delta
  delta_small : delta ≤ 1/4112
  shift_large : 100*R ≤ gamma*(2:ℝ)^shift

def rate (T : Template) : ℝ := driftConstant T.sigma T.gamma T.delta T.L T.shift

variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

/-- Finite form of the posterior identity of the source. `filtered t` is the
new pre-move posterior at step t+1; `post t` is the previous post-move measure.
The test-function identity is over every old measurable function, not merely
on an event selected later by the edit rule. -/
structure Flow (X Ω : Type*) [Fintype X] [Fintype Ω] (k : ℕ) where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_total : ∑ ω, weight ω = 1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω ω', (filtration (t+1)).r ω ω' → (filtration t).r ω ω'
  post : ℕ → Ω → X → ℝ
  filtered : ℕ → Ω → X → ℝ
  mover : ℕ → Ω → X → ℝ
  request : ℕ → Ω → X
  post_nonneg : ∀ t ω y, 0 ≤ post t ω y
  post_total : ∀ t ω, ∑ y, post t ω y = k
  filtered_nonneg : ∀ t ω y, 0 ≤ filtered t ω y
  filtered_total : ∀ t ω, ∑ y, filtered t ω y = k
  mover_nonneg : ∀ t ω y, 0 ≤ mover t ω y
  mover_total : ∀ t ω, ∑ y, mover t ω y = 1
  mover_le : ∀ t ω y, mover t ω y ≤ filtered t ω y
  update : ∀ t ω y, post (t+1) ω y = filtered t ω y - mover t ω y +
    if y = request t ω then 1 else 0
  post_measurable : ∀ t ω ω', (filtration t).r ω ω' → post t ω = post t ω'
  filtering : ∀ t (b : Ω → ℝ), (∀ ω ω', (filtration t).r ω ω' → b ω = b ω') →
    ∀ y, (∑ ω, weight ω*b ω*(filtered t ω y-post t ω y)) = 0

end

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HiddenFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The true-metric posterior flow is derived from literal labeled one-server
trajectories. Observing further partition randomness may refine the filtration;
no filtering identity on a later selected event is assumed. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

structure Data (X Ω : Type*) [Fintype Ω] (k : ℕ) where
  weight : Ω → ℝ
  positive : ∀ ω, 0 < weight ω
  total : ∑ ω, weight ω=1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  position : ℕ → Ω → Fin k → X
  chosen : ℕ → Ω → Fin k
  request : ℕ → Ω → X
  update : ∀ t ω a, position (t+1) ω a=if a=chosen t ω then request t ω else position t ω a
  request_measurable : ∀ t ω v, (filtration (t+1)).r ω v → request t ω=request t v

def atom (x y : X) : ℝ := if x=y then 1 else 0

def counts (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  ∑ a : Fin k, atom (D.position t ω a) y

def moverAtom (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  atom (D.position t ω (D.chosen t ω)) y

def current (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  posterior D.weight (D.filtration t) (fun v => counts D t v y) ω

def filtered (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  posterior D.weight (D.filtration (t+1)) (fun v => counts D t v y) ω

def mover (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  posterior D.weight (D.filtration (t+1)) (fun v => moverAtom D t v y) ω

omit [Fintype X] in
theorem atom_nonneg (x y : X) : 0 ≤ atom x y := by unfold atom; split_ifs <;> norm_num

theorem atom_total (x : X) : (∑ y, atom x y)=1 := by simp [atom]

omit [Fintype X] in
theorem counts_nonneg (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : 0 ≤ counts D t ω y :=
  sum_nonneg fun _ _ => atom_nonneg _ _

theorem counts_total (D : Data X Ω k) (t : ℕ) (ω : Ω) : (∑ y, counts D t ω y)=k := by
  unfold counts
  rw [sum_comm]
  simp only [atom_total,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

omit [Fintype X] in
theorem mover_le_count (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) :
    moverAtom D t ω y ≤ counts D t ω y :=
  single_le_sum (fun a _ => atom_nonneg (D.position t ω a) y) (mem_univ (D.chosen t ω))

omit [Fintype X] in
theorem counts_update (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) :
    counts D (t+1) ω y=counts D t ω y-moverAtom D t ω y+atom (D.request t ω) y := by
  have he (a : Fin k) : atom (D.position (t+1) ω a) y=atom (D.position t ω a) y+
      if a=D.chosen t ω then atom (D.request t ω) y-atom (D.position t ω a) y else 0 := by
    rw [D.update]
    split_ifs <;> ring
  simp only [counts,he,sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true, if_true,moverAtom]
  ring

omit [Fintype X] in
theorem normalization (D : Data X Ω k) (t : ℕ) (ω : Ω) :
    (∑ v, kernel D.weight (D.filtration t) ω v)=1 := by
  apply ConditionalRanks.normalized_kernel
  exact ne_of_gt (lt_of_lt_of_le (D.positive ω)
    (weight_le_mass (fun v => (D.positive v).le) _ _))

omit [Fintype X] in
theorem posterior_local (D : Data X Ω k) (t : ℕ) (ω : Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ v, (D.filtration t).r ω v → f v=c) :
    posterior D.weight (D.filtration t) f ω=c := by
  unfold posterior
  calc
    _ = ∑ v, kernel D.weight (D.filtration t) ω v*c := by
      apply sum_congr rfl
      intro v _
      by_cases h : (D.filtration t).r ω v
      · rw [hf v h]
      · simp only [kernel,ite_eq_right h,zero_mul]
    _ = _ := by rw [←sum_mul,normalization,one_mul]

theorem posterior_total (D : Data X Ω k) (t : ℕ) (ω : Ω) (f : Ω → X → ℝ) (c : ℝ)
    (hf : ∀ v, ∑ y, f v y=c) :
    (∑ y, posterior D.weight (D.filtration t) (fun v => f v y) ω)=c := by
  unfold posterior
  rw [sum_comm]
  simp only [←mul_sum,hf,←sum_mul,normalization,one_mul]

omit [Fintype X] in
theorem posterior_mono (D : Data X Ω k) (t : ℕ) (ω : Ω) (f g : Ω → ℝ)
    (hfg : ∀ v, f v ≤ g v) :
    posterior D.weight (D.filtration t) f ω ≤ posterior D.weight (D.filtration t) g ω :=
  sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hfg v) (kernel_nonneg (fun v => (D.positive v).le) _ _ _)

def flow (D : Data X Ω k) : PilotEdits.Flow X Ω k where
  weight := D.weight
  weight_nonneg := fun ω => (D.positive ω).le
  weight_total := D.total
  filtration := D.filtration
  refines := D.refines
  post := current D
  filtered := filtered D
  mover := mover D
  request := D.request
  post_nonneg := fun t ω y => posterior_nonneg (fun v => (D.positive v).le) (fun v => counts_nonneg D t v y) _ _
  post_total := fun t ω => posterior_total D t ω (fun v y => counts D t v y) k (counts_total D t)
  filtered_nonneg := fun t ω y => posterior_nonneg (fun v => (D.positive v).le) (fun v => counts_nonneg D t v y) _ _
  filtered_total := fun t ω => posterior_total D (t+1) ω (fun v y => counts D t v y) k (counts_total D t)
  mover_nonneg := fun t ω y => posterior_nonneg (fun v => (D.positive v).le) (fun v => atom_nonneg _ _) _ _
  mover_total := fun t ω => posterior_total D (t+1) ω (fun v y => moverAtom D t v y) 1 (fun v => atom_total _)
  mover_le := fun t ω y => posterior_mono D (t+1) ω _ _ (fun v => mover_le_count D t v y)
  update := by
    intro t ω y
    have hd := posterior_local D (t+1) ω (fun v => atom (D.request t v) y) (atom (D.request t ω) y)
      (fun v hv => by rw [D.request_measurable t ω v hv])
    unfold current filtered mover posterior at *
    simp only [counts_update,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
    rw [hd]
    simp only [atom,eq_comm]
  post_measurable := by
    intro t ω v h
    funext y
    exact posterior_measurable _ _ _ ω v h
  filtering := by
    intro t b hb y
    exact ConditionalLaw.filtering (fun v => (D.positive v).le) (D.filtration t) (D.filtration (t+1))
      (D.refines t) b (fun v => counts D t v y) hb

end UniformKServer.HiddenFlow

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HiddenCausality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! True-prefix measurability and service mass for literal hidden trajectories. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

omit [Fintype X] in
theorem refines_le (D : Data X Ω k) (s t : ℕ) (hst : s≤t) (ω v : Ω)
    (h : (D.filtration t).r ω v) : (D.filtration s).r ω v := by
  induction t,hst using Nat.le_induction with
  | base => exact h
  | succ t hst ih => exact ih (D.refines t ω v h)

theorem current_measurable (D : Data X Ω k) (s t : ℕ) (hst : s≤t) (ω v : Ω)
    (h : (D.filtration t).r ω v) : current D s ω=current D s v := by
  exact (flow D).post_measurable s ω v (refines_le D s t hst ω v h)

omit [Fintype X] in
theorem request_past (D : Data X Ω k) (s t : ℕ) (hst : s<t) (ω v : Ω)
    (h : (D.filtration t).r ω v) : D.request s ω=D.request s v := by
  exact D.request_measurable s ω v (refines_le D (s+1) t (by omega) ω v h)

theorem serving_mass (D : Data X Ω k) (t : ℕ) (ω : Ω) : 1 ≤ current D (t+1) ω (D.request t ω) := by
  have hu := (flow D).update t ω (D.request t ω)
  have hl := (flow D).mover_le t ω (D.request t ω)
  change current D (t+1) ω (D.request t ω)=filtered D t ω (D.request t ω)-mover D t ω (D.request t ω)+(if D.request t ω=D.request t ω then 1 else 0) at hu
  rw [ite_eq_left rfl] at hu
  change mover D t ω (D.request t ω)≤filtered D t ω (D.request t ω) at hl
  linarith

end UniformKServer.HiddenFlow

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FirstStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Precedence across heavy balls, chronological tiers, and singleton fallback.
A qualifying prefix covers the request, so fallback does not contribute to the
short-edge separation estimate. -/
noncomputable section
namespace UniformKServer.FirstStructure
open scoped Classical
variable {I J : Type*}

def first : List I → (I → Option J) → Option J
  | [], _ => none
  | i::is, f => (f i).or (first is f)

def indicator (x y : J) : ℝ := if x=y then 0 else 1

theorem indicator_bounds (x y : J) : indicator x y ∈ Set.Icc (0:ℝ) 1 := by
  unfold indicator
  split_ifs <;> constructor <;> norm_num

theorem indicator_map (f : I → J) (a b : I) : indicator (f a) (f b)≤ indicator a b := by
  by_cases he : a=b
  · subst b; simp [indicator]
  · simpa only [indicator,ite_eq_right he] using (indicator_bounds (f a) (f b)).2

end UniformKServer.FirstStructure

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Fixed-slot implementation of disjoint heavy balls, including the literal
finite-metric intersection test for label reuse. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ : Type*} [MetricSpace X] [Fintype Λ]

structure State (X Λ : Type*) [MetricSpace X] (r : ℝ) where
  present : Finset Λ
  center : Λ → X
  radius : Λ → ℝ
  radius_bounds : ∀ l ∈ present, radius l ∈ Set.Icc (16*r) (20*r)
  separated : ∀ a ∈ present, ∀ b ∈ present, a ≠ b → 100*r < dist (center a) (center b)

variable {r : ℝ}

def covers (S : State X Λ r) (l : Λ) (p : X) : Prop :=
  l ∈ S.present ∧ dist (S.center l) p ≤ S.radius l

omit [Fintype Λ] in
theorem unique (S : State X Λ r) (hr : 0 ≤ r) (a b : Λ) (p : X)
    (ha : covers S a p) (hb : covers S b p) : a=b := by
  by_contra hn
  have hh := S.separated a ha.1 b hb.1 hn
  have ht := dist_triangle (S.center a) p (S.center b)
  rw [dist_comm p (S.center b)] at ht
  linarith [(S.radius_bounds a ha.1).2,(S.radius_bounds b hb.1).2,ha.2,hb.2]

def key (S : State X Λ r) (p : X) : Option Λ :=
  if h : ∃ l, covers S l p then some (Classical.choose h) else none

theorem key_some (S : State X Λ r) (hr : 0 ≤ r) (p : X) (l : Λ) :
    key S p=some l ↔ covers S l p := by
  unfold key
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · intro he; rw [←he]; exact Classical.choose_spec h
    · intro hc; exact unique S hr _ _ p (Classical.choose_spec h) hc
  · constructor
    · intro h; cases h
    · intro hc; exact (h ⟨l,hc⟩).elim

def intersects (S : State X Λ r) (x : X) (R : ℝ) (l : Λ) : Prop :=
  ∃ p, covers S l p ∧ dist x p ≤ R

omit [Fintype Λ] in
theorem intersect_distance (S : State X Λ r) (x : X) (R : ℝ) (l : Λ)
    (hR : R ≤ 20*r) (h : intersects S x R l) : dist x (S.center l) ≤ 40*r := by
  obtain ⟨p,hp,hd⟩ := h
  have ht := dist_triangle x p (S.center l)
  rw [dist_comm p (S.center l)] at ht
  linarith [(S.radius_bounds l hp.1).2,hp.2]

omit [Fintype Λ] in
theorem intersect_unique (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ≤ 20*r) (a b : Λ) (ha : intersects S x R a) (hb : intersects S x R b) : a=b := by
  by_contra hn
  have hh := S.separated a (Classical.choose_spec ha).1.1 b (Classical.choose_spec hb).1.1 hn
  have ha' := intersect_distance S x R a hR ha
  have hb' := intersect_distance S x R b hR hb
  have ht := dist_triangle (S.center a) x (S.center b)
  rw [dist_comm (S.center a) x] at ht
  linarith

def reused (S : State X Λ r) (x : X) (R : ℝ) : Option Λ :=
  if h : ∃ l, intersects S x R l then some (Classical.choose h) else none

def chosen (S : State X Λ r) (x : X) (R : ℝ) (fresh : Λ) : Λ :=
  (reused S x R).getD fresh

theorem chosen_of_intersects (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ≤ 20*r) (fresh l : Λ) (hl : intersects S x R l) : chosen S x R fresh=l := by
  unfold chosen reused
  rw [dite_eq_left ⟨l,hl⟩]
  exact intersect_unique S hr x R hR _ l (Classical.choose_spec _) hl

theorem chosen_cases (S : State X Λ r) (x : X) (R : ℝ) (fresh : Λ) :
    intersects S x R (chosen S x R fresh) ∨
      (chosen S x R fresh=fresh ∧ ¬∃ l, intersects S x R l) := by
  unfold chosen reused
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h)
  · exact Or.inr ⟨rfl,h⟩

def survivors (S : State X Λ r) (x : X) : Finset Λ :=
  S.present.filter (fun l => 100*r < dist x (S.center l))

theorem chosen_not_survivor (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ≤ 20*r) (fresh : Λ) (hf : fresh ∉ S.present) : chosen S x R fresh ∉ survivors S x := by
  intro hc
  obtain ⟨hp,hd⟩ := mem_filter.mp hc
  rcases chosen_cases S x R fresh with hi | ⟨he,_⟩
  · have := intersect_distance S x R _ hR hi
    linarith
  · exact hf (he ▸ hp)

def insert (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) : State X Λ r where
  present := Insert.insert (chosen S x R fresh) (survivors S x)
  center := Function.update S.center (chosen S x R fresh) x
  radius := Function.update S.radius (chosen S x R fresh) R
  radius_bounds := by
    intro l hl
    rcases mem_insert.mp hl with he | hs
    · subst l
      simpa only [Function.update_self] using hR
    · have hn : l ≠ chosen S x R fresh := fun he => chosen_not_survivor S hr x R hR.2 fresh hf (he ▸ hs)
      rw [Function.update_of_ne hn]
      exact S.radius_bounds l (mem_filter.mp hs).1
  separated := by
    intro a ha b hb hn
    rcases mem_insert.mp ha with he | ha
    · subst a
      rcases mem_insert.mp hb with he | hb
      · exact (hn he.symm).elim
      · have hbne : b ≠ chosen S x R fresh := Ne.symm hn
        rw [Function.update_self,Function.update_of_ne hbne]
        exact (mem_filter.mp hb).2
    · have hane : a ≠ chosen S x R fresh := fun he => chosen_not_survivor S hr x R hR.2 fresh hf (he ▸ ha)
      rw [Function.update_of_ne hane]
      rcases mem_insert.mp hb with he | hb
      · subst b
        rw [Function.update_self,dist_comm]
        exact (mem_filter.mp ha).2
      · have hbne : b ≠ chosen S x R fresh := fun he => chosen_not_survivor S hr x R hR.2 fresh hf (he ▸ hb)
        rw [Function.update_of_ne hbne]
        exact S.separated a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hn

theorem new_covers (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (p : X)
    (hp : dist x p ≤ R) : covers (insert S hr x R hR fresh hf) (chosen S x R fresh) p := by
  constructor
  · exact mem_insert_self _ _
  · simpa only [insert,Function.update_self] using hp

omit [Fintype Λ] in
theorem center_injective (S : State X Λ r) (hr : 0 ≤ r) :
    Set.InjOn S.center S.present := by
  intro a ha b hb he
  by_contra hn
  have := S.separated a ha b hb hn
  rw [he,dist_self] at this
  linarith

omit [Fintype Λ] in
theorem card_present [Fintype X] (S : State X Λ r) (hr : 0 ≤ r) :
    S.present.card ≤ Fintype.card X := by
  have h := card_image_of_injOn (center_injective S hr)
  rw [←h]
  exact card_le_card (subset_univ _)

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.HeavyPilot

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- The clipped ramp on [3,4]. -/
def ramp (v : ℝ) : ℝ := max 0 (min 1 (v-3))

/-- The source's ramp of distance to the center set, equal to one for the empty set. -/
def parameter (r : ℝ) (H : Finset X) (p : X) : ℝ :=
  (insert 1 (H.image (fun c => ramp (dist p c/r)))).min' (by simp)

/-- The heavy update deletes all centers at distance at most 100r, then inserts x. -/
def updateCenters (r : ℝ) (H : Finset X) (x : X) : Finset X :=
  insert x (H.filter fun c => 100*r < dist x c)

def annulusMass (r : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ p, if 3*r < dist p x ∧ dist p x ≤ 120*r then μ p else 0

end

open PilotCompact

end UniformKServer.HeavyPilot

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavySchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The literal deterministic heavy-center recursion of companion §07.
The update decision depends only on the request, posterior, and old centers,
not on any radius, lifetime, allocation, or rounding variable. -/
noncomputable section
namespace UniformKServer.HeavySchedule
open Finset
open scoped Classical
variable {X : Type*} [MetricSpace X]

def trigger (r : ℝ) (h : Prop) (H : Finset X) (x : X) : Prop :=
  h ∧ ∀ c ∈ H, 8*r < dist x c

def step (r : ℝ) (h : Prop) (H : Finset X) (x : X) : Finset X :=
  if trigger r h H x then HeavyPilot.updateCenters r H x else H

def centers (r : ℝ) (h : ℕ → Prop) (x : ℕ → X) : ℕ → Finset X
  | 0 => ∅
  | t+1 => step r (h t) (centers r h x t) (x t)

theorem coverage (r : ℝ) (hr : 0 ≤ r) (h : Prop) (hh : h) (H : Finset X) (x : X) :
    ∃ c ∈ step r h H x, dist x c ≤ 8*r := by
  by_cases hu : trigger r h H x
  · refine ⟨x,?_,?_⟩
    · simp only [step,ite_eq_left hu,HeavyPilot.updateCenters,mem_insert_self]
    · simp only [dist_self] <;> positivity
  · have hn : ¬∀ c ∈ H, 8*r < dist x c := fun hf => hu ⟨hh,hf⟩
    push Not at hn
    obtain ⟨c,hc,hd⟩ := hn
    exact ⟨c,by simpa only [step,ite_eq_right hu] using hc,hd⟩

theorem centers_coverage (r : ℝ) (hr : 0 ≤ r) (h : ℕ → Prop) (x : ℕ → X)
    (t : ℕ) (hh : h t) : ∃ c ∈ centers r h x (t+1), dist (x t) c ≤ 8*r :=
  coverage r hr (h t) hh _ _

end UniformKServer.HeavySchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRecordGeometry
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

def centers (S : State X Λ r) : Finset X := S.present.image S.center

variable [Fintype Λ]

theorem centers_insert (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) :
    centers (insert S hr x R hR fresh hf)=HeavyPilot.updateCenters r (centers S) x := by
  have hn := chosen_not_survivor S hr x R hR.2 fresh hf
  ext p
  simp only [centers,insert,mem_image,mem_insert,HeavyPilot.updateCenters,mem_filter]
  constructor
  · rintro ⟨l,hl,he⟩
    rcases hl with rfl | hl
    · left; simpa only [Function.update_self] using he.symm
    · have hlne : l ≠ chosen S x R fresh := fun he => hn (he ▸ hl)
      rw [Function.update_of_ne hlne] at he
      exact Or.inr ⟨⟨l,(mem_filter.mp hl).1,he⟩,he ▸ (mem_filter.mp hl).2⟩
  · rintro (rfl | ⟨⟨l,hl,he⟩,hd⟩)
    · exact ⟨chosen S p R fresh,Or.inl rfl,Function.update_self _ _ _⟩
    · have hs : l ∈ survivors S x := mem_filter.mpr ⟨hl,he ▸ hd⟩
      have hlne : l ≠ chosen S x R fresh := fun he => hn (he ▸ hs)
      exact ⟨l,Or.inr hs,by rwa [Function.update_of_ne hlne]⟩

theorem common_region_reused (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (p : X) (l : Λ) (hold : covers S l p) (hnew : dist x p ≤ R) :
    key (insert S hr x R hR fresh hf) p=key S p := by
  have he := chosen_of_intersects S hr x R hR.2 fresh l ⟨p,hold,hnew⟩
  rw [(key_some S hr p l).mpr hold]
  apply (key_some _ hr p l).mpr
  rw [←he]
  exact new_covers S hr x R hR fresh hf p hnew

variable [Fintype X]

theorem fresh_exists (S T : State X Λ r) (hr : 0 ≤ r)
    (hΛ : 2*Fintype.card X < Fintype.card Λ) : ∃ l : Λ, l ∉ S.present ∪ T.present := by
  have hc : (S.present ∪ T.present).card < Fintype.card Λ := by
    have hs := card_present S hr
    have ht := card_present T hr
    have hu := card_union_le S.present T.present
    omega
  by_contra h
  push Not at h
  have he : S.present ∪ T.present=univ := eq_univ_of_forall h
  rw [he,card_univ] at hc
  omega

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! A horizon-independent fixed-slot heavy process with the source's one-step
cooldown. Its centers equal the radius-independent deterministic schedule. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

def empty (a : X) : State X Λ r where
  present := ∅
  center := fun _ => a
  radius := fun _ => 0
  radius_bounds := by simp
  separated := by simp

def fresh (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ) : Λ :=
  Classical.choose (fresh_exists S T hr hΛ)

theorem fresh_absent (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ) :
    fresh S T hr hΛ ∉ S.present ∧ fresh S T hr hΛ ∉ T.present := by
  have h := Classical.choose_spec (fresh_exists S T hr hΛ)
  simpa only [fresh,mem_union,not_or] using h

def step (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R ∈ Set.Icc (16*r) (20*r)) : State X Λ r :=
  if HeavySchedule.trigger r h (centers S) x then
    HeavyRecords.insert S hr x R hR (fresh S T hr hΛ) (fresh_absent S T hr hΛ).1
  else S

theorem centers_step (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R ∈ Set.Icc (16*r) (20*r)) :
    centers (step S T hr hΛ h x R hR)=HeavySchedule.step r h (centers S) x := by
  unfold step HeavySchedule.step
  split_ifs
  · exact centers_insert S hr x R hR _ _
  · rfl

def runPair (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r)) :
    ℕ → State X Λ r × State X Λ r
  | 0 => (empty a,empty a)
  | t+1 => let ST := runPair a hr hΛ h x R hR t
           (ST.2,step ST.2 ST.1 hr hΛ (h t) (x t) (R t) (hR t))

def run (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) : State X Λ r := (runPair a hr hΛ h x R hR t).2

theorem run_centers (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) : centers (run a hr hΛ h x R hR t)=HeavySchedule.centers r h x t := by
  induction t with
  | zero => simp only [run,runPair,empty,centers,image_empty,HeavySchedule.centers]
  | succ t ih =>
    change centers (step _ _ hr hΛ (h t) (x t) (R t) (hR t))=_
    rw [centers_step]
    change HeavySchedule.step r (h t) (centers (run a hr hΛ h x R hR t)) (x t)=_
    rw [ih]
    rfl

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.FiniteProbability

section
attribute [local instance] Classical.propDecidable

structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def Law.expect (P : Law Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.weight ω*f ω

theorem Law.expect_nonneg (P : Law Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ P.expect f := Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hf ω)

theorem Law.expect_mono (P : Law Ω) (f g : Ω → ℝ) (hfg : ∀ ω, f ω ≤ g ω) :
    P.expect f ≤ P.expect g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (P.nonneg ω)

@[simp] theorem Law.expect_const (P : Law Ω) (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect,←Finset.sum_mul,P.total]

theorem Law.expect_add (P : Law Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω+g ω) = P.expect f+P.expect g := by
  simp [expect,mul_add,Finset.sum_add_distrib]

theorem Law.expect_sub (P : Law Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω-g ω) = P.expect f-P.expect g := by
  simp [expect,mul_sub,Finset.sum_sub_distrib]

theorem Law.expect_mul (P : Law Ω) (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun ω => c*f ω) = c*P.expect f := by
  simp only [expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

def Law.prod (P : Law Ω) (Q : Law Γ) : Law (Ω × Γ) where
  weight ω := P.weight ω.1*Q.weight ω.2
  nonneg ω := mul_nonneg (P.nonneg ω.1) (Q.nonneg ω.2)
  total := by simp [Fintype.sum_prod_type,←Finset.mul_sum,Q.total,P.total]

theorem Law.expect_prod (P : Law Ω) (Q : Law Γ) (f : Ω → Γ → ℝ) :
    (P.prod Q).expect (fun ω => f ω.1 ω.2) = P.expect (fun ω => Q.expect (f ω)) := by
  simp only [expect,prod,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

variable {I : Type*} [Fintype I]

def bernoulli (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

theorem bernoulli_total (p : ℝ) : ∑ b : Bool, bernoulli p b = 1 := by
  simp [bernoulli]

def coins (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) : Law (I → Bool) where
  weight ω := ∏ i, bernoulli (p i) (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => by
    unfold bernoulli
    split_ifs
    · exact (hp i).1
    · linarith [(hp i).2]
  total := by
    classical
    rw [←Fintype.prod_sum]
    simp only [bernoulli_total,Finset.prod_const_one]

theorem coins_expect_coordinate (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (i : I) (f : Bool → ℝ) :
    (coins p hp).expect (fun ω => f (ω i)) = (1-p i)*f false+p i*f true := by
  classical
  have hpoint (ω : I → Bool) : (∏ j, bernoulli (p j) (ω j))*f (ω i) =
      ∏ j, bernoulli (p j) (ω j)*(if j=i then f (ω j) else 1) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    symm
    simpa only [ite_true, if_true] using (Finset.prod_eq_single (s := Finset.univ)
      (f := fun j : I => if j=i then f (ω j) else 1) i
      (by intro j _ hj; simp [hj]) (by simp))
  unfold Law.expect coins
  simp only [hpoint]
  rw [←Fintype.prod_sum (fun (j : I) (b : Bool) =>
    bernoulli (p j) b*(if j=i then f b else 1))]
  have hexcept (j : I) (hj : j ≠ i) :
      (∑ b : Bool, bernoulli (p j) b*(if j=i then f b else 1)) = 1 := by
    simpa [hj] using bernoulli_total (p j)
  rw [Finset.prod_eq_single i (fun j _ hj => hexcept j hj) (by simp)]
  simp [bernoulli,add_comm]

@[simp] theorem coins_true (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (i : I) :
    (coins p hp).expect (fun ω => if ω i then 1 else 0) = p i := by
  rw [coins_expect_coordinate p hp i (fun b => if b then 1 else 0)]
  simp

@[simp] theorem coins_false (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (i : I) :
    (coins p hp).expect (fun ω => if ω i then 0 else 1) = 1-p i := by
  rw [coins_expect_coordinate p hp i (fun b => if b then 0 else 1)]
  simp

end
variable {Ω I : Type*} [Fintype Ω]

theorem Law.expect_congr (P : Law Ω) (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) :
    P.expect f = P.expect g := by
  unfold expect
  exact Finset.sum_congr rfl (fun ω _ => by rw [h ω])

theorem Law.expect_finset_sum (P : Law Ω) (S : Finset I) (f : I → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ S, f i ω) = ∑ i ∈ S, P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

end UniformKServer.FiniteProbability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FinitePiLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

noncomputable section
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]

def Law.pi (P : ∀ i, Law (A i)) : Law (∀ i, A i) where
  weight a := ∏ i, (P i).weight (a i)
  nonneg a := prod_nonneg fun i _ => (P i).nonneg _
  total := by rw [←Fintype.prod_sum]; simp only [Law.total,prod_const_one]

theorem Law.expect_pi_product (P : ∀ i, Law (A i)) (f : ∀ i, A i → ℝ) :
    (Law.pi P).expect (fun a => ∏ i, f i (a i)) = ∏ i, (P i).expect (f i) := by
  simp only [Law.expect,Law.pi,←prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a*f i a)).symm

theorem Law.expect_pi_coordinate (P : ∀ i, Law (A i)) (i : I) (f : A i → ℝ) :
    (Law.pi P).expect (fun a => f (a i)) = (P i).expect f := by
  let g : ∀ j, A j → ℝ := fun j a => if h : j=i then f (h ▸ a) else 1
  have hg (a : ∀ j, A j) : (∏ j, g j (a j))=f (a i) := by
    rw [prod_eq_single i]
    · simp only [g,dite_eq_left rfl]
    · intro j _ hj
      simp only [g,dite_eq_right hj]
    · simp
  have he := Law.expect_pi_product P g
  simp only [hg] at he
  rw [he,prod_eq_single i]
  · simp [g]
  · intro j _ hj
    simp only [g,dite_eq_right hj,Law.expect_const]
  · simp

theorem Law.expect_pi_separate (P : ∀ i, Law (A i)) (i : I)
    (f : A i → ℝ) (g : (∀ i, A i) → ℝ)
    (hg : ∀ a b, (∀ j, j ≠ i → a j=b j) → g a=g b) :
    (Law.pi P).expect (fun a => f (a i)*g a) =
      (P i).expect f*(Law.pi P).expect g := by
  by_cases he : Nonempty (∀ j, A j)
  · let : DecidableEq {j : I // j ≠ i} := fun a b => Classical.propDecidable (a=b)
    let a₀ : ∀ j, A j := Classical.choice he
    let e := Equiv.piSplitAt i A
    have hweight (x : A i × (∀ j : {j // j ≠ i}, A j.val)) :
        (Law.pi P).weight (e.symm x) = (P i).weight x.1 *
          ∏ j : {j // j ≠ i}, (P j.val).weight (x.2 j) := by
      change (∏ j, (P j).weight (e.symm x j))=_
      rw [←mul_prod_erase _ _ (mem_univ i)]
      have h0 : e.symm x i=x.1 := by simp [e,Equiv.piSplitAt]
      rw [h0]
      congr 1
      rw [Finset.prod_subtype (p:=fun j : I => j ≠ i) (univ.erase i) (by simp [eq_comm])]
      apply prod_congr rfl
      intro j _
      simp [e,Equiv.piSplitAt,j.property]
    have hg' (x : A i × (∀ j : {j // j ≠ i}, A j.val)) :
        g (e.symm x)=g (e.symm (a₀ i,x.2)) := by
      apply hg
      intro j hj
      simp [e,Equiv.piSplitAt,hj]
    have hfun (a : A i) (b : ∀ j : {j // j ≠ i}, A j.val) :
        (e.symm (a,b)) i=a := by simp [e,Equiv.piSplitAt]
    let Q := Law.pi (fun j : {j // j ≠ i} => P j.val)
    have hleft : (Law.pi P).expect (fun a => f (a i)*g a)=
        (P i).expect f * Q.expect (fun b => g (e.symm (a₀ i,b))) := by
      unfold Law.expect
      rw [←e.symm.sum_comp,Fintype.sum_prod_type]
      simp only [hweight,hfun,hg']
      simp only [Q,Law.pi]
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      ring
    have hright : (Law.pi P).expect g=Q.expect (fun b => g (e.symm (a₀ i,b))) := by
      unfold Law.expect
      rw [←e.symm.sum_comp,Fintype.sum_prod_type]
      simp only [hweight,hg',mul_assoc,←mul_sum,←sum_mul,(P i).total,one_mul]
      rfl
    rw [hleft,hright]
  · have hzero : (∑ a : ∀ j, A j, (Law.pi P).weight a)=0 := by
      apply sum_eq_zero
      intro a _
      exact (he ⟨a⟩).elim
    have := (Law.pi P).total
    linarith

end UniformKServer.FiniteProbability

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section
namespace UniformKServer.FiniteThreshold
noncomputable section
open MeasureTheory FiniteProbability
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

def collapse {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : A → Ω) (hf : ∀ ω, MeasurableSet (f ⁻¹' {ω})) : Law Ω where
  weight ω := μ.real (f ⁻¹' {ω})
  nonneg _ := measureReal_nonneg
  total := by
    have h := sum_measureReal_preimage_singleton (μ := μ) Finset.univ (fun ω _ => hf ω)
    simpa using h

def unitInterval : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance unitInterval_probability : IsProbabilityMeasure unitInterval where
  measure_univ := by simp [unitInterval,Real.volume_Ioc]

def normalized (u : ℝ) : ℝ := if u ∈ Set.Ioc (0:ℝ) 1 then u else 1

theorem normalized_mem (u : ℝ) : normalized u ∈ Set.Ioc (0:ℝ) 1 := by
  unfold normalized
  split_ifs with hu
  · exact hu
  · exact ⟨zero_lt_one,le_rfl⟩

theorem normalized_measurable : Measurable normalized :=
  Measurable.ite measurableSet_Ioc measurable_id measurable_const

variable {X : Type*} [Fintype X]

def threshold (p : X → ℝ) (u : ℝ) : X → Bool := fun x => decide (u ≤ p x)

abbrev Signature (p : X → ℝ) := {ω : X → Bool // ∃ u ∈ Set.Ioc (0:ℝ) 1, ω = threshold p u}

def sample (p : X → ℝ) (u : ℝ) : Signature p :=
  ⟨threshold p (normalized u),normalized u,normalized_mem u,rfl⟩

theorem sample_measurable (p : X → ℝ) (ω : Signature p) :
    MeasurableSet (sample p ⁻¹' {ω}) := by
  have heq : sample p ⁻¹' {ω} = ⋂ x : X, {u : ℝ | threshold p (normalized u) x = ω.val x} := by
    ext u
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · intro h x
      exact congrFun (congrArg Subtype.val h) x
    · intro h
      exact Subtype.ext (funext h)
  rw [heq]
  apply MeasurableSet.iInter
  intro x
  cases hω : ω.val x
  · simp only [threshold,decide_eq_false_iff_not]
    exact (measurableSet_le normalized_measurable (measurable_const : Measurable (fun _ : ℝ => p x))).compl
  · simpa only [threshold,decide_eq_true_eq] using
      (measurableSet_le normalized_measurable measurable_const)

def experiment (p : X → ℝ) : Law (Signature p) :=
  collapse unitInterval (sample p) (sample_measurable p)
theorem collapse_event {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : A → Ω) (hf : ∀ ω, MeasurableSet (f ⁻¹' {ω})) (P : Ω → Prop) :
    (collapse μ f hf).expect (fun ω => if P ω then 1 else 0) = μ.real (f ⁻¹' {ω | P ω}) := by
  classical
  unfold Law.expect collapse
  simp only [mul_ite,mul_one,mul_zero,←Finset.sum_filter]
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ.filter P) (fun ω _ => hf ω)
  simpa using h

theorem threshold_event (p : X → ℝ) (P : Signature p → Prop) :
    (experiment p).expect (fun ω => if P ω then 1 else 0) =
      unitInterval.real {u | P (sample p u)} := by
  exact collapse_event unitInterval (sample p) (sample_measurable p) P

theorem threshold_bool_event (p : X → ℝ) (P : Signature p → Bool) :
    (experiment p).expect (fun ω => if P ω then 1 else 0) =
      unitInterval.real {u | P (sample p u) = true} := by
  have h := threshold_event p (fun ω => P ω = true)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply (experiment p).expect_congr
  intro ω
  by_cases hω : P ω = true <;> simp [hω]

theorem interval_threshold (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) :
    unitInterval.real {u | normalized u ≤ a} = a := by
  rw [unitInterval,measureReal_restrict_apply (measurableSet_le normalized_measurable measurable_const)]
  have hset : {u | normalized u ≤ a} ∩ Set.Ioc (0:ℝ) 1 = Set.Ioc 0 a := by
    ext u
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_Ioc]
    constructor
    · rintro ⟨hu,hu0,hu1⟩
      rw [normalized,ite_eq_left ⟨hu0,hu1⟩] at hu
      exact ⟨hu0,hu⟩
    · rintro ⟨hu0,hua⟩
      have hu1 := hua.trans ha.2
      exact ⟨by rw [normalized,ite_eq_left ⟨hu0,hu1⟩]; exact hua,hu0,hu1⟩
  rw [hset,Real.volume_real_Ioc,sub_zero,max_eq_left ha.1]
/-- Finite collapse of one shared uniform threshold. These laws realize the
same nested coverage events as a single truncated-exponential radius. -/
theorem threshold_coordinate (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0:ℝ) 1) (x : X) :
    (experiment p).expect (fun ω => if ω.val x then 1 else 0) = p x := by
  rw [threshold_bool_event p (fun ω => ω.val x)]
  simpa only [sample,threshold,decide_eq_true_eq] using interval_threshold (p x) (hp x)

theorem threshold_hit (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0:ℝ) 1) (x y : X) :
    (experiment p).expect (fun ω => if ω.val x || ω.val y then 1 else 0) = max (p x) (p y) := by
  rw [threshold_bool_event p (fun ω => ω.val x || ω.val y)]
  have hset : {u | ((sample p u).val x || (sample p u).val y) = true} =
      {u | normalized u ≤ max (p x) (p y)} := by
    ext u
    simp only [Set.mem_ofPred_eq,sample,threshold,Bool.or_eq_true,decide_eq_true_eq,le_max_iff]
  rw [hset]
  exact interval_threshold _ ⟨(hp x).1.trans (le_max_left _ _),max_le (hp x).2 (hp y).2⟩

theorem threshold_separation (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0:ℝ) 1) (x y : X) :
    (experiment p).expect (fun ω => if ω.val x != ω.val y then 1 else 0) = |p x-p y| := by
  have hid (ω : Signature p) : (if ω.val x != ω.val y then (1:ℝ) else 0) =
      2*(if ω.val x || ω.val y then 1 else 0)-(if ω.val x then 1 else 0)-(if ω.val y then 1 else 0) := by
    cases ω.val x <;> cases ω.val y <;> norm_num
  rw [(experiment p).expect_congr _ _ hid,(experiment p).expect_sub,(experiment p).expect_sub,
    (experiment p).expect_mul,threshold_hit p hp x y,threshold_coordinate p hp x,threshold_coordinate p hp y]
  rcases le_total (p x) (p y) with h|h
  · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring
end
end UniformKServer.FiniteThreshold

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! A finite exact realization of the uniform heavy-ball radius.  The same
finite signature records membership for every possible center. Thus selecting
a center by the input-driven schedule does not alter the radius distribution. -/
noncomputable section
namespace UniformKServer.HeavyRadius
open FiniteProbability
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def probability (r : ℝ) (a : X × X) : ℝ := max 0 (min 1 ((20*r-dist a.1 a.2)/(4*r)))

abbrev Sample (r : ℝ) := FiniteThreshold.Signature (@probability X _ r)

def law (r : ℝ) : Law (Sample (X:=X) r) := FiniteThreshold.experiment (probability r : X × X → ℝ)

def scalar (r : ℝ) (ω : Sample (X:=X) r) : ℝ := Classical.choose ω.property

omit [Fintype X] in
theorem scalar_mem (r : ℝ) (ω : Sample (X:=X) r) : scalar r ω ∈ Set.Ioc (0:ℝ) 1 :=
  (Classical.choose_spec ω.property).1

def radius (r : ℝ) (ω : Sample (X:=X) r) : ℝ := 20*r-4*r*scalar r ω

omit [Fintype X] in
theorem radius_bounds (r : ℝ) (hr : 0 ≤ r) (ω : Sample (X:=X) r) :
    radius r ω ∈ Set.Icc (16*r) (20*r) := by
  have h := scalar_mem r ω
  dsimp [radius]
  constructor <;> nlinarith [h.1,h.2]

end UniformKServer.HeavyRadius

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyFiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! The exact finite uniform-radius law for the literal heavy process. The
slot pool is fixed before the horizon; only the independent tape is truncated
at the finite horizon under analysis. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords FiniteProbability
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

local instance pairDecEq_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance finDecEq_rc42fe4_1 (N : ℕ) : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
def radiusStream (r : ℝ) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r) (t : ℕ) : ℝ :=
  if h : t<N then HeavyRadius.radius r (ω ⟨t,h⟩) else 16*r

omit [Fintype X] in
theorem radiusStream_bounds (r : ℝ) (hr : 0 ≤ r) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r)
    (t : ℕ) : radiusStream r N ω t ∈ Set.Icc (16*r) (20*r) := by
  unfold radiusStream
  split_ifs
  · exact HeavyRadius.radius_bounds r hr _
  · constructor <;> linarith

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Every time slice of the same finite product tape, not a new resampling of
old balls. The slot universe remains independent of the analysis horizon. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords FiniteProbability
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

local instance tapePairDecEq_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance tapeFinDecEq_rc42fe4_1 (N : ℕ) : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
def slice (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r) (t : ℕ) : State X Λ r :=
  run a hr hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr N ω) t

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FirstHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section
namespace UniformKServer.FirstHit
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable

/-- A finite independently sampled chronological family. Each coordinate can
include a collapsed continuous radius law, so no count of random bits is
claimed at this existence-only stage. -/
structure Entry where
  Sample : Type
  finite : Fintype Sample
  law : @Law Sample finite
  hit : Sample → Bool
  separates : Sample → Bool
  separates_hit : ∀ x, separates x = true → hit x = true

attribute [instance] Entry.finite

def Samples : List Entry → Type
  | [] => Unit
  | E::es => E.Sample × Samples es

instance samplesFinite : (es : List Entry) → Fintype (Samples es)
  | [] => inferInstanceAs (Fintype Unit)
  | E::es => @instFintypeProd _ _ E.finite (samplesFinite es)

def experiment : (es : List Entry) → Law (Samples es)
  | [] => ⟨fun _ => 1,by intro _; norm_num,by change (∑ _ : Unit, (1:ℝ)) = 1; simp⟩
  | E::es => E.law.prod (experiment es)

def firstSeparates : (es : List Entry) → Samples es → Bool
  | [], _ => false
  | E::es, ω => if E.hit ω.1 then E.separates ω.1 else firstSeparates es ω.2

def hitProbability (E : Entry) : ℝ := E.law.expect (fun ω => if E.hit ω then 1 else 0)
def separationProbability (E : Entry) : ℝ := E.law.expect (fun ω => if E.separates ω then 1 else 0)
theorem hitProbability_bounds (E : Entry) : hitProbability E ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact E.law.expect_nonneg _ (fun _ => by split_ifs <;> norm_num)
  · have := E.law.expect_mono (fun ω => if E.hit ω then 1 else 0) (fun _ => 1)
      (fun _ => by split_ifs <;> norm_num)
    simpa only [hitProbability,Law.expect_const] using this

theorem recurrence (E : Entry) (es : List Entry) :
    (experiment (E::es)).expect (fun ω => if firstSeparates (E::es) ω then 1 else 0) =
      separationProbability E+(1-hitProbability E)*
        (experiment es).expect (fun ω => if firstSeparates es ω then 1 else 0) := by
  let z := (experiment es).expect (fun ω => if firstSeparates es ω then 1 else 0)
  let f : E.Sample → Samples es → ℝ := fun ω η =>
    if (if E.hit ω then E.separates ω else firstSeparates es η) then 1 else 0
  change (E.law.prod (experiment es)).expect (fun ω => f ω.1 ω.2) = _
  rw [E.law.expect_prod (experiment es) f]
  have hinner (ω : E.Sample) :
      (experiment es).expect (f ω) =
      (if E.separates ω then 1 else 0)+(1-(if E.hit ω then 1 else 0))*z := by
    unfold f
    by_cases hh : E.hit ω = true
    · simp only [ite_eq_left hh,sub_self,zero_mul,add_zero,Law.expect_const]
    · have hs : E.separates ω ≠ true := fun h => hh (E.separates_hit ω h)
      simp only [ite_eq_right hh,ite_eq_right hs,sub_zero,one_mul,zero_add]
      rfl
  rw [E.law.expect_congr _ _ hinner,E.law.expect_add]
  have hid : E.law.expect (fun ω => (1-(if E.hit ω then 1 else 0))*z) =
      (1-hitProbability E)*z := by
    rw [show (fun ω => (1-(if E.hit ω then 1 else 0))*z) =
        (fun ω => z*(1-(if E.hit ω then 1 else 0))) by funext; ring]
    rw [E.law.expect_mul,E.law.expect_sub,E.law.expect_const]
    unfold hitProbability
    ring
  rw [hid]
  rfl
end
end UniformKServer.FirstHit

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PiFirstHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Chronological first-hit experiments are the actual marginal of one fixed
independent tape; no product-law identity is supplied as a hypothesis. -/
noncomputable section
namespace UniformKServer.FirstHit
open FiniteProbability
open scoped Classical
variable {I : Type*} [Fintype I]

def firstPi (E : I → Entry) : List I → (∀ i, (E i).Sample) → Bool
  | [], _ => false
  | i::is, ω => if (E i).hit (ω i) then (E i).separates (ω i) else firstPi E is ω

omit [Fintype I] in
theorem firstPi_dep (E : I → Entry) (is : List I) (ω η : ∀ i, (E i).Sample)
    (he : ∀ i ∈ is, ω i=η i) : firstPi E is ω=firstPi E is η := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [firstPi,he i (List.mem_cons_self ..),ih (fun j hj => he j (List.mem_cons_of_mem _ hj))]

theorem pi_recurrence (E : I → Entry) (i : I) (is : List I) (hi : i ∉ is) :
    (Law.pi (fun i => (E i).law)).expect (fun ω => if firstPi E (i::is) ω then 1 else 0)=
    separationProbability (E i)+(1-hitProbability (E i))*
      (Law.pi (fun i => (E i).law)).expect (fun ω => if firstPi E is ω then 1 else 0) := by
  have hid (ω : ∀ j, (E j).Sample) :
      (if firstPi E (i::is) ω then (1:ℝ) else 0)=
      (if (E i).separates (ω i) then 1 else 0)+
        (1-(if (E i).hit (ω i) then 1 else 0))*(if firstPi E is ω then 1 else 0) := by
    by_cases hh : (E i).hit (ω i)=true
    · simp only [firstPi,ite_eq_left hh,sub_self,zero_mul,add_zero]
    · have hs : (E i).separates (ω i) ≠ true := fun hs => hh ((E i).separates_hit _ hs)
      simp only [firstPi,ite_eq_right hh,ite_eq_right hs,sub_zero,one_mul,zero_add]
  rw [Law.expect_congr _ _ _ hid,Law.expect_add,
    Law.expect_pi_coordinate (fun j => (E j).law) i (fun a => if (E i).separates a then 1 else 0)]
  rw [Law.expect_pi_separate (fun j => (E j).law) i
    (fun a => 1-(if (E i).hit a then 1 else 0))
    (fun ω => if firstPi E is ω then 1 else 0)]
  · simp only [Law.expect_sub,Law.expect_const,hitProbability,separationProbability]
  · intro ω η he
    have hh : firstPi E is ω=firstPi E is η := by
      apply firstPi_dep
      intro j hj
      exact he j (fun h => hi (h ▸ hj))
    rw [hh]

theorem pi_expect_first (E : I → Entry) (is : List I) (hn : is.Nodup) :
    (Law.pi (fun i => (E i).law)).expect (fun ω => if firstPi E is ω then 1 else 0)=
    (experiment (is.map E)).expect (fun ω => if firstSeparates _ ω then 1 else 0) := by
  induction is with
  | nil =>
    change (Law.pi (fun i => (E i).law)).expect (fun _ => (0:ℝ))=(experiment []).expect (fun _ => 0)
    rw [Law.expect_const,Law.expect_const]
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    rw [pi_recurrence E i is hi,List.map_cons,recurrence,ih hn]

end UniformKServer.FirstHit

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ChronologicalRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ChronologicalRoster

section
variable {I X : Type*} [LinearOrder I] [MetricSpace X]

/-- Ages count subsequent chronological insertions, whether or not those
entries have retired. Equal physical centers remain distinct records. -/
def age (S : Finset I) (c : I → X) (r : ℝ) (i : I) : ℕ :=
  (S.filter fun j => i < j ∧ dist (c i) (c j) ≤ 20*r).card

def young (S : Finset I) (c : I → X) (r : ℝ) (A : ℕ) : Finset I :=
  S.filter fun i => age S c r i < A

end

section
open Finset
variable {I X : Type*} [LinearOrder I] [MetricSpace X]

theorem local_age_count (S T : Finset I) (c : I → X) (r : ℝ) (A : ℕ)
    (hTS : T ⊆ S) (hy : ∀ i ∈ T, age S c r i < A)
    (hd : ∀ i ∈ T, ∀ j ∈ T, dist (c i) (c j) ≤ 20*r) : T.card ≤ A
 := by
  by_cases hT : T.Nonempty
  · let m := T.min' hT
    have hm : m ∈ T := Finset.min'_mem T hT
    have hsub : T.erase m ⊆ S.filter (fun j => m < j ∧ dist (c m) (c j) ≤ 20*r) := by
      intro j hj
      have hjT := (Finset.mem_erase.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨hTS hjT,?_,hd m hm j hjT⟩
      exact lt_of_le_of_ne (Finset.min'_le T j hjT) (Ne.symm (Finset.mem_erase.mp hj).1)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hm] at hcard
    have ha := hy m hm
    change _ < A at ha
    unfold age at ha
    omega
  · have : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [this]

end
variable {I X : Type*} [LinearOrder I] [MetricSpace X]

theorem age_insert (S : Finset I) (c : I → X) (r : ℝ) (n i : I)
    (hn : ∀ j ∈ S, j < n) (hi : i ∈ S) :
    age (insert n S) c r i = age S c r i + if dist (c i) (c n) ≤ 20*r then 1 else 0 := by
  have hin := hn i hi
  have hnot : n ∉ S := fun h => (lt_irrefl n) (hn n h)
  unfold age
  rw [Finset.filter_insert]
  by_cases hd : dist (c i) (c n) ≤ 20*r
  · rw [ite_eq_left ⟨hin,hd⟩,ite_eq_left hd,Finset.card_insert_of_notMem]
    exact fun h => hnot (Finset.mem_filter.mp h).1
  · simp [hd]

theorem new_age_zero (S : Finset I) (c : I → X) (r : ℝ) (n : I)
    (hn : ∀ j ∈ S, j < n) : age (insert n S) c r n = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj,hnj,_⟩ := Finset.mem_filter.mp hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact (lt_irrefl _) hnj
  · exact (not_lt_of_gt (hn j hj)) hnj

end UniformKServer.ChronologicalRoster

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FirstHitSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Required finite-law partition bridge: only potentially hitting roster
records are charged in the truncated-radius correction. All other present
records remain in the actual chronological product experiment. -/
namespace UniformKServer.FirstHit
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable

theorem separationProbability_nonneg (E : Entry) : 0 ≤ separationProbability E :=
  E.law.expect_nonneg _ (fun _ => by split_ifs <;> norm_num)

theorem separationProbability_le_hit (E : Entry) :
    separationProbability E ≤ hitProbability E :=
  by
    apply E.law.expect_mono
    intro ω
    by_cases hs : E.separates ω = true
    · simp only [ite_eq_left hs, ite_eq_left (E.separates_hit ω hs)]
      exact le_rfl
    · simp only [ite_eq_right hs]
      split_ifs <;> norm_num

/-- A heterogeneous indexed formulation avoids identifying equal physical
centers or equal entry laws; repeated centers are counted as separate records. -/
theorem first_hit_support {I : Type*} (is : List I) (entry : I → Entry)
    (P : I → Prop) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hlocal : ∀ i ∈ is, P i →
      separationProbability (entry i) ≤ α*(hitProbability (entry i)+ε))
    (hmiss : ∀ i ∈ is, ¬ P i → hitProbability (entry i) = 0) :
    (experiment (is.map entry)).expect (fun ω => if firstSeparates _ ω then 1 else 0) ≤
      α*(1+((is.filter (fun i => decide (P i))).length:ℝ)*ε) := by
  induction is with
  | nil =>
    have he : (experiment []).expect (fun ω => if firstSeparates [] ω then (1:ℝ) else 0) = 0 :=
      Law.expect_const _ 0
    change (experiment []).expect (fun ω => if firstSeparates [] ω then (1:ℝ) else 0) ≤ _
    rw [he,List.filter_nil,List.length_nil,Nat.cast_zero,zero_mul,add_zero,mul_one]
    exact hα
  | cons i is ih =>
    change (experiment (entry i :: is.map entry)).expect
      (fun ω => if firstSeparates (entry i :: is.map entry) ω then 1 else 0) ≤ _
    have hre := recurrence (entry i) (is.map entry)
    rw [hre]
    obtain ⟨hp0,hp1⟩ := hitProbability_bounds (entry i)
    have hi := ih (fun j hj => hlocal j (List.mem_cons_of_mem _ hj))
      (fun j hj => hmiss j (List.mem_cons_of_mem _ hj))
    by_cases hp : P i
    · have hs := hlocal i (List.mem_cons_self ..) hp
      have hm := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hp1)
      simp only [List.filter_cons,decide_eq_true_eq,ite_eq_left hp,List.length_cons,
        Nat.cast_add,Nat.cast_one]
      calc
        _ ≤ α*(hitProbability (entry i)+ε)+(1-hitProbability (entry i))*
            (α*(1+((is.filter (fun i => decide (P i))).length:ℝ)*ε)) := add_le_add hs hm
        _ = α*(1+(((is.filter (fun i => decide (P i))).length:ℝ)+1)*ε)-
            α*hitProbability (entry i)*((is.filter (fun i => decide (P i))).length:ℝ)*ε := by ring
        _ ≤ _ := sub_le_self _ (by positivity)
    · have hh := hmiss i (List.mem_cons_self ..) hp
      have hs : separationProbability (entry i) = 0 :=
        le_antisymm (by rw [←hh]; exact separationProbability_le_hit _) (separationProbability_nonneg _)
      simpa only [List.filter_cons,decide_eq_true_eq,ite_eq_right hp,hh,hs,sub_zero,
        one_mul,zero_add] using hi

end
end UniformKServer.FirstHit

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RadiusTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section
namespace UniformKServer.RadiusTail
noncomputable section

def clipped (a : ℝ) : ℝ := min (max (a-1) 0) 1

/-- Survival function of the manuscript's truncated exponential radius,
normalized by r. It includes support endpoints with their exact values. -/
def tail (lam a : ℝ) : ℝ :=
  (Real.exp (-lam*clipped a)-Real.exp (-lam))/(1-Real.exp (-lam))
theorem clipped_bounds (a : ℝ) : clipped a ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨le_min (le_max_right _ _) zero_le_one,min_le_right _ _⟩

theorem clipped_mono : Monotone clipped := by
  intro a b hab
  exact min_le_min (max_le_max (sub_le_sub_right hab 1) le_rfl) le_rfl

theorem clipped_difference (a b : ℝ) (hab : a ≤ b) : clipped b-clipped a ≤ b-a := by
  unfold clipped
  rcases le_total (a-1) 0 with ha|ha
  · rw [max_eq_right ha,min_eq_left zero_le_one]
    rcases le_total (b-1) 0 with hb|hb
    · rw [max_eq_right hb,min_eq_left zero_le_one]
      linarith
    · rw [max_eq_left hb]
      linarith [min_le_left (b-1) (1:ℝ)]
  · rw [max_eq_left ha,max_eq_left (by linarith : 0 ≤ b-1)]
    rcases le_total (a-1) 1 with ha1|ha1
    · rw [min_eq_left ha1]
      linarith [min_le_left (b-1) (1:ℝ)]
    · rw [min_eq_right ha1,min_eq_right (by linarith : 1 ≤ b-1)]
      linarith

theorem denominator_pos (lam : ℝ) (hlam : 0 < lam) : 0 < 1-Real.exp (-lam) := by
  have : Real.exp (-lam) < 1 := (Real.exp_lt_one_iff).mpr (by linarith)
  linarith

theorem tail_bounds (lam a : ℝ) (hlam : 0 < lam) : tail lam a ∈ Set.Icc (0:ℝ) 1 := by
  have hc := clipped_bounds a
  have hlo : Real.exp (-lam) ≤ Real.exp (-lam*clipped a) := Real.exp_le_exp.mpr (by nlinarith [hc.2])
  have hhi : Real.exp (-lam*clipped a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hc.1])
  unfold tail
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (denominator_pos lam hlam).le
  · apply (div_le_one (denominator_pos lam hlam)).mpr
    linarith

theorem tail_antitone (lam : ℝ) (hlam : 0 < lam) : Antitone (tail lam) := by
  intro a b hab
  unfold tail
  apply div_le_div_of_nonneg_right _ (denominator_pos lam hlam).le
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have := clipped_mono hab
  nlinarith

theorem tail_eq_one (lam a : ℝ) (hlam : 0 < lam) (ha : a ≤ 1) : tail lam a = 1 := by
  have hc : clipped a = 0 := by
    unfold clipped
    rw [max_eq_right (by linarith),min_eq_left zero_le_one]
  unfold tail
  rw [hc,mul_zero,Real.exp_zero]
  exact div_self (ne_of_gt (denominator_pos lam hlam))

theorem tail_eq_zero (lam a : ℝ) (ha : 2 ≤ a) : tail lam a = 0 := by
  have hc : clipped a = 1 := by
    unfold clipped
    rw [max_eq_left (by linarith),min_eq_right (by linarith)]
  simp only [tail,hc,mul_one,sub_self,zero_div]

theorem tail_offset (lam a : ℝ) (hlam : 0 < lam) :
    tail lam a+1/(Real.exp lam-1) = Real.exp (-lam*clipped a)/(1-Real.exp (-lam)) := by
  have hx : Real.exp lam-1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam))
  have hd := ne_of_gt (denominator_pos lam hlam)
  have he : Real.exp lam ≠ 0 := ne_of_gt (Real.exp_pos lam)
  have hid : Real.exp (-lam)*(Real.exp lam-1) = 1-Real.exp (-lam) := by
    rw [mul_sub,Real.exp_neg,inv_mul_cancel₀ he,mul_one]
  unfold tail
  field_simp
  nlinarith [hid]
/-- Exact separation-tail estimate, including intervals crossing either end
of the support. The two actual distances are later substituted for a,b. -/
theorem tail_difference (lam a b : ℝ) (hlam : 0 < lam) (hab : a ≤ b) :
    tail lam a-tail lam b ≤ lam*(b-a)*(tail lam a+1/(Real.exp lam-1))
 := by
  have hd := denominator_pos lam hlam
  have hca := clipped_bounds a
  have hc := clipped_mono hab
  have heq : Real.exp (-lam*clipped b) =
      Real.exp (-lam*clipped a)*Real.exp (-lam*(clipped b-clipped a)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hexp : 1-Real.exp (-lam*(clipped b-clipped a)) ≤ lam*(clipped b-clipped a) := by
    have := Real.add_one_le_exp (-lam*(clipped b-clipped a))
    linarith
  have hstep : 1-Real.exp (-lam*(clipped b-clipped a)) ≤ lam*(b-a) :=
    hexp.trans (mul_le_mul_of_nonneg_left (clipped_difference a b hab) hlam.le)
  rw [tail_offset lam a hlam]
  calc
    tail lam a-tail lam b =
        Real.exp (-lam*clipped a)*(1-Real.exp (-lam*(clipped b-clipped a)))/(1-Real.exp (-lam)) := by
      unfold tail
      rw [heq,←sub_div]
      congr 1
      ring
    _ ≤ Real.exp (-lam*clipped a)*(lam*(b-a))/(1-Real.exp (-lam)) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le) hd.le
    _ = _ := by ring
end
end UniformKServer.RadiusTail

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RadiusFirstHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section
namespace UniformKServer.RadiusFirstHit
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X]

theorem ordered_tail (lam a b D : ℝ) (hlam : 0 < lam) (hab : a ≤ b) (hD : b-a ≤ D) :
    |RadiusTail.tail lam a-RadiusTail.tail lam b| ≤
      lam*D*(max (RadiusTail.tail lam a) (RadiusTail.tail lam b)+1/(Real.exp lam-1)) := by
  have hanti := RadiusTail.tail_antitone lam hlam hab
  rw [abs_of_nonneg (sub_nonneg.mpr hanti),max_eq_left hanti]
  apply (RadiusTail.tail_difference lam a b hlam hab).trans
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hlam.le)
  exact add_nonneg (RadiusTail.tail_bounds lam a hlam).1
    (one_div_nonneg.mpr (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hlam.le)))

end
end UniformKServer.RadiusFirstHit

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RadiusRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The first-hit estimate for the entire actual present roster.  The global
roster may have far more than K² records. Only centers that can hit one of the
two points incur a truncated-tail correction; all other coordinates remain
in the actual independent product law. -/
namespace UniformKServer.RadiusRoster
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable
variable {I : Type*} [LinearOrder I] {X : Type} [Fintype X] [MetricSpace X]

omit [Fintype X] in
/-- Repeated centers are distinct chronological identities, not collapsed
into a set of sites. This count therefore applies to the actual roster. -/
theorem candidate_count (S : Finset I) (is : List I) (c : I → X) (r : ℝ)
    (A : ℕ) (x y : X) (hr : 0 ≤ r) (hxy : dist x y ≤ r)
    (hnodup : is.Nodup) (hsub : ∀ i ∈ is, i ∈ S)
    (hage : ∀ i ∈ is, ChronologicalRoster.age S c r i < A) :
    (is.filter (fun i => decide (dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r))).length ≤ A := by
  let P : I → Prop := fun i => dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r
  let T := (is.filter (fun i => decide (P i))).toFinset
  have hmem (i : I) : i ∈ T ↔ i ∈ is ∧ P i := by simp [T]
  have hnear (i : I) (hi : i ∈ T) : dist (c i) x ≤ 3*r := by
    rcases (hmem i).mp hi with ⟨_,hi|hi⟩
    · linarith
    · have ht := dist_triangle (c i) y x
      rw [dist_comm y x] at ht
      linarith
  have hc : T.card ≤ A := ChronologicalRoster.local_age_count S T c r A
    (fun i hi => hsub i ((hmem i).mp hi).1)
    (fun i hi => hage i ((hmem i).mp hi).1)
    (by
      intro i hi j hj
      have ht := dist_triangle (c i) x (c j)
      rw [dist_comm x (c j)] at ht
      linarith [hnear i hi,hnear j hj])
  simpa only [T,List.toFinset_card_of_nodup (hnodup.filter _)] using hc

end
end UniformKServer.RadiusRoster

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! One universal finite radius seed covers every possible input-driven
center, so the seed law is independent of the hidden input. -/
noncomputable section
namespace UniformKServer.TierRadius
open FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def probability (lam r : ℝ) (a : X × X) : ℝ := RadiusTail.tail lam (dist a.1 a.2/r)
abbrev Sample (lam r : ℝ) := FiniteThreshold.Signature (@probability X _ lam r)
def law (lam r : ℝ) : Law (Sample (X:=X) lam r) := FiniteThreshold.experiment (probability lam r : X × X → ℝ)

def entry (lam r : ℝ) (c x y : X) : FirstHit.Entry where
  Sample := Sample (X:=X) lam r
  finite := inferInstance
  law := law lam r
  hit ω := ω.val (c,x) || ω.val (c,y)
  separates ω := ω.val (c,x) != ω.val (c,y)
  separates_hit := by
    intro ω h
    cases hx : ω.val (c,x) <;> cases hy : ω.val (c,y) <;> simp_all

omit [Fintype X] in
theorem cover_inner (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (ω : Sample (X:=X) lam r)
    (c p : X) (hd : dist c p ≤ r) : ω.val (c,p)=true := by
  obtain ⟨u,hu,he⟩ := ω.property
  rw [he]
  change decide (u ≤ probability lam r (c,p))=true
  apply decide_eq_true
  change u ≤ RadiusTail.tail lam (dist c p/r)
  rw [RadiusTail.tail_eq_one lam _ hlam ((div_le_one hr).mpr hd)]
  exact hu.2

theorem local_bound (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (c x y : X) :
    FirstHit.separationProbability (entry lam r c x y) ≤
      (lam*dist x y/r)*(FirstHit.hitProbability (entry lam r c x y)+1/(Real.exp lam-1)) := by
  have hp (a : X × X) : probability lam r a ∈ Set.Icc (0:ℝ) 1 := RadiusTail.tail_bounds lam _ hlam
  change (FiniteThreshold.experiment (probability lam r : X × X → ℝ)).expect
      (fun ω => if ω.val (c,x) != ω.val (c,y) then (1:ℝ) else 0) ≤
    (lam*dist x y/r)*((FiniteThreshold.experiment (probability lam r : X × X → ℝ)).expect
      (fun ω => if ω.val (c,x) || ω.val (c,y) then (1:ℝ) else 0)+_)
  rw [FiniteThreshold.threshold_separation (probability lam r) hp,
    FiniteThreshold.threshold_hit (probability lam r) hp]
  unfold probability
  rw [mul_div_assoc]
  rcases le_total (dist c x) (dist c y) with hxy|hyx
  · apply RadiusFirstHit.ordered_tail lam _ _ _ hlam (div_le_div_of_nonneg_right hxy hr.le)
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [dist_triangle c x y]
  · rw [abs_sub_comm,max_comm]
    apply RadiusFirstHit.ordered_tail lam _ _ _ hlam (div_le_div_of_nonneg_right hyx hr.le)
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [dist_triangle c y x,dist_comm x y]

theorem hit_zero (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (c x y : X)
    (hx : 2*r ≤ dist c x) (hy : 2*r ≤ dist c y) :
    FirstHit.hitProbability (entry lam r c x y)=0 := by
  have hp (a : X × X) : probability lam r a ∈ Set.Icc (0:ℝ) 1 := RadiusTail.tail_bounds lam _ hlam
  change (FiniteThreshold.experiment (probability lam r : X × X → ℝ)).expect
    (fun ω => if ω.val (c,x) || ω.val (c,y) then (1:ℝ) else 0)=0
  rw [FiniteThreshold.threshold_hit (probability lam r) hp]
  unfold probability
  rw [RadiusTail.tail_eq_zero lam _ ((le_div_iff₀ hr).mpr hx),
    RadiusTail.tail_eq_zero lam _ ((le_div_iff₀ hr).mpr hy),max_self]

end UniformKServer.TierRadius

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! The actual persistent-radius tape controls all roster keys at once;
conditioning on arbitrary independent lifetimes leaves these estimates valid. -/
noncomputable section
namespace UniformKServer.TierKeys
open FiniteProbability Finset
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [LinearOrder I] {X : Type} [Fintype X] [MetricSpace X]
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def key (lam r : ℝ) (is : List I) (c : I → X) (ω : I → TierRadius.Sample (X:=X) lam r) (p : X) : Option I :=
  is.find? (fun i => (ω i).val (c i,p))

omit [Fintype I] [LinearOrder I] [Fintype X] in
theorem key_mem (lam r : ℝ) (is : List I) (c : I → X) (ω : I → TierRadius.Sample (X:=X) lam r)
    (p : X) (i : I) (hi : key lam r is c ω p=some i) : i ∈ is := by
  exact List.mem_of_find?_eq_some hi

omit [Fintype I] [LinearOrder I] [Fintype X] in
theorem key_cons (lam r : ℝ) (is : List I) (i : I) (c : I → X)
    (ω : I → TierRadius.Sample (X:=X) lam r) (p : X) :
    key lam r (i::is) c ω p=if (ω i).val (c i,p) then some i else key lam r is c ω p := by
  unfold key
  rw [List.find?_cons]
  cases (ω i).val (c i,p) <;> rfl

omit [Fintype I] [LinearOrder I] in
theorem disagreement (lam r : ℝ) (is : List I) (hn : is.Nodup) (c : I → X)
    (ω : I → TierRadius.Sample (X:=X) lam r) (x y : X) :
    FirstHit.firstPi (fun i => TierRadius.entry lam r (c i) x y) is ω=
      decide (key lam r is c ω x ≠ key lam r is c ω y) := by
  induction is with
  | nil => simp [FirstHit.firstPi,key]
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    have hx : key lam r is c ω x ≠ some i := fun h => hi (key_mem lam r is c ω x i h)
    have hy : key lam r is c ω y ≠ some i := fun h => hi (key_mem lam r is c ω y i h)
    have he := ih hn
    change (if (ω i).val (c i,x) || (ω i).val (c i,y) then
      (ω i).val (c i,x) != (ω i).val (c i,y) else
      FirstHit.firstPi (fun j => TierRadius.entry lam r (c j) x y) is ω)=_
    simp_rw [key_cons]
    cases hleft : (ω i).val (c i,x) <;> cases hright : (ω i).val (c i,y)
    · simpa only [Bool.false_or,Bool.false_eq_true,ite_false, if_false] using he
    · simp [hx]
    · simp [Ne.symm hy]
    · simp

theorem separation (S : Finset I) (is : List I) (c : I → X) (K : ℕ) (hK : 2 ≤ K)
    (r : ℝ) (hr : 0 < r) (x y : X) (hxy : dist x y < r/4) (hn : is.Nodup)
    (hsub : ∀ i ∈ is, i ∈ S) (hage : ∀ i ∈ is, ChronologicalRoster.age S c r i < K^2) :
    let lam := Real.log (1+(K:ℝ)^2)
    (Law.pi (fun _ : I => TierRadius.law (X:=X) lam r)).expect
      (fun ω => if key lam r is c ω x ≠ key lam r is c ω y then (1:ℝ) else 0) ≤
      2*lam*dist x y/r := by
  dsimp only
  let lam := Real.log (1+(K:ℝ)^2)
  let E := fun i => TierRadius.entry lam r (c i) x y
  let P : I → Prop := fun i => dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0<K)
  have hsq : 0 < (K:ℝ)^2 := sq_pos_of_pos hKr
  have hlam : 0 < lam := Real.log_pos (by linarith)
  have hexp : Real.exp lam-1=(K:ℝ)^2 := by rw [Real.exp_log (by positivity)]; ring
  have hcount := RadiusRoster.candidate_count S is c r (K^2) x y hr.le (by linarith) hn hsub hage
  have hb := FirstHit.first_hit_support is E P (lam*dist x y/r) (1/(K:ℝ)^2)
    (by positivity) (by positivity)
    (by intro i _ _; simpa only [hexp] using TierRadius.local_bound lam r hlam hr (c i) x y)
    (by
      intro i _ hi
      exact TierRadius.hit_zero lam r hlam hr (c i) x y
        (le_of_not_ge (not_or.mp hi).1) (le_of_not_ge (not_or.mp hi).2))
  have he (ω : I → TierRadius.Sample (X:=X) lam r) :
      (if key lam r is c ω x ≠ key lam r is c ω y then (1:ℝ) else 0)=
      (if FirstHit.firstPi E is ω then 1 else 0) := by
    rw [disagreement lam r is hn c ω x y]
    simp
  rw [Law.expect_congr _ _ _ he]
  have hpi : (Law.pi (fun _ : I => TierRadius.law (X:=X) lam r)).expect
      (fun ω => if FirstHit.firstPi E is ω then (1:ℝ) else 0)=
      (FirstHit.experiment (is.map E)).expect (fun ω => if FirstHit.firstSeparates _ ω then 1 else 0) :=
    FirstHit.pi_expect_first E is hn
  rw [hpi]
  have hcr : ((is.filter (fun i => decide (P i))).length:ℝ) ≤ (K:ℝ)^2 := by exact_mod_cast hcount
  have hfrac : ((is.filter (fun i => decide (P i))).length:ℝ)*(1/(K:ℝ)^2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hsq).mpr hcr
  have hdec (i : I) : @decide (P i) (Classical.propDecidable (P i))=decide (P i) := by
    exact congrArg (@decide (P i)) (Subsingleton.elim _ _)
  simp only [hdec] at hb
  calc
    _ ≤ (lam*dist x y/r)*(1+((is.filter (fun i => decide (P i))).length:ℝ)*(1/(K:ℝ)^2)) := hb
    _ ≤ (lam*dist x y/r)*2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end UniformKServer.TierKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TierPilot

section
attribute [local instance] Classical.propDecidable
open PilotCompact

/-- The two source pilot templates use D_H=51200, R_L=4D_H, D_L=100R_L.
The small numerical parameters remain free so the later travel absorption can
choose them once and for all. -/
structure Parameters where
  sigma : ℝ
  gammaH : ℝ
  gammaL : ℝ
  deltaH : ℝ
  sigma_pos : 0 < sigma
  sigma_small : 3*sigma < 1/8
  sigma_gamma : 10*sigma < gammaH
  gammaH_small : gammaH ≤ 1/100
  gammaL_pos : 0 < gammaL
  gammaL_small : gammaL < sigma
  deltaH_pos : 0 < deltaH
  deltaH_small : deltaH ≤ 1/4112

variable {X : Type*} [Fintype X] [MetricSpace X]

def heavy (P : Parameters) (r : ℝ) (μ : X → ℝ) (x : X) : Prop :=
  ballMass r 51200 μ x ≤ (1+P.deltaH)*ballMass r P.gammaH μ x

def insertionMass (P : Parameters) (r : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  if heavy P r μ x then ballMass r 51200 μ x-ballMass r P.gammaH μ x
  else ballMass r 20480000 μ x

omit [Fintype X] [MetricSpace X] in
theorem Parameters.sigma_le_one (P : Parameters) : P.sigma ≤ 1 := by linarith [P.sigma_small]
omit [Fintype X] [MetricSpace X] in
theorem Parameters.gammaH_pos (P : Parameters) : 0 < P.gammaH := by
  linarith [P.sigma_pos,P.sigma_gamma]

end
open PilotCompact

end UniformKServer.TierPilot

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ShortRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ShortRoster

section
open FiniteProbability
variable {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable

/-- A clipped distance-to-set ramp, expressed as the minimum of all live
center costs and the empty-roster cost one. -/
def costValue (a : I → ℝ) (H : Finset I) : ℝ :=
  (insert 1 (H.image a)).min' (by simp)

/-- Continue all old lifetime trials using fresh independent keep bits;
compulsory cutoffs apply on the same age increment. The new entry's ramp
value is supplied separately so duplicates of physical centers are harmless. -/
def retained (inc kill : I → Prop) (H : Finset I) (τ : I → Bool) : Finset I :=
  H.filter fun i => ¬inc i ∨ (¬kill i ∧ τ i = true)

def fresh (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) : Law (I → Bool) :=
  coins (fun _ => 1-q) (fun _ => ⟨by linarith [hq.2],by linarith [hq.1]⟩)

end

section
open FiniteProbability
attribute [local instance] Classical.propDecidable

/-- The finite random experiment is part of the constructed state, not an
assumed randomized-policy interface. -/
structure State (I : Type) where
  Sample : Type
  finite : Fintype Sample
  law : @Law Sample finite
  live : Sample → Finset I

attribute [instance] State.finite

variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

def ramp (v : ℝ) : ℝ := max 0 (min 1 (8*v-1))

def State.parameter (D : State I) (c : I → X) (r : ℝ) (p : X) : ℝ :=
  D.law.expect fun ω => costValue (fun i => ramp (dist p (c i)/r)) (D.live ω)

def State.next (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I) : State I where
  Sample := D.Sample × (I → Bool)
  finite := inferInstance
  law := D.law.prod (fresh q hq)
  live ω := insert n (retained (fun i => dist (c i) (c n) ≤ 20*r)
    (fun i => K ≤ ChronologicalRoster.age S c r i+1) (D.live ω.1) ω.2)

end

attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster

end UniformKServer.ShortRoster

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ShortRosterValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section
namespace UniformKServer.ShortRoster
noncomputable section
attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]
local instance rosterDecEq : DecidableEq I := fun a b => Classical.propDecidable (a=b)

/- Finite-set insertion does not depend on the implementation of equality.
This bridge lets the ordered-age lemmas coexist with the canonical classical
finite coin sample space. -/
omit [Fintype I] in
theorem insert_linear (S : Finset I) (n : I) :
    insert n S = @insert I (Finset I)
      (@Finset.instInsert I (fun a b => LinearOrder.toDecidableEq a b)) n S := by
  ext i
  simp only [Finset.mem_insert]

def State.empty : State I where
  Sample := Unit
  finite := inferInstance
  law := ⟨fun _ => 1,by intro; norm_num,by simp⟩
  live _ := ∅

omit [LinearOrder I] in
theorem retained_marginal (inc kill : I → Prop) (H : Finset I)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (i : I) :
    (fresh (I := I) q hq).expect (fun τ => if i ∈ retained inc kill H τ then 1 else 0) =
      (if i ∈ H then 1 else 0)*(if inc i then (if kill i then 0 else 1-q) else 1) := by
  classical
  by_cases hi : i ∈ H
  · by_cases hc : inc i
    · by_cases hk : kill i
      · simp [retained,hi,hc,hk,Law.expect_const]
      · simp only [retained,Finset.mem_filter,hi,hc,hk,not_true_eq_false,not_false_eq_true,
          true_and,false_or,ite_true, if_true,ite_false, if_false,one_mul]
        exact coins_true _ _ i
    · simp [retained,hi,hc,Law.expect_const]
  · simp [retained,hi,Law.expect_const]

end
end UniformKServer.ShortRoster

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section
namespace UniformKServer.ActualRoster
noncomputable section
attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster ShortRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]
local instance rosterDecEq : DecidableEq I := fun a b => Classical.propDecidable (a=b)

def survival (K a : ℕ) : ℝ := if a < K^2 then (1-1/(K:ℝ))^(a+1-K) else 0

def valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) : Prop :=
  (∀ ω, D.live ω ⊆ young S c r (K^2)) ∧
    ∀ i, D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) =
      if i ∈ S then survival K (age S c r i) else 0

def active (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) (n i : I) : Prop :=
  dist (c i) (c n) ≤ 20*r ∧ K ≤ age S c r i+1

def compulsory (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) (i : I) : Prop :=
  K^2 ≤ age S c r i+1

def next (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n : I) : State I where
  Sample := D.Sample × (I → Bool)
  finite := inferInstance
  law := D.law.prod (fresh (1/(K:ℝ)) hq)
  live ω := insert n (retained (active S c r K n) (compulsory S c r K) (D.live ω.1) ω.2)

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem survival_zero (K : ℕ) (hK : 0 < K) : survival K 0 = 1 := by
  simp only [survival,show 0<K^2 by positivity,ite_true, if_true,zero_add]
  rw [Nat.sub_eq_zero_of_le hK,pow_zero]

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem survival_step (K a : ℕ) (hK : 2 ≤ K) :
    survival K (a+1) = survival K a *
      (if K ≤ a+1 then (if K^2 ≤ a+1 then 0 else 1-1/(K:ℝ)) else 1) := by
  have hkk : K ≤ K^2 := by nlinarith
  by_cases hcut : K^2 ≤ a+1
  · simp only [survival,not_lt.mpr hcut,ite_false, if_false,ite_eq_left (hkk.trans hcut),ite_eq_left hcut,mul_zero]
  · have hay : a < K^2 := by omega
    have hay' : a+1 < K^2 := by omega
    simp only [survival,ite_eq_left hay,ite_eq_left hay',ite_eq_right hcut]
    by_cases htrial : K ≤ a+1
    · rw [ite_eq_left htrial,show a+1+1-K=(a+1-K)+1 by omega,pow_succ]
    · have hzero : a+1-K=0 := by omega
      have hzero' : a+1+1-K=0 := by omega
      simp only [ite_eq_right htrial,hzero,hzero',pow_zero,mul_one]

theorem next_marginal (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n i : I) (hi : i ≠ n) :
    (next D S c r K hq n).law.expect (fun ω => if i ∈ (next D S c r K hq n).live ω then 1 else 0) =
      (if active S c r K n i then (if compulsory S c r K i then 0 else 1-1/(K:ℝ)) else 1)*
        D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) := by
  change (D.law.prod (fresh (1/(K:ℝ)) hq)).expect (fun ω =>
    if i ∈ insert n (retained (active S c r K n) (compulsory S c r K) (D.live ω.1) ω.2) then 1 else 0) = _
  rw [D.law.expect_prod (fresh (1/(K:ℝ)) hq) (fun ω τ =>
    if i ∈ insert n (retained (active S c r K n) (compulsory S c r K) (D.live ω) τ) then 1 else 0)]
  simp only [Finset.mem_insert,hi,false_or,retained_marginal]
  conv_rhs => rw [←D.law.expect_mul]
  apply D.law.expect_congr
  intro ω
  by_cases hmem : i ∈ D.live ω
  · simp only [ite_eq_left hmem,one_mul,mul_one]
  · simp only [ite_eq_right hmem,zero_mul,mul_zero]
theorem next_valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (K : ℕ) (hK : 2 ≤ K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : valid D S c r K) (hn : ∀ i ∈ S, i < n) :
    valid (next D S c r K hq n) (insert n S) c r K := by
  classical
  have hkpos : 0 < K := by omega
  have hkk : K ≤ K^2 := by nlinarith
  rw [insert_linear S n]
  constructor
  · intro ω i hi
    simp only [next,Finset.mem_insert] at hi
    obtain hei | hi := hi
    · subst i
      simp only [young,Finset.mem_filter,Finset.mem_insert_self,true_and]
      rw [new_age_zero S c r n hn]
      positivity
    · have hi' : i ∈ D.live ω.1 ∧
          (¬active S c r K n i ∨ (¬compulsory S c r K i ∧ ω.2 i = true)) := by
        simpa only [retained,Finset.mem_filter] using hi
      obtain ⟨hi,hstay⟩ := hi'
      obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp (hD.1 ω.1 hi)
      simp only [young,Finset.mem_filter,Finset.mem_insert,hiS,or_true,true_and]
      rw [age_insert S c r n i hn hiS]
      by_cases hd : dist (c i) (c n) ≤ 20*r
      · rw [ite_eq_left hd]
        rcases hstay with hstay | hstay
        · change ¬(dist (c i) (c n) ≤ 20*r ∧ K ≤ age S c r i+1) at hstay
          have : age S c r i+1 < K := lt_of_not_ge (fun h => hstay ⟨hd,h⟩)
          omega
        · exact lt_of_not_ge hstay.1
      · simpa only [ite_eq_right hd,add_zero] using hage
  · intro i
    by_cases hi : i = n
    · subst i
      have he : ∀ ω, (if n ∈ (next D S c r K hq n).live ω then (1:ℝ) else 0) = 1 := by
        intro ω
        simp only [next,Finset.mem_insert_self,ite_true, if_true]
      rw [Law.expect_congr _ _ _ he,Law.expect_const,new_age_zero S c r n hn]
      simp only [Finset.mem_insert_self,ite_true, if_true,survival_zero K hkpos]
    · rw [next_marginal D S c r K hq n i hi,hD.2]
      by_cases hiS : i ∈ S
      · rw [age_insert S c r n i hn hiS]
        simp only [Finset.mem_insert,hiS,or_true,ite_true, if_true]
        by_cases hd : dist (c i) (c n) ≤ 20*r
        · simp only [active,hd,true_and,ite_true, if_true,compulsory]
          rw [survival_step K (age S c r i) hK]
          ring_nf
        · simp only [active,hd,false_and,ite_false, if_false,add_zero,one_mul]
      · simp only [hiS,hi,Finset.mem_insert,false_or,ite_false, if_false,mul_zero]
end
end UniformKServer.ActualRoster

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PiFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                              
section

noncomputable section
namespace UniformKServer.FiniteProbability
open Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]

theorem Law.expect_eq_indicator {Y : Type*} [Fintype Y] (P : Law Y) (y : Y) :
    P.expect (fun z => if z=y then (1:ℝ) else 0)=P.weight y := by
  simp only [Law.expect,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true, if_true]

theorem Law.expect_pi_fresh (P : ∀ i, Law (A i)) (i : I) {Y : Type*}
    (f : (∀ i, A i) → Y) (hf : ∀ a b, (∀ j, j ≠ i → a j=b j) → f a=f b)
    (g : Y → A i → ℝ) :
    (Law.pi P).expect (fun a => g (f a) (a i))=
      ((Law.pi P).prod (P i)).expect (fun z => g (f z.1) z.2) := by
  have hid (a : ∀ i, A i) : g (f a) (a i)=
      ∑ b : A i, (if a i=b then (1:ℝ) else 0)*g (f a) b := by
    simp only [ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ,ite_true, if_true]
  rw [Law.expect_congr _ _ _ hid,Law.expect_finset_sum]
  have hs (b : A i) :
      (Law.pi P).expect (fun a => (if a i=b then (1:ℝ) else 0)*g (f a) b)=
        (P i).weight b*(Law.pi P).expect (fun a => g (f a) b) := by
    rw [Law.expect_pi_separate (P:=P) i (fun c => if c=b then (1:ℝ) else 0)
      (fun a => g (f a) b) (by intro a c he; rw [hf a c he]),Law.expect_eq_indicator]
  simp_rw [hs]
  rw [Law.expect_prod (Law.pi P) (P i) (fun a b => g (f a) b)]
  change _ = (Law.pi P).expect (fun a => ∑ b, (P i).weight b*g (f a) b)
  rw [Law.expect_finset_sum]
  apply sum_congr rfl
  intro b _
  rw [Law.expect_mul]

end UniformKServer.FiniteProbability

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The literal insertion schedule. It inspects chronological ages, not
realized lifetimes, and is defined before any radius or lifetime tape. -/
noncomputable section
namespace UniformKServer.TierSchedule
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type*} [MetricSpace X] {N : ℕ}

def trigger (r : ℝ) (K : ℕ) (S : Finset (Fin N)) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) : Prop :=
  q n ∧ ¬∃ i ∈ young S c r K, dist (c n) (c i) ≤ r/2

def run (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) : ℕ → Finset (Fin N)
  | 0 => ∅
  | t+1 => if ht : t<N then
      if trigger r K (run r K q c t) q c ⟨t,ht⟩ then insert ⟨t,ht⟩ (run r K q c t) else run r K q c t
    else run r K q c t

theorem index_lt (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (i : Fin N) (hi : i ∈ run r K q c t) : i.val<t := by
  induction t with
  | zero => simp only [run,notMem_empty] at hi
  | succ t ih =>
    simp only [run] at hi
    split_ifs at hi with ht hn
    · rcases mem_insert.mp hi with rfl|hi
      · exact Nat.lt_succ_self t
      · exact Nat.lt_succ_of_lt (ih hi)
    · exact Nat.lt_succ_of_lt (ih hi)
    · exact Nat.lt_succ_of_lt (ih hi)

theorem chronological_coverage (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (hK : 0<K)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) (hq : q n) :
    ∃ i ∈ young (run r K q c (n.val+1)) c r K, dist (c n) (c i) ≤ r/2 := by
  have ht := n.isLt
  rw [run,dite_eq_left ht]
  by_cases hn : trigger r K (run r K q c n.val) q c n
  · rw [ite_eq_left hn]
    refine ⟨n,mem_filter.mpr ⟨mem_insert_self _ _,?_⟩,?_⟩
    · rw [new_age_zero]
      · exact hK
      · intro i hi
        exact index_lt r K q c n.val i hi
    · rw [dist_self]; positivity
  · rw [ite_eq_right hn]
    exact Classical.not_not.mp (fun hh => hn ⟨hq,hh⟩)

end UniformKServer.TierSchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLifetimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Actual tier lifetimes on one fixed finite independent tape. The chronological
schedule is formed before this tape and is not redefined by realized survival. -/
noncomputable section
namespace UniformKServer.TierLifetimes
open Finset FiniteProbability ChronologicalRoster ShortRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [MetricSpace X] {N : ℕ}
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

abbrev Tape (N : ℕ) := Fin N → (Fin N → Bool)

def live (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) : ℕ → Tape N → Finset (Fin N)
  | 0, _ => ∅
  | t+1, τ => if ht : t<N then
      let n : Fin N := ⟨t,ht⟩
      let S := TierSchedule.run r K q c t
      if TierSchedule.trigger r K S q c n then
        insert n (retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) (live r K q c t τ) (τ n))
      else live r K q c t τ
    else live r K q c t τ

theorem live_congr (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (a b : Tape N) (hab : ∀ j : Fin N, j.val<t → a j=b j) :
    live r K q c t a=live r K q c t b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => hab j (Nat.lt_succ_of_lt hj))
    simp only [live]
    split_ifs with ht hn
    · rw [he,hab ⟨t,ht⟩ (Nat.lt_succ_self t)]
    · exact he
    · exact he

def law (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) : Law (Tape N) :=
  Law.pi (I:=Fin N) (A:=fun _ => Fin N → Bool) (fun _ => fresh (I:=Fin N) (1/(K:ℝ)) hq)

def state (r : ℝ) (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : State (Fin N) where
  Sample := Tape N
  finite := inferInstance
  law := law K hq
  live := live r K q c t

theorem fresh_step (r : ℝ) (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (g : Finset (Fin N) → (Fin N → Bool) → ℝ) :
    (law K hq).expect (fun τ => g (live r K q c n.val τ) (τ n))=
      ((law K hq).prod (fresh (1/(K:ℝ)) hq)).expect (fun z => g (live r K q c n.val z.1) z.2) := by
  apply Law.expect_pi_fresh
  intro a b he
  apply live_congr
  intro j hj
  exact he j (fun h => by subst j; omega)

theorem valid (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    ActualRoster.valid (state r K hq q c t) (TierSchedule.run r K q c t) c r K := by
  induction t with
  | zero =>
    constructor
    · intro τ; exact empty_subset _
    · intro i
      change (law K hq).expect (fun _ => if i∈(∅ : Finset (Fin N)) then 1 else 0)=_
      simp only [notMem_empty,ite_false, if_false,Law.expect_const,TierSchedule.run]
  | succ t ih =>
    by_cases ht : t<N
    · let n : Fin N := ⟨t,ht⟩
      let S := TierSchedule.run r K q c t
      by_cases hn : TierSchedule.trigger r K S q c n
      · have hv := ActualRoster.next_valid (state r K hq q c t) S c r K hK hq n ih
          (fun i hi => TierSchedule.index_lt r K q c t i hi)
        have hr : TierSchedule.run r K q c (t+1)=insert n S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_left hn]
          ext i
          simp only [mem_insert]
          rfl
        have hl (τ : Tape N) : live r K q c (t+1) τ=
            (ActualRoster.next (state r K hq q c t) S c r K hq n).live (τ,τ n) := by
          rw [live,dite_eq_left ht]
          change (if TierSchedule.trigger r K S q c n then _ else _)=_
          rw [ite_eq_left hn]
          ext i
          simp only [ActualRoster.next,state,mem_insert]
          rfl
        rw [hr]
        constructor
        · change ∀ τ : Tape N, live r K q c (t+1) τ ⊆ _
          intro τ
          rw [hl]
          exact hv.1 (τ,τ n)
        · intro i
          change (law K hq).expect (fun τ => if i∈live r K q c (t+1) τ then 1 else 0)=_
          simp_rw [hl]
          change (law K hq).expect (fun τ => if i∈insert n
            (retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) (live r K q c n.val τ) (τ n)) then 1 else 0)=_
          rw [fresh_step r K hq q c n (fun H τ => if i∈insert n
            (retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) H τ) then 1 else 0)]
          exact hv.2 i
      · have hr : TierSchedule.run r K q c (t+1)=S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_right hn]
        have hl : state r K hq q c (t+1)=state r K hq q c t := by
          unfold state
          congr 1
          funext τ
          rw [live,dite_eq_left ht]
          change (if TierSchedule.trigger r K S q c n then _ else _)=_
          rw [ite_eq_right hn]
        rw [hr,hl]; exact ih
    · have hr : TierSchedule.run r K q c (t+1)=TierSchedule.run r K q c t := by
        rw [TierSchedule.run,dite_eq_right ht]
      have hl : state r K hq q c (t+1)=state r K hq q c t := by
        unfold state
        congr 1
        funext τ
        simp only [live,dite_eq_right ht]
      rw [hr,hl]; exact ih

theorem young_present (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : Tape N) :
    young (TierSchedule.run r K q c t) c r K ⊆ live r K q c t τ := by
  induction t with
  | zero => intro i hi; exact (notMem_empty i (mem_filter.mp hi).1).elim
  | succ t ih =>
    by_cases ht : t<N
    · let n : Fin N := ⟨t,ht⟩
      let S := TierSchedule.run r K q c t
      by_cases hn : TierSchedule.trigger r K S q c n
      · have hr : TierSchedule.run r K q c (t+1)=insert n S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_left hn]
          ext i; simp only [mem_insert]; rfl
        rw [hr,live,dite_eq_left ht]
        change young (insert n S) c r K ⊆
          (if TierSchedule.trigger r K S q c n then _ else _)
        rw [ite_eq_left hn]
        intro i hi
        rcases mem_filter.mp hi with ⟨hi,hage⟩
        rcases mem_insert.mp hi with hnew|hi
        · exact mem_insert.mpr (Or.inl hnew)
        · apply mem_insert_of_mem
          apply mem_filter.mpr
          have horder : ∀ j ∈ S, j<n := fun j hj => TierSchedule.index_lt r K q c t j hj
          rw [ShortRoster.insert_linear S n,age_insert S c r n i horder hi] at hage
          have hold : age S c r i<K := by split_ifs at hage <;> omega
          refine ⟨ih (mem_filter.mpr ⟨hi,hold⟩),Or.inl ?_⟩
          intro ha
          have hd := ha.1
          rw [ite_eq_left hd] at hage
          exact (not_le_of_gt hage) ha.2
      · have hr : TierSchedule.run r K q c (t+1)=S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_right hn]
        rw [hr,live,dite_eq_left ht]
        change young S c r K ⊆ (if TierSchedule.trigger r K S q c n then _ else _)
        rw [ite_eq_right hn]
        exact ih
    · simpa only [TierSchedule.run,live,dite_eq_right ht] using ih

theorem coverage (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (hK : 0<K)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) (hn : q n) (τ : Tape N) :
    ∃ i∈live r K q c (n.val+1) τ, dist (c n) (c i) ≤ r/2 := by
  obtain ⟨i,hi,hd⟩ := TierSchedule.chronological_coverage r hr K hK q c n hn
  exact ⟨i,young_present r K q c _ τ hi,hd⟩

end UniformKServer.TierLifetimes

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierKeyProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

noncomputable section
namespace UniformKServer.TierKeyProcess
open FiniteProbability Finset ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

def key (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) : Option (Fin N) :=
  TierKeys.key (Real.log (1+(K:ℝ)^2)) r ((TierLifetimes.live r K q c t τ).sort (·≤·)) c ω p

theorem conditional_separation (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (τ : TierLifetimes.Tape N) (x y : X) (hxy : dist x y < r/4) :
    (Law.pi (fun _ : Fin N => TierRadius.law (X:=X) (Real.log (1+(K:ℝ)^2)) r)).expect
      (fun ω => if key r K q c t τ ω x≠key r K q c t τ ω y then (1:ℝ) else 0)≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hv := (TierLifetimes.valid r K hK hq q c t).1 τ
  apply TierKeys.separation (TierSchedule.run r K q c t) _ c K hK r hr x y hxy
  · exact sort_nodup _ _
  · intro i hi
    exact (mem_filter.mp (hv ((mem_sort _).mp hi))).1
  · intro i hi
    exact (mem_filter.mp (hv ((mem_sort _).mp hi))).2

theorem separation (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (x y : X) (hxy : dist x y < r/4) :
    ((TierLifetimes.law (N:=N) K hq).prod
      (Law.pi (fun _ : Fin N => TierRadius.law (X:=X) (Real.log (1+(K:ℝ)^2)) r))).expect
      (fun z => if key r K q c t z.1 z.2 x≠key r K q c t z.1 z.2 y then (1:ℝ) else 0)≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  rw [Law.expect_prod _ _ (fun τ ω => if key r K q c t τ ω x≠key r K q c t τ ω y then (1:ℝ) else 0)]
  have hh := (TierLifetimes.law (N:=N) K hq).expect_mono _
    (fun _ => 2*Real.log (1+(K:ℝ)^2)*dist x y/r)
    (fun τ => conditional_separation r hr K hK hq q c t τ x y hxy)
  simpa only [Law.expect_const] using hh

omit [Fintype X] in
theorem coverage (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K) (q : Fin N → Prop) (c : Fin N → X)
    (n : Fin N) (hn : q n) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) :
    (key r K q c (n.val+1) τ ω (c n)).isSome=true := by
  obtain ⟨i,hi,hd⟩ := TierLifetimes.coverage r hr.le K (by omega) q c n hn τ
  have hKr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hlam : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hKr])
  have hcover : (ω i).val (c i,c n)=true := TierRadius.cover_inner _ r hlam hr (ω i) _ _
    (by rw [dist_comm]; linarith)
  change (List.find? (fun j => (ω j).val (c j,c n))
    ((TierLifetimes.live r K q c (n.val+1) τ).sort (·≤·))).isSome = true
  rw [List.isSome_find?]
  exact List.any_eq_true.mpr ⟨i,(mem_sort _).mpr hi,hcover⟩

end UniformKServer.TierKeyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CooldownLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Fixed finite label pools with a full preceding-step cooldown. No historical
label is globally reserved: only current and preceding record sets are excluded. -/
noncomputable section
namespace UniformKServer.CooldownLabels
open Finset
open scoped Classical
variable {I : Type*} [DecidableEq I]

abbrev Slot (M : ℕ) := Fin (4*M+4)

def chooseSlot (M : ℕ) (S : Finset (Slot M)) : Slot M :=
  if h : ∃ a : Slot M, a∉S then Classical.choose h else ⟨0,by omega⟩

structure State (I : Type*) (M : ℕ) where
  label : I → Slot M
  previous : Finset (Slot M)

def step (M : ℕ) (S : Finset I) (b : Option I) (D : State I M) : State I M where
  label := match b with
    | none => D.label
    | some n => Function.update D.label n (chooseSlot M (D.previous ∪ S.image D.label))
  previous := S.image D.label

def run (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I) : ℕ → State I M
  | 0 => ⟨fun _ => ⟨0,by omega⟩,∅⟩
  | t+1 => step M (S t) (birth t) (run M S birth t)

theorem label_none (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (t : ℕ) (hb : birth t=none) : (run M S birth (t+1)).label=(run M S birth t).label := by
  simp only [run,step,hb]

end UniformKServer.CooldownLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabels
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

def reserved (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : Finset (Fin N) :=
  young (TierSchedule.run r K q c t) c r (K^2)

def birth (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : Option (Fin N) :=
  if ht : t<N then
    if TierSchedule.trigger r K (TierSchedule.run r K q c t) q c ⟨t,ht⟩ then some ⟨t,ht⟩ else none
  else none

def labels (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :=
  CooldownLabels.run (Fintype.card X*K^2) (reserved r K q c) (birth r K q c) t

end UniformKServer.TierLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabeledKeys
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

local instance pairDecEq_rc42fe4_2 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
abbrev Slot (X : Type) [Fintype X] (K : ℕ) := CooldownLabels.Slot (Fintype.card X*K^2)

def anchor (a : X) (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (l : Slot X K) : X :=
  if h : ∃ i∈TierLabels.reserved r K q c t, (TierLabels.labels r K q c t).label i=l then
    c (Classical.choose h) else a

def key (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) : Option (Slot X K) :=
  (TierKeyProcess.key r K q c t τ ω p).map (TierLabels.labels r K q c t).label

end UniformKServer.TierLabeledKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelMap
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
local instance indexDecEq_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEq : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

structure Data (X : Type) [Fintype X] [MetricSpace X] (N H : ℕ) where
  r : ℝ
  positive : 0 < r
  K : Fin H → ℕ
  two : ∀ i, 2≤K i
  base : X
  center : Fin N → X
  heavy : Fin N → Prop
  qualify : Fin H → Fin N → Prop

abbrev HeavySlot (X : Type) [Fintype X] := Fin (2*Fintype.card X+1)
abbrev Label (D : Data X N H) := HeavySlot X ⊕ ((i : Fin H) × TierLabeledKeys.Slot X (D.K i)) ⊕ X
abbrev HeavyTape (D : Data X N H) := Fin N → HeavyRadius.Sample (X:=X) D.r
abbrev TierTape (D : Data X N H) (i : Fin H) := TierLifetimes.Tape N ×
  (Fin N → TierRadius.Sample (X:=X) (Real.log (1+(D.K i:ℝ)^2)) D.r)
abbrev Tape (D : Data X N H) := HeavyTape D × (∀ i, TierTape D i)

namespace Data

local instance indexDecEq_rc42fe4_2 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
theorem quota (D : Data X N H) (i : Fin H) : 1/(D.K i:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
  have hk : (2:ℝ)≤D.K i := by exact_mod_cast D.two i
  constructor
  · positivity
  · exact (div_le_one (by linarith)).mpr (by linarith)

def point (D : Data X N H) (t : ℕ) : X := if ht : t<N then D.center ⟨t,ht⟩ else D.base
def heavyFlag (D : Data X N H) (t : ℕ) : Prop := ∃ ht : t<N, D.heavy ⟨t,ht⟩

def heavyState (D : Data X N H) (ω : HeavyTape D) (t : ℕ) :
    HeavyRecords.State X (HeavySlot X) D.r :=
  HeavyProcess.slice D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point N ω t

def heavyKey (D : Data X N H) (ω : Tape D) (t : ℕ) (p : X) : Option (Label D) :=
  (HeavyRecords.key (D.heavyState ω.1 t) p).map Sum.inl

def tierKey (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) : Option (Label D) :=
  (TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p).map
    (fun l => Sum.inr (Sum.inl ⟨i,l⟩))

def key (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p : X) : Label D :=
  ((D.heavyKey ω t p).or (FirstStructure.first is (fun i => D.tierKey ω t i p))).getD (Sum.inr (Sum.inr p))

def anchor (D : Data X N H) (ω : Tape D) (t : ℕ) : Label D → X
  | Sum.inl l => (D.heavyState ω.1 t).center l
  | Sum.inr (Sum.inl ⟨i,l⟩) => TierLabeledKeys.anchor D.base D.r (D.K i) (D.qualify i) D.center t l
  | Sum.inr (Sum.inr p) => p

def tierLaw (D : Data X N H) (i : Fin H) : Law (TierTape D i) :=
  (TierLifetimes.law (N:=N) (D.K i) (D.quota i)).prod
    (Law.pi (fun _ : Fin N => TierRadius.law (X:=X) (Real.log (1+(D.K i:ℝ)^2)) D.r))

def law (D : Data X N H) : Law (Tape D) :=
  (Law.pi (fun _ : Fin N => HeavyRadius.law (X:=X) D.r)).prod (Law.pi D.tierLaw)

end Data
end UniformKServer.LevelMap

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelHeavy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance heavyPairDecEq_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance heavyIndexDecEq_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance heavyTierDecEq_rc42fe4_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
theorem point_at (D : Data X N H) (n : Fin N) : D.point n.val=D.center n := by
  simp only [point,dite_eq_left n.isLt]

theorem heavy_center (D : Data X N H) (n : Fin N) (hh : D.heavy n) (ω : HeavyTape D) :
    ∃ l∈(D.heavyState ω (n.val+1)).present,
      dist (D.center n) ((D.heavyState ω (n.val+1)).center l) ≤ 8*D.r := by
  have ht : D.heavyFlag n.val := ⟨n.isLt,hh⟩
  have hc := HeavySchedule.centers_coverage D.r D.positive.le D.heavyFlag D.point n.val ht
  have he : HeavyRecords.centers (D.heavyState ω (n.val+1))=
      HeavySchedule.centers D.r D.heavyFlag D.point (n.val+1) :=
    HeavyProcess.run_centers D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point
      (HeavyProcess.radiusStream D.r N ω) (HeavyProcess.radiusStream_bounds D.r D.positive.le N ω) (n.val+1)
  rw [←he,point_at] at hc
  obtain ⟨c,hc,hd⟩ := hc
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hc
  exact ⟨l,hl,hd⟩

theorem heavy_agreement (D : Data X N H) (n : Fin N) (hh : D.heavy n)
    (ω : Tape D) (p : X) (hp : dist (D.center n) p ≤ 8*D.r) :
    ∃ l, D.heavyKey ω (n.val+1) (D.center n)=some l ∧ D.heavyKey ω (n.val+1) p=some l := by
  obtain ⟨l,hl,hd⟩ := heavy_center D n hh ω.1
  have hr := ((D.heavyState ω.1 (n.val+1)).radius_bounds l hl).1
  have hc : HeavyRecords.covers (D.heavyState ω.1 (n.val+1)) l (D.center n) := by
    refine ⟨hl,?_⟩
    rw [dist_comm]
    linarith [D.positive]
  have hc' : HeavyRecords.covers (D.heavyState ω.1 (n.val+1)) l p := by
    refine ⟨hl,?_⟩
    have ht := dist_triangle ((D.heavyState ω.1 (n.val+1)).center l) (D.center n) p
    rw [dist_comm _ (D.center n)] at ht
    linarith
  have hs := (HeavyRecords.key_some _ D.positive.le _ l).mpr hc
  have hs' := (HeavyRecords.key_some _ D.positive.le _ l).mpr hc'
  exact ⟨Sum.inl l,by simp only [heavyKey,hs,Option.map_some],by simp only [heavyKey,hs',Option.map_some]⟩

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEq_rc42fe4_3 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEq : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem tier_coverage (D : Data X N H) (n : Fin N) (i : Fin H) (hi : D.qualify i n) (ω : Tape D) :
    (D.tierKey ω (n.val+1) i (D.center n)).isSome=true := by
  simpa only [tierKey,TierLabeledKeys.key,Option.isSome_map] using
    TierKeyProcess.coverage D.r D.positive (D.K i) (D.two i) (D.qualify i) D.center n hi
      (ω.2 i).1 (ω.2 i).2

theorem tier_separation (D : Data X N H) (t : ℕ) (i : Fin H) (p q : X) (hpq : dist p q<D.r/4) :
    D.law.expect (fun ω => indicator (D.tierKey ω t i p) (D.tierKey ω t i q))≤
      2*Real.log (1+(D.K i:ℝ)^2)*dist p q/D.r := by
  have hm := D.law.expect_mono _ _ (fun ω =>
    (indicator_map (fun o => o.map (fun l => (Sum.inr (Sum.inl ⟨i,l⟩) : Label D)))
      (TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p)
      (TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 q)).trans
    (indicator_map (fun o => o.map (TierLabels.labels D.r (D.K i) (D.qualify i) D.center t).label)
      (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p)
      (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 q)))
  change D.law.expect _≤D.law.expect (fun ω => indicator
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p)
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 q)) at hm
  apply hm.trans
  rw [law,Law.expect_prod _ _ (fun (_ : HeavyTape D) (b : ∀ j, TierTape D j) => indicator (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (b i).1 (b i).2 p) (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (b i).1 (b i).2 q))]
  simp only [Law.expect_const]
  rw [Law.expect_pi_coordinate D.tierLaw i (fun a => indicator
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 p)
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 q))]
  have he := TierKeyProcess.separation D.r D.positive (D.K i) (D.two i) (D.quota i)
    (D.qualify i) D.center t p q hpq
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply Law.expect_congr
  intro a
  by_cases hh : TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 p=
      TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 q
  · simp [indicator,hh]
  · simp [indicator,hh]

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Quantitative radius parameter used by the chronological tiers in §07.
Constants are explicit and independent of the metric and the horizon. -/
namespace UniformKServer.TierParameters
noncomputable section

def cutoff (C h : ℝ) : ℕ := ⌈Real.exp (C*h)⌉₊

theorem cutoff_two (C h : ℝ) (hC : 1 ≤ C) (hh : 1 ≤ h) : 2 ≤ cutoff C h := by
  have ha : 1 ≤ C*h := by nlinarith
  have he := Real.add_one_le_exp (C*h)
  have hc := Nat.le_ceil (Real.exp (C*h))
  have : (2:ℝ) ≤ (cutoff C h : ℝ) := by unfold cutoff; linarith
  exact_mod_cast this

end
end UniformKServer.TierParameters

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_DyadicTiers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! The source's dyadic tiers, including the minimal last tier and the sharp
prefix/unqualified sums. These coefficients are summed before summing scales. -/
noncomputable section
namespace UniformKServer.DyadicTiers
open Finset
open scoped Classical

def value (i : ℕ) : ℝ := 2^i

theorem one_le_value (i : ℕ) : 1≤value i := one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem unbounded (L : ℝ) : ∃ i : ℕ, L≤value i := by
  obtain ⟨n,hn⟩ := exists_nat_ge L
  refine ⟨n,hn.trans ?_⟩
  have hh : n≤(2:ℕ)^n := Nat.le_of_lt (Nat.lt_two_pow_self)
  dsimp only [value]
  exact_mod_cast hh

def last (L : ℝ) : ℕ := Nat.find (unbounded L)

end UniformKServer.DyadicTiers

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_GeometricMass
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

def radius (R q : ℝ) (j : ℕ) : ℝ := R*q^(j+1)
def mass (μ : X → ℝ) (x : X) (a : ℝ) : ℝ := ∑ y, if dist x y ≤ a then μ y else 0

theorem radius_pos (R q : ℝ) (hR : 0< R) (hq : 0< q) (j : ℕ) : 0< radius R q j := by
  unfold radius; positivity

end UniformKServer.GeometricMass

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Instantiation of the level construction from the true post-request GeometricMass.mass.
Tier qualifications are precisely the source exponential GeometricMass.mass test. -/
noncomputable section
namespace UniformKServer.PartitionLevel
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance pairDecEq_rc42fe4_3 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq_rc42fe4_4 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
structure Input (X : Type) [Fintype X] [MetricSpace X] (N : ℕ) where
  k : ℕ
  two : 2 ≤ k
  P : TierPilot.Parameters
  C : ℝ
  C_one : 1 ≤ C
  r : ℝ
  r_pos : 0< r
  base : X
  center : Fin N → X
  μ : Fin N → X → ℝ
  μ_nonneg : ∀ n x, 0 ≤ μ n x
  μ_total : ∀ n, ∑ x, μ n x ≤ k
  served : ∀ n, 1 ≤ μ n (center n)

namespace Input

local instance pairDecEq_rc42fe4_4 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq_rc42fe4_5 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
def height (I : Input X N) : ℕ := DyadicTiers.last (Real.log I.k)+1

def data (I : Input X N) : LevelMap.Data X N I.height where
  r := I.r
  positive := I.r_pos
  K i := TierParameters.cutoff I.C (DyadicTiers.value i.val)
  two i := TierParameters.cutoff_two I.C _ I.C_one (DyadicTiers.one_le_value i.val)
  base := I.base
  center := I.center
  heavy n := GeometricMass.mass (I.μ n) (I.center n) (51200*I.r) ≤
    (1+I.P.deltaH)*GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaH*I.r)
  qualify i n := GeometricMass.mass (I.μ n) (I.center n) (20480000*I.r) ≤
    Real.exp (DyadicTiers.value i.val)*GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r)

def order (I : Input X N) : List (Fin I.height) := List.ofFn id

end Input
end UniformKServer.PartitionLevel

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Final-map separation summed over geometric scales. The additive one in
the level estimate is charged only at nonheavy scales, not at every scale. -/
noncomputable section
namespace UniformKServer.PartitionScales
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N J : ℕ}

structure Input (X : Type) [Fintype X] [MetricSpace X] (N J : ℕ) where
  k : ℕ
  two : 2 ≤ k
  P : TierPilot.Parameters
  C : ℝ
  C_one : 1 ≤ C
  R : ℝ
  R_pos : 0< R
  q : ℝ
  q_pos : 0< q
  q_small : q ≤ 1/2
  shiftH : 51200*q ≤ P.gammaH
  shiftL : 20480000*q ≤ P.gammaL
  base : X
  center : Fin N → X
  μ : Fin N → X → ℝ
  μ_nonneg : ∀ n x, 0 ≤ μ n x
  μ_total : ∀ n, ∑ x, μ n x ≤ k
  served : ∀ n, 1 ≤ μ n (center n)

namespace Input

def level (I : Input X N J) (j : ℕ) : PartitionLevel.Input X N where
  k := I.k
  two := I.two
  P := I.P
  C := I.C
  C_one := I.C_one
  r := radius I.R I.q j
  r_pos := radius_pos I.R I.q I.R_pos I.q_pos j
  base := I.base
  center := I.center
  μ := I.μ
  μ_nonneg := I.μ_nonneg
  μ_total := I.μ_total
  served := I.served

end Input
end UniformKServer.PartitionScales

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section
namespace UniformKServer.TierInsertion
noncomputable section
open PilotCompact TierPilot ShortRoster ChronologicalRoster

def gainCoefficient (P : Parameters) : ℝ := min (1/2) (128*P.deltaH)

def lifetimeExponent (P : Parameters) : ℝ :=
  2*(Real.log (2*257*49/gainCoefficient P)+3)

end
end UniformKServer.TierInsertion

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The actual true-posterior partition, on every positive finite hidden law.
All inputs are the real post-request counts, not a fitted proxy mass. -/
noncomputable section
namespace UniformKServer.ActualPartitions
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

structure Config (X : Type) where
  P : TierPilot.Parameters
  C : ℝ
  C_one : 1≤C
  C_large : TierInsertion.lifetimeExponent P≤C
  R : ℝ
  R_pos : 0<R
  q : ℝ
  q_pos : 0<q
  q_small : q≤1/2
  shiftH : 51200*q≤P.gammaH
  shiftL : 20480000*q≤P.gammaL
  base : X

namespace Config

def input (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) (ω : Ω) :
    PartitionScales.Input X N J where
  k := k
  two := hk
  P := A.P
  C := A.C
  C_one := A.C_one
  R := A.R
  R_pos := A.R_pos
  q := A.q
  q_pos := A.q_pos
  q_small := A.q_small
  shiftH := A.shiftH
  shiftL := A.shiftL
  base := A.base
  center n := D.request n.val ω
  μ n := HiddenFlow.current D (n.val+1) ω
  μ_nonneg n := (HiddenFlow.flow D).post_nonneg (n.val+1) ω
  μ_total n := ((HiddenFlow.flow D).post_total (n.val+1) ω).le
  served n := HiddenFlow.serving_mass D n.val ω

theorem past_centers (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t : ℕ) (he : (D.filtration t).r ω v) (i : Fin N) (hi : i.val<t) :
    (A.input (J:=J) D hk ω).center i=(A.input (J:=J) D hk v).center i :=
  HiddenFlow.request_past D i.val t hi ω v he

theorem past_mass (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t : ℕ) (he : (D.filtration t).r ω v) (i : Fin N) (hi : i.val<t) :
    (A.input (J:=J) D hk ω).μ i=(A.input (J:=J) D hk v).μ i :=
  HiddenFlow.current_measurable D (i.val+1) t (by omega) ω v he

theorem past_heavy (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v) (i : Fin N) (hi : i.val<t) :
    ((A.input (J:=J) D hk ω).level j).data.heavy i ↔
      ((A.input (J:=J) D hk v).level j).data.heavy i := by
  change GeometricMass.mass ((A.input (J:=J) D hk ω).μ i) ((A.input (J:=J) D hk ω).center i) _ ≤ _ ↔ _
  dsimp only [PartitionLevel.Input.data,PartitionScales.Input.level]
  rw [A.past_mass (J:=J) D hk ω v t he i hi,A.past_centers (J:=J) D hk ω v t he i hi]
  rfl

theorem past_qualify (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (a : Fin ((A.input (N:=N) (J:=J) D hk ω).level j).height) (i : Fin N) (hi : i.val<t) :
    ((A.input (J:=J) D hk ω).level j).data.qualify a i ↔
      ((A.input (J:=J) D hk v).level j).data.qualify a i := by
  change GeometricMass.mass ((A.input (J:=J) D hk ω).μ i) ((A.input (J:=J) D hk ω).center i) _ ≤ _ ↔ _
  dsimp only [PartitionLevel.Input.data,PartitionScales.Input.level]
  rw [A.past_mass (J:=J) D hk ω v t he i hi,A.past_centers (J:=J) D hk ω v t he i hi]
  rfl

end Config
end UniformKServer.ActualPartitions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalHeavy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Causality of actual fixed-slot heavy records, including the cooldown state. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem pair_inputs (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h v : ℕ → Prop) (x y : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (hh : ∀ j<t, h j ↔ v j) (hx : ∀ j<t, x j=y j) :
    runPair a hr hΛ h x R hR t=runPair a hr hΛ v y R hR t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runPair,runPair,ih (fun j hj => hh j (by omega)) (fun j hj => hx j (by omega))]
    rw [propext (hh t (by omega)),hx t (by omega)]

theorem run_inputs (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h v : ℕ → Prop) (x y : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (hh : ∀ j<t, h j ↔ v j) (hx : ∀ j<t, x j=y j) :
    run a hr hΛ h x R hR t=run a hr hΛ v y R hR t := by
  unfold run
  rw [pair_inputs a hr hΛ h v x y R hR t hh hx]

omit [Fintype X] in
theorem centers_inputs (h v : ℕ → Prop) (x y : ℕ → X) (t : ℕ)
    (hh : ∀ j<t, h j ↔ v j) (hx : ∀ j<t, x j=y j) :
    HeavySchedule.centers r h x t=HeavySchedule.centers r v y t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [HeavySchedule.centers,HeavySchedule.centers,
      ih (fun j hj => hh j (by omega)) (fun j hj => hx j (by omega)),
      propext (hh t (by omega)),hx t (by omega)]

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalRosters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Dependence of the chronological insertion/slot schedule only on past true
inputs. No realized lifetime is used to decide a chronological insertion. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type} [MetricSpace X] {N : ℕ}

lemma age_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (i : Fin N)
    (hi : c i=d i) (he : ∀ j∈S, c j=d j) : age S c r i=age S d r i := by
  unfold age
  congr 1
  apply filter_congr
  intro j hj
  rw [hi,he j hj]

lemma young_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (A : ℕ)
    (he : ∀ j∈S, c j=d j) : young S c r A=young S d r A := by
  apply filter_congr
  intro j hj
  rw [age_congr S c d r j (he j hj) he]

lemma trigger_congr (S : Finset (Fin N)) (q v : Fin N → Prop) (c d : Fin N → X)
    (r : ℝ) (K : ℕ) (n : Fin N) (hq : q n ↔ v n) (hc : c n=d n)
    (he : ∀ j∈S, c j=d j) :
    TierSchedule.trigger r K S q c n ↔ TierSchedule.trigger r K S v d n := by
  unfold TierSchedule.trigger
  rw [hq,young_congr S c d r K he,hc]
  apply and_congr_right
  intro _
  apply not_congr
  constructor <;> rintro ⟨i,hi,hd⟩ <;> refine ⟨i,hi,?_⟩
  · rwa [he i (mem_filter.mp hi).1] at hd
  · rwa [he i (mem_filter.mp hi).1]

lemma schedule (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierSchedule.run r K q c t=TierSchedule.run r K v d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))
    simp only [TierSchedule.run]
    by_cases ht : t<N
    · simp only [dite_eq_left ht,hh]
      have he := trigger_congr (TierSchedule.run r K v d t) q v c d r K ⟨t,ht⟩
        (hq ⟨t,ht⟩ (by simp)) (hc ⟨t,ht⟩ (by simp))
        (fun j hj => hc j (Nat.lt_succ_of_lt (TierSchedule.index_lt r K v d t j hj)))
      rw [propext he]
    · simp only [dite_eq_right ht,hh]

lemma reserved (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierLabels.reserved r K q c t=TierLabels.reserved r K v d t := by
  unfold TierLabels.reserved
  rw [schedule r K q v c d t hq hc]
  exact young_congr _ c d r _ (fun j hj => hc j (TierSchedule.index_lt r K v d t j hj))

lemma birth (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val≤t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val≤t → c i=d i) :
    TierLabels.birth r K q c t=TierLabels.birth r K v d t := by
  unfold TierLabels.birth
  by_cases ht : t<N
  · simp only [dite_eq_left ht,schedule r K q v c d t (fun i hi => hq i hi.le) (fun i hi => hc i hi.le)]
    rw [propext (trigger_congr _ q v c d r K ⟨t,ht⟩ (hq _ le_rfl) (hc _ le_rfl)
      (fun j hj => hc j (TierSchedule.index_lt r K v d t j hj).le))]
  · simp only [dite_eq_right ht]

variable [Fintype X]

lemma labels (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierLabels.labels r K q c t=TierLabels.labels r K v d t := by
  unfold TierLabels.labels
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [CooldownLabels.run,CooldownLabels.run,
      reserved r K q v c d t (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega)),
      birth r K q v c d t (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega)),
      ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))]

end UniformKServer.CausalRosters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalTier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Causality of the realized live roster and its labeled key, with the entire
independent random tape held fixed. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type} [MetricSpace X] {N : ℕ}

local instance causalIndexDecEq_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
lemma active_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (K : ℕ)
    (n : Fin N) (hn : c n=d n) (he : ∀ j∈S, c j=d j) :
    ∀ i∈S, ActualRoster.active S c r K n i ↔ ActualRoster.active S d r K n i := by
  intro i hi
  unfold ActualRoster.active
  rw [hn,he i hi,age_congr S c d r i (he i hi) he]

lemma compulsory_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (K : ℕ)
    (he : ∀ j∈S, c j=d j) :
    ∀ i∈S, ActualRoster.compulsory S c r K i ↔ ActualRoster.compulsory S d r K i := by
  intro i hi
  unfold ActualRoster.compulsory
  rw [age_congr S c d r i (he i hi) he]

lemma live_subset (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N) :
    TierLifetimes.live r K q c t τ ⊆ TierSchedule.run r K q c t := by
  induction t with
  | zero => exact subset_rfl
  | succ t ih =>
    simp only [TierLifetimes.live,TierSchedule.run]
    split_ifs with ht hn
    · intro i hi
      simp only [mem_insert] at hi ⊢
      rcases hi with hi|hi
      · exact Or.inl hi
      · exact Or.inr (ih (mem_filter.mp hi).1)
    · exact ih
    · exact ih

lemma live_inputs (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (τ : TierLifetimes.Tape N) :
    TierLifetimes.live r K q c t τ=TierLifetimes.live r K v d t τ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))
    simp only [TierLifetimes.live]
    by_cases ht : t<N
    · simp only [dite_eq_left ht,schedule r K q v c d t (fun i hi => hq i (by omega))
        (fun i hi => hc i (by omega)),hh]
      let S := TierSchedule.run r K v d t
      have he : ∀ j∈S, c j=d j := fun j hj => hc j (Nat.lt_succ_of_lt (TierSchedule.index_lt r K v d t j hj))
      have hn := hc ⟨t,ht⟩ (by simp)
      rw [propext (trigger_congr S q v c d r K ⟨t,ht⟩ (hq _ (by simp)) hn he)]
      split_ifs
      · congr 1
        apply filter_congr
        intro i hi
        have his := live_subset r K v d t τ hi
        rw [active_congr S c d r K ⟨t,ht⟩ hn he i his,
          compulsory_congr S c d r K he i his]
      · rfl
    · simp only [dite_eq_right ht,hh]

lemma key_inputs (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    TierKeyProcess.key r K q c t τ ω p=TierKeyProcess.key r K v d t τ ω p := by
  unfold TierKeyProcess.key TierKeys.key
  rw [live_inputs r K q v c d t hq hc τ]
  apply List.find?_congr
  intro i hi
  rw [hc i (TierSchedule.index_lt r K v d t i
    (live_subset r K v d t τ ((mem_sort _).mp hi)))]

variable [Fintype X]

lemma labeled_inputs (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    TierLabeledKeys.key r K q c t τ ω p=TierLabeledKeys.key r K v d t τ ω p := by
  unfold TierLabeledKeys.key
  rw [key_inputs r K q v c d t hq hc τ ω p,labels r K q v c d t hq hc]

end UniformKServer.CausalRosters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Causal dependence of the actual level keys and all their occupied anchors. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

lemma tier_anchor (a : X) (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (l : TierLabeledKeys.Slot X K) :
    TierLabeledKeys.anchor a r K q c t l=TierLabeledKeys.anchor a r K v d t l := by
  unfold TierLabeledKeys.anchor
  simp only [reserved r K q v c d t hq hc,labels r K q v c d t hq hc]
  split_ifs with he
  · exact hc _ (TierSchedule.index_lt r K v d t _ (mem_filter.mp (Classical.choose_spec he).1).1)
  · rfl

end UniformKServer.CausalRosters
namespace UniformKServer.LevelMap.Data
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

def inputs (D : LevelMap.Data X N H) (c : Fin N → X) (h : Fin N → Prop)
    (q : Fin H → Fin N → Prop) : LevelMap.Data X N H :=
  { D with center := c, heavy := h, qualify := q }

lemma point_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (j : ℕ) (hj : j<t) :
    (D.inputs c h q).point j=(D.inputs d v u).point j := by
  unfold point inputs
  split_ifs with hn
  · exact hc ⟨j,hn⟩ hj
  · rfl

lemma heavy_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (hh : ∀ i : Fin N, i.val<t → (h i ↔ v i))
    (ω : LevelMap.HeavyTape D) :
    (D.inputs c h q).heavyState ω t=(D.inputs d v u).heavyState ω t := by
  apply HeavyProcess.run_inputs
  · intro j hj
    simp only [heavyFlag,inputs]
    apply exists_congr
    intro hjN
    exact hh ⟨j,hjN⟩ hj
  · exact fun j hj => point_inputs D c d h v q u t hc j hj

lemma anchor_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (hh : ∀ i : Fin N, i.val<t → (h i ↔ v i))
    (hq : ∀ a (i : Fin N), i.val<t → (q a i ↔ u a i))
    (ω : LevelMap.Tape D) (l : LevelMap.Label D) :
    (D.inputs c h q).anchor ω t l=(D.inputs d v u).anchor ω t l := by
  rcases l with l|⟨i,l⟩|p
  · change ((D.inputs c h q).heavyState ω.1 t).center l=_
    rw [heavy_inputs D c d h v q u t hc hh ω.1]
    rfl
  · exact CausalRosters.tier_anchor D.base D.r (D.K i) (q i) (u i) c d t (hq i) hc l
  · rfl

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeyEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section
namespace UniformKServer.KeyEdits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I J : Type*}

/-- Fixed earlier and later structures implement precedence. Label recycling
is immaterial to this one-edit operation: an unchanged record has its old
label and both other structures are held fixed. -/
def overlay (earlier : Option J) (label : I → J) (later : J) (o : Option I) : J :=
  earlier.getD ((o.map label).getD later)

def changed (earlier : Option J) (label : I → J) (later : J) (old new : Option I) : ℝ :=
  if overlay earlier label later old = overlay earlier label later new then 0 else 1

def uncovered (o : Option I) : ℝ := if o.isNone then 1 else 0

def retirement (old : Option I) (keep : I → Bool) : ℝ :=
  match old with
  | none => 0
  | some i => if keep i then 0 else 1

def next (old : List I) (keep : I → Bool) (n : I) : List I := old.filter keep ++ [n]
theorem first_persists (old : List I) (keep cover : I → Bool) (n i : I)
    (hfirst : old.find? cover = some i) (hkeep : keep i = true) :
    (next old keep n).find? cover = some i := by
  unfold next
  induction old with
  | nil => simp at hfirst
  | cons a old ih =>
    by_cases ha : cover a = true
    · have hai : a = i := by simpa [ha] using hfirst
      subst a
      simp [hkeep,ha]
    · have ht : old.find? cover = some i := by simpa [ha] using hfirst
      have hi := ih ht
      by_cases hk : keep a = true <;> simp [hk,ha,hi]

theorem changed_bounds (earlier : Option J) (label : I → J) (later : J) (old new : Option I) :
    changed earlier label later old new ∈ Set.Icc (0:ℝ) 1 := by
  unfold changed
  split_ifs <;> constructor <;> norm_num

@[simp] theorem changed_self (earlier : Option J) (label : I → J) (later : J) (old : Option I) :
    changed earlier label later old old = 0 := by simp [changed]

theorem uncovered_bounds (o : Option I) : uncovered o ∈ Set.Icc (0:ℝ) 1 := by
  cases o <;> norm_num [uncovered]

theorem insertion_mover (old : List I) (keep cover : I → Bool) (n : I)
    (earlier : Option J) (label : I → J) (later : J) :
    changed earlier label later (old.find? cover) ((next old keep n).find? cover) -
      uncovered (old.find? cover) ≤ retirement (old.find? cover) keep := by
  cases hfirst : old.find? cover with
  | none =>
    have hc := (changed_bounds earlier label later none ((next old keep n).find? cover)).2
    simp only [uncovered,Option.isNone_none,ite_true, if_true,retirement]
    linarith
  | some i =>
    by_cases hk : keep i = true
    · rw [first_persists old keep cover n i hfirst hk,changed_self]
      simp [uncovered,retirement,hk]
    · simpa only [uncovered,Option.isNone_some,Bool.false_eq_true,ite_false, if_false,sub_zero,retirement,ite_eq_right hk]
        using (changed_bounds earlier label later (some i) ((next old keep n).find? cover)).2

theorem shadowed (j : J) (label : I → J) (later : J) (old new : Option I) :
    changed (some j) label later old new = 0 := by simp [changed,overlay]
end
end UniformKServer.KeyEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FirstEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Serializing actual priority edits. The higher-priority prefix uses its
new state and the lower-priority suffix its old state, exactly as in source. -/
noncomputable section
namespace UniformKServer.FirstStructure
open scoped Classical
variable {I J : Type*}

def overlayKey (e : Option J) (is : List I) (f : I→Option J) (z : J) : J :=
  (e.or (first is f)).getD z

def editSum (f g : I→Option J) (z : J) : Option J→List I→ℝ
  | _,[] => 0
  | e,i::is => KeyEdits.changed e id ((first is f).getD z) (f i) (g i)+
      editSum f g z (e.or (g i)) is

theorem indicator_triangle (a b c : J) : indicator a c ≤ indicator a b+indicator b c := by
  unfold indicator
  split_ifs <;> simp_all

theorem overlay_step (e : Option J) (b : Option J) (is : List I) (f : I→Option J) (z : J) :
    (e.or (b.or (first is f))).getD z=KeyEdits.overlay e id ((first is f).getD z) b := by
  cases e <;> cases b <;> rfl

theorem serial_bound (e : Option J) (is : List I) (f g : I→Option J) (z : J) :
    indicator (overlayKey e is f z) (overlayKey e is g z)≤editSum f g z e is := by
  induction is generalizing e with
  | nil => simp [overlayKey,first,indicator,editSum]
  | cons i is ih =>
    have h := indicator_triangle (overlayKey e (i::is) f z)
      (overlayKey (e.or (g i)) is f z) (overlayKey e (i::is) g z)
    have h1 : indicator (overlayKey e (i::is) f z) (overlayKey (e.or (g i)) is f z)=
        KeyEdits.changed e id ((first is f).getD z) (f i) (g i) := by
      simp only [overlayKey,first]
      have he : ((e.or (g i)).or (first is f)).getD z=(e.or ((g i).or (first is f))).getD z := by
        cases e <;> rfl
      rw [he,overlay_step,overlay_step]
      rfl
    have h2 : overlayKey e (i::is) g z=overlayKey (e.or (g i)) is g z := by
      cases e <;> rfl
    rw [h1,h2] at h
    rw [h2]
    exact h.trans (add_le_add le_rfl (ih (e.or (g i))))

end UniformKServer.FirstStructure

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyEditRamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.HeavyEditRamp

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- The clipped ramp on [9,10]. -/
def ramp (v : ℝ) : ℝ := max 0 (min 1 (v-9))

/-- The source's ramp of distance to the center set, equal to one for the empty set. -/
def parameter (r : ℝ) (H : Finset X) (p : X) : ℝ :=
  (insert 1 (H.image (fun c => ramp (dist p c/r)))).min' (by simp)

end

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem ramp_bounds (v : ℝ) : ramp v ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

omit [MetricSpace X] in
theorem ramp_zero {v : ℝ} (h : v ≤ 9) : ramp v = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [MetricSpace X] in
theorem ramp_one {v : ℝ} (h : 10 ≤ v) : ramp v = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

omit [MetricSpace X] in
theorem ramp_lip (v w : ℝ) : |ramp v-ramp w| ≤ |v-w| := by
  have h₁ := abs_max_sub_max_le_max (0:ℝ) (min 1 (v-9)) 0 (min 1 (w-9))
  have h₂ := abs_min_sub_min_le_max (1:ℝ) (v-9) 1 (w-9)
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 (v-9)-min 1 (w-9)))] at h₁
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (v-9-(w-9)))] at h₂
  simpa only [sub_sub_sub_cancel_right,ramp] using h₁.trans h₂

theorem parameter_bounds (r : ℝ) (H : Finset X) (p : X) :
    parameter r H p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.le_min'
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · norm_num
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ha
      exact (ramp_bounds _).1
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem parameter_le_center (r : ℝ) (H : Finset X) (p c : X) (hc : c ∈ H) :
    parameter r H p ≤ ramp (dist p c/r) :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c,hc,rfl⟩))

theorem le_parameter (r : ℝ) (H : Finset X) (p : X) (a : ℝ) (h1 : a ≤ 1)
    (hc : ∀ c ∈ H, a ≤ ramp (dist p c/r)) : a ≤ parameter r H p := by
  apply Finset.le_min'
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact h1
  · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hb
    exact hc c hc'

theorem parameter_lip (r : ℝ) (hr : 0 < r) (H : Finset X) (p q : X) :
    |parameter r H p-parameter r H q| ≤ dist p q/r := by
  suffices h : ∀ p q : X, parameter r H p-parameter r H q ≤ dist p q/r by
    apply abs_le.mpr
    constructor
    · have hh := h q p
      rw [dist_comm q p] at hh
      linarith
    · exact h p q
  intro p q
  have hm := Finset.min'_mem (insert 1 (H.image (fun c => ramp (dist q c/r)))) (by simp)
  change parameter r H q ∈ insert 1 (H.image (fun c => ramp (dist q c/r))) at hm
  rcases Finset.mem_insert.mp hm with hq | hq
  · rw [hq]
    have := (parameter_bounds r H p).2
    exact (sub_nonpos.mpr this).trans (div_nonneg dist_nonneg hr.le)
  · obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hq
    have h₁ := parameter_le_center r H p c hc
    have h₂ := (le_abs_self (ramp (dist p c/r)-ramp (dist q c/r))).trans (ramp_lip _ _)
    have h₃ : |dist p c/r-dist q c/r| ≤ dist p q/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
      exact div_le_div_of_nonneg_right (abs_dist_sub_le p q c) hr.le
    rw [he] at h₂
    linarith

end
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

theorem center_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (p c : X)
    (hc : c ∈ H) (hd : dist p c ≤ 9*r) : parameter r H p=0 := by
  have he := parameter_le_center r H p c hc
  rw [ramp_zero ((div_le_iff₀ hr).mpr hd)] at he
  linarith [(parameter_bounds r H p).1]

theorem far_one (r : ℝ) (hr : 0 < r) (H : Finset X) (p : X)
    (hd : ∀ c ∈ H, 10*r ≤ dist p c) : parameter r H p=1 := by
  apply le_antisymm (parameter_bounds r H p).2
  apply le_parameter r H p 1 le_rfl
  intro c hc
  rw [ramp_one ((le_div_iff₀ hr).mpr (hd c hc))]

theorem update_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : dist p x ≤ 9*r) : parameter r (HeavyPilot.updateCenters r H x) p=0 :=
  center_zero r hr _ p x (Finset.mem_insert_self _ _) hp

end UniformKServer.HeavyEditRamp

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyEditPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The literal [9,10] auxiliary potential pays heavy-label edits (§07,
Heavy edits). These are pointwise inequalities before any posterior averaging. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset HeavyEditRamp
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

def editCharge (S T : State X Λ r) (p : X) : ℝ := if key S p ≠ key T p then r else 0

omit [Fintype X] in
theorem editCharge_bounds (S T : State X Λ r) (hr : 0 ≤ r) (p : X) :
    editCharge S T p ∈ Set.Icc 0 r := by
  unfold editCharge
  split_ifs <;> constructor <;> linarith

omit [Fintype X] in
theorem inner_edit_payment (S : State X Λ r) (hr : 0 < r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (p : X) (hd : dist p x ≤ 3*r) :
    editCharge S (insert S hr.le x R hR fresh hf) p+
      r*(parameter r (centers (insert S hr.le x R hR fresh hf)) p-parameter r (centers S) p) ≤ 0 := by
  rw [centers_insert,HeavyEditRamp.update_zero r hr _ x p (by linarith)]
  by_cases hc : ∃ c ∈ centers S, dist p c ≤ 10*r
  · obtain ⟨c,hc,hpc⟩ := hc
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hc
    have hcov : covers S l p := by
      refine ⟨hl,?_⟩
      rw [dist_comm] at hpc
      linarith [(S.radius_bounds l hl).1]
    have he := common_region_reused S hr.le x R hR fresh hf p l hcov (by rw [dist_comm]; linarith [hR.1])
    rw [editCharge,ite_eq_right (not_not.mpr he.symm)]
    nlinarith [(parameter_bounds r (centers S) p).1]
  · have ho : parameter r (centers S) p=1 := by
      apply far_one r hr
      intro c hc'
      exact (lt_of_not_ge (fun h => hc ⟨c,hc',h⟩)).le
    rw [ho]
    linarith [(editCharge_bounds S (insert S hr.le x R hR fresh hf) hr.le p).2]

omit [Fintype X] in
theorem mover_edit_payment (S : State X Λ r) (hr : 0 < r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (y : X) :
    editCharge S (insert S hr.le x R hR fresh hf) y+
      r*(parameter r (centers (insert S hr.le x R hR fresh hf)) x-parameter r (centers S) y) ≤
      if 3*r < dist y x then r else 0 := by
  have hz : parameter r (centers (insert S hr.le x R hR fresh hf)) x=0 := by
    rw [centers_insert]
    exact HeavyEditRamp.update_zero r hr _ x x (by rw [dist_self]; positivity)
  by_cases hi : dist y x ≤ 3*r
  · rw [ite_eq_right (not_lt_of_ge hi)]
    have hp := inner_edit_payment S hr x R hR fresh hf y hi
    have hy : parameter r (centers (insert S hr.le x R hR fresh hf)) y=0 := by
      rw [centers_insert]
      exact HeavyEditRamp.update_zero r hr _ x y (by linarith)
    simpa only [hz,hy] using hp
  · rw [ite_eq_left (lt_of_not_ge hi),hz]
    nlinarith [(editCharge_bounds S (insert S hr.le x R hR fresh hf) hr.le y).2,
      (parameter_bounds r (centers S) y).1]

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyProcessEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! End-to-end heavy edits and physical movement, including all no-insertion
cases. The auxiliary potential is the literal [9,10] distance ramp. -/
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords HeavyEditRamp
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem step_mover_payment (S T : State X Λ r) (hr : 0 < r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : Prop) (x : X) (R : ℝ)
    (hR : R∈Set.Icc (16*r) (20*r)) (y : X) :
    editCharge S (step S T hr.le hΛ h x R hR) y+
      r*(parameter r (centers (step S T hr.le hΛ h x R hR)) x-parameter r (centers S) y)≤
      (if HeavySchedule.trigger r h (centers S) x ∧ 3*r<dist y x then r else 0)+
        (if h then 0 else dist x y) := by
  by_cases hi : HeavySchedule.trigger r h (centers S) x
  · have hh : h := hi.1
    simp only [step,hi,ite_true, if_true,true_and,ite_eq_left hh,add_zero]
    exact mover_edit_payment S hr x R hR (fresh S T hr.le hΛ) (fresh_absent S T hr.le hΛ).1 y
  · simp only [step,hi,ite_false, if_false,false_and,zero_add,editCharge,ne_eq,not_true_eq_false]
    by_cases hh : h
    · rw [ite_eq_left hh]
      have hc : ∃ c∈centers S, dist x c≤8*r := by
        by_contra hn
        apply hi
        refine ⟨hh,?_⟩
        push Not at hn
        exact hn
      obtain ⟨c,hc,hd⟩ := hc
      rw [center_zero r hr (centers S) x c hc (by linarith)]
      exact mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith [(parameter_bounds r (centers S) y).1])
    · rw [ite_eq_right hh]
      have hp := (le_abs_self (parameter r (centers S) x-parameter r (centers S) y)).trans
        (parameter_lip r hr (centers S) x y)
      have hb := mul_le_mul_of_nonneg_left hp hr.le
      have he : r*(dist x y/r)=dist x y := by field_simp
      simpa only [he] using hb

theorem run_mover_payment (a : X) (hr : 0 < r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : ℕ→Prop) (x : ℕ→X)
    (R : ℕ→ℝ) (hR : ∀ t, R t∈Set.Icc (16*r) (20*r)) (t : ℕ) (y : X) :
    editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) y+
      r*(parameter r (HeavySchedule.centers r h x (t+1)) (x t)-parameter r (HeavySchedule.centers r h x t) y)≤
      (if HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) ∧
        3*r<dist y (x t) then r else 0)+(if h t then 0 else dist (x t) y) := by
  have hp := step_mover_payment (run a hr.le hΛ h x R hR t)
    (runPair a hr.le hΛ h x R hR t).1 hr hΛ (h t) (x t) (R t) (hR t) y
  change editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) y+
    r*(parameter r (centers (run a hr.le hΛ h x R hR (t+1))) (x t)-
      parameter r (centers (run a hr.le hΛ h x R hR t)) y)≤_ at hp
  simpa only [run_centers] using hp

end UniformKServer.HeavyProcess

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelHeavyEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Heavy key edits on the actual tape, with a tape-independent auxiliary ramp. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqHeavyEdit_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqHeavyEdit : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)

def heavyPotential (D : Data X N H) (t : ℕ) (p : X) : ℝ :=
  HeavyEditRamp.parameter D.r (HeavySchedule.centers D.r D.heavyFlag D.point t) p

def heavyTrigger (D : Data X N H) (n : Fin N) : Prop :=
  HeavySchedule.trigger D.r (D.heavyFlag n.val)
    (HeavySchedule.centers D.r D.heavyFlag D.point n.val) (D.point n.val)

local instance pairDecEqHeavyEdit_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def heavyEdit (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) : ℝ :=
  indicator (D.heavyKey ω n.val p) (D.heavyKey ω (n.val+1) p)

theorem heavyEdit_le (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) :
    D.r*D.heavyEdit n p ω≤HeavyRecords.editCharge (D.heavyState ω.1 n.val) (D.heavyState ω.1 (n.val+1)) p := by
  have h := mul_le_mul_of_nonneg_left (indicator_map (Option.map (Sum.inl : HeavySlot X→Label D))
    (HeavyRecords.key (D.heavyState ω.1 n.val) p) (HeavyRecords.key (D.heavyState ω.1 (n.val+1)) p)) D.positive.le
  change D.r*D.heavyEdit n p ω≤_ at h
  apply h.trans_eq
  unfold indicator HeavyRecords.editCharge
  split_ifs <;> simp_all

theorem heavyFlag_at (D : Data X N H) (n : Fin N) : D.heavyFlag n.val↔D.heavy n := by
  constructor
  · rintro ⟨_,hh⟩; exact hh
  · exact fun h=>⟨n.isLt,h⟩

theorem heavy_mover (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) :
    D.r*(D.heavyEdit n p ω+D.heavyPotential (n.val+1) (D.center n)-D.heavyPotential n.val p)≤
      (if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p then D.r else 0)+
        (if D.heavy n then 0 else dist (D.center n) p) := by
  have h := HeavyProcess.run_mover_payment D.base D.positive
    (show 2*Fintype.card X<Fintype.card (HeavySlot X) by simp [HeavySlot])
    D.heavyFlag D.point (HeavyProcess.radiusStream D.r N ω.1)
    (HeavyProcess.radiusStream_bounds D.r D.positive.le N ω.1) n.val p
  change HeavyRecords.editCharge (D.heavyState ω.1 n.val) (D.heavyState ω.1 (n.val+1)) p+
    D.r*(D.heavyPotential (n.val+1) (D.point n.val)-D.heavyPotential n.val p)≤
      (if D.heavyTrigger n ∧ 3*D.r<dist p (D.point n.val) then D.r else 0)+
        (if D.heavyFlag n.val then 0 else dist (D.point n.val) p) at h
  rw [point_at,dist_comm p,heavyFlag_at] at h
  nlinarith only [h,D.heavyEdit_le n p ω]

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PiIntegrate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for an arbitrary function on the same finite independent tape.
The one-coordinate ledger may depend on every other coordinate. -/
noncomputable section
namespace UniformKServer.FiniteProbability

section
open Finset
open scoped Classical
variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]
local instance restDecEq (i : I) : DecidableEq {j : I // j ≠ i} :=
  fun a b => Classical.propDecidable (a=b)

theorem Law.expect_pi_split (P : ∀ i, Law (A i)) (i : I) (f : (∀ i, A i)→ℝ) :
    (Law.pi P).expect f =
      (Law.pi (fun j : {j // j≠i} => P j.val)).expect
        (fun b => (P i).expect (fun a => f ((Equiv.piSplitAt i A).symm (a,b)))) := by
  let e := Equiv.piSplitAt i A
  have hweight (x : A i × (∀ j : {j // j ≠ i}, A j.val)) :
      (Law.pi P).weight (e.symm x) = (P i).weight x.1 *
        ∏ j : {j // j ≠ i}, (P j.val).weight (x.2 j) := by
    change (∏ j, (P j).weight (e.symm x j))=_
    rw [←mul_prod_erase _ _ (mem_univ i)]
    have h0 : e.symm x i=x.1 := by simp [e,Equiv.piSplitAt]
    rw [h0]
    congr 1
    rw [Finset.prod_subtype (p:=fun j : I => j ≠ i) (univ.erase i) (by simp [eq_comm])]
    apply prod_congr rfl
    intro j _
    simp [e,Equiv.piSplitAt,j.property]
  unfold Law.expect
  rw [←e.symm.sum_comp,Fintype.sum_prod_type]
  simp only [Law.pi,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  change (Law.pi P).weight (e.symm (a,b))*f (e.symm (a,b))=_
  rw [hweight]
  dsimp only [e]
  ring

theorem Law.expect_pi_fiber_le (P : ∀ i, Law (A i)) (i : I) (f : (∀ i, A i)→ℝ)
    (c : ℝ) (h : ∀ b, (P i).expect (fun a => f ((Equiv.piSplitAt i A).symm (a,b))) ≤ c) :
    (Law.pi P).expect f ≤ c := by
  rw [Law.expect_pi_split P i f]
  exact ((Law.pi _).expect_mono _ (fun _=>c) h).trans_eq (Law.expect_const _ _)

end

section
open Finset
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem Law.expect_prod_reverse (P : Law Ω) (Q : Law Γ) (f : Ω→Γ→ℝ) :
    (P.prod Q).expect (fun z=>f z.1 z.2)=Q.expect (fun b=>P.expect (fun a=>f a b)) := by
  simp only [Law.expect,Law.prod,Fintype.sum_prod_type,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

end

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
theorem Law.expect_pair (P : Law Ω) (Q : Law Γ) (f : Ω×Γ→ℝ) :
    (P.prod Q).expect f=P.expect (fun a=>Q.expect (fun b=>f (a,b))) :=
  Law.expect_prod P Q (fun a b=>f (a,b))
theorem Law.expect_pair_reverse (P : Law Ω) (Q : Law Γ) (f : Ω×Γ→ℝ) :
    (P.prod Q).expect f=Q.expect (fun b=>P.expect (fun a=>f (a,b))) :=
  Law.expect_prod_reverse P Q (fun a b=>f (a,b))
end UniformKServer.FiniteProbability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierFrozen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Noninsertions change no actual tier key, including its recycled label. -/
noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance indexDecEqFrozen_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqFrozen_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem frozen (r : ℝ) (K : ℕ) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : ¬TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N→TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    key r K q c (n.val+1) τ ω p=key r K q c n.val τ ω p := by
  have hb : TierLabels.birth r K q c n.val=none := by
    rw [TierLabels.birth,dite_eq_left n.isLt,ite_eq_right hn]
  have hl := @CooldownLabels.label_none (Fin N) (instDecidableEqFin N)
    (Fintype.card X*K^2) (TierLabels.reserved r K q c) (TierLabels.birth r K q c) n.val hb
  have hv : TierLifetimes.live r K q c (n.val+1) τ=TierLifetimes.live r K q c n.val τ := by
    rw [TierLifetimes.live,dite_eq_left n.isLt,ite_eq_right hn]
  unfold key TierKeyProcess.key TierLabels.labels
  rw [hl,hv]

end UniformKServer.TierLabeledKeys
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqFrozen_rc42fe4_2 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqFrozen_rc42fe4_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqFrozen_rc42fe4_2 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem uncovered_difference {I : Type*} (a b : Option I) :
    KeyEdits.uncovered a-KeyEdits.uncovered b≤ indicator a b := by
  by_cases he : a=b
  · simp only [he,sub_self,indicator,ite_true, if_true,le_refl]
  · have ha := (KeyEdits.uncovered_bounds a).2
    have hb := (KeyEdits.uncovered_bounds b).1
    simp only [indicator,ite_eq_right he]
    linarith

def tierUncovered (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) : ℝ :=
  KeyEdits.uncovered (D.tierKey ω t i p)

theorem tierUncovered_nonneg (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) :
    0≤D.tierUncovered ω t i p := (KeyEdits.uncovered_bounds _).1

theorem tierUncovered_covered (D : Data X N H) (n : Fin N) (i : Fin H)
    (hi : D.qualify i n) (ω : Tape D) : D.tierUncovered ω (n.val+1) i (D.center n)=0 := by
  have h := tier_coverage D n i hi ω
  unfold tierUncovered
  cases hk : D.tierKey ω (n.val+1) i (D.center n) with
  | none => simp [hk] at h
  | some l => rfl

theorem tierUncovered_motion (D : Data X N H) (n : Fin N) (i : Fin H) (y : X) :
    D.r*D.law.expect (fun ω=>D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω (n.val+1) i y)≤
      if D.qualify i n then 0 else (4+2*Real.log (1+(D.K i:ℝ)^2))*dist (D.center n) y := by
  by_cases hq : D.qualify i n
  · rw [ite_eq_left hq]
    have hm := D.law.expect_mono (fun ω=>D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω (n.val+1) i y) (fun _=>0) (fun ω=>by
      rw [tierUncovered_covered D n i hq ω]
      simpa only [zero_sub,neg_nonpos] using tierUncovered_nonneg D ω (n.val+1) i y)
    rw [Law.expect_const] at hm
    exact mul_nonpos_of_nonneg_of_nonpos D.positive.le hm
  · rw [ite_eq_right hq]
    have hlam : 0≤Real.log (1+(D.K i:ℝ)^2) := Real.log_nonneg (by nlinarith [sq_nonneg (D.K i:ℝ)])
    by_cases hd : dist (D.center n) y<D.r/4
    · have hm := D.law.expect_mono _ _ (fun ω=>uncovered_difference
        (D.tierKey ω (n.val+1) i (D.center n)) (D.tierKey ω (n.val+1) i y))
      have hs := mul_le_mul_of_nonneg_left
        (hm.trans (tier_separation D (n.val+1) i (D.center n) y hd)) D.positive.le
      have he : D.r*(2*Real.log (1+(D.K i:ℝ)^2)*dist (D.center n) y/D.r)=
          2*Real.log (1+(D.K i:ℝ)^2)*dist (D.center n) y := by field_simp [ne_of_gt D.positive]
      rw [he] at hs
      exact hs.trans (by nlinarith [dist_nonneg (x:=D.center n) (y:=y)])
    · have hm := D.law.expect_mono (fun ω=>D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω (n.val+1) i y) (fun _=>1) (fun ω=>by
        have ha := (KeyEdits.uncovered_bounds (D.tierKey ω (n.val+1) i (D.center n))).2
        have hb := tierUncovered_nonneg D ω (n.val+1) i y
        change KeyEdits.uncovered _-_≤_
        linarith)
      rw [Law.expect_const] at hm
      have hs := mul_le_mul_of_nonneg_left hm D.positive.le
      have hd' := le_of_not_gt hd
      have hprod := mul_nonneg hlam (dist_nonneg (x:=D.center n) (y:=y))
      nlinarith

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierRetirement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

noncomputable section
namespace UniformKServer.TierRetirement
open FiniteProbability Finset ChronologicalRoster ShortRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [MetricSpace X] {N : ℕ}
local instance pairDecEq_rc42fe4_5 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

def event (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) : Prop :=
  ∃ i, TierKeyProcess.key r K q c n.val τ ω p=some i ∧
    i∈TierLifetimes.live r K q c n.val τ ∧
    i∉retained (ActualRoster.active (TierSchedule.run r K q c n.val) c r K n)
      (ActualRoster.compulsory (TierSchedule.run r K q c n.val) c r K)
      (TierLifetimes.live r K q c n.val τ) (τ n)

end UniformKServer.TierRetirement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierKeyEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Actual roster edits, including the noncoverage credit. The fixed-radius
values are persistent over an insertion, and retirements use the true law. -/
noncomputable section
namespace UniformKServer.TierKeyEdits
open Finset FiniteProbability ShortRoster ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance pairDecEq_rc42fe4_6 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq_rc42fe4_6 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
abbrev RadiusTape (X : Type) [Fintype X] [MetricSpace X] (N K : ℕ) (r : ℝ) :=
  Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r

def keep (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (τ : TierLifetimes.Tape N) (i : Fin N) : Bool :=
  decide (¬ActualRoster.active (TierSchedule.run r K q c n.val) c r K n i ∨
    (¬ActualRoster.compulsory (TierSchedule.run r K q c n.val) c r K i ∧ τ n i=true))

end UniformKServer.TierKeyEdits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelTierEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Actual full-tape one-tier edit estimates. Prefix and suffix may depend
arbitrarily on the tape; the noncoverage ledger is not conditioned on either. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqEdit_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqEdit : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqEdit : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def tierTrigger (D : Data X N H) (n : Fin N) (i : Fin H) : Prop :=
  TierSchedule.trigger D.r (D.K i) (TierSchedule.run D.r (D.K i) (D.qualify i) D.center n.val)
    (D.qualify i) D.center n

def tierEdit (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D) (ω : Tape D) : ℝ :=
  KeyEdits.changed (earlier ω) id (later ω) (D.tierKey ω n.val i p) (D.tierKey ω (n.val+1) i p)

theorem tierEdit_frozen (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (hn : ¬D.tierTrigger n i) (ω : Tape D) :
    D.tierEdit n i p earlier later ω=0 ∧
      D.tierUncovered ω (n.val+1) i p=D.tierUncovered ω n.val i p := by
  have he : D.tierKey ω (n.val+1) i p=D.tierKey ω n.val i p := by
    unfold tierKey
    rw [TierLabeledKeys.frozen D.r (D.K i) (D.qualify i) D.center n hn]
  constructor
  · simp only [tierEdit,he,KeyEdits.changed,ite_true, if_true]
  · unfold tierUncovered; rw [he]

theorem tier_expect_bound (D : Data X N H) (i : Fin H) (f : Tape D→ℝ) (c : ℝ)
    (h : ∀ (heavy : HeavyTape D) (b : ∀ j : {j : Fin H // j≠i}, TierTape D j.val)
      (rad : Fin N→TierRadius.Sample (X:=X) (Real.log (1+(D.K i:ℝ)^2)) D.r),
      (TierLifetimes.law (D.K i) (D.quota i)).expect (fun τ=>
        f (heavy,(Equiv.piSplitAt i (TierTape D)).symm ((τ,rad),b))) ≤ c) :
    D.law.expect f ≤ c := by
  change ((Law.pi fun _:Fin N=>HeavyRadius.law (X:=X) D.r).prod (Law.pi D.tierLaw)).expect _≤_
  rw [Law.expect_pair]
  apply (le_trans ((Law.pi _).expect_mono _ (fun _=>c) _))
  · exact Law.expect_const _ _ |>.le
  intro heavy
  apply Law.expect_pi_fiber_le D.tierLaw i _ c
  intro b
  change ((TierLifetimes.law (D.K i) (D.quota i)).prod _).expect _ ≤ c
  rw [Law.expect_pair_reverse]
  exact ((Law.pi _).expect_mono _ (fun _=>c) (h heavy b)).trans_eq (Law.expect_const _ _)

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelTierLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! The complete one-tier end-to-end ledger; movement is included exactly once.
No-insertion qualified tiers contribute zero, not a spurious per-step cost. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqLedger_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqLedger_rc42fe4_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqLedger_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def errorIndicator (D : Data X N H) (γ : ℝ) (n : Fin N) (p : X) : ℝ :=
  if dist (D.center n) p≤22*D.r ∧ (¬D.heavy n ∨ γ*D.r<dist (D.center n) p) then 1 else 0

def moverBudget (D : Data X N H) (γ : ℝ) (n : Fin N) (i : Fin H) (p : X) : ℝ :=
  if D.tierTrigger n i then 49*D.r/(D.K i:ℝ)*D.errorIndicator γ n p
  else if D.qualify i n then 0 else (4+2*Real.log (1+(D.K i:ℝ)^2))*dist (D.center n) p

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelSerial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The source edit order: first heavy, then tiers in order. Each tier ledger
retains its higher-priority shadow and its old lower-priority suffix. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqSerial_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqSerial_rc42fe4_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqSerial_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def serialEdit (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X)
    (e : Tape D→Option (Label D)) (ω : Tape D) : ℝ :=
  editSum (fun i=>D.tierKey ω n.val i p) (fun i=>D.tierKey ω (n.val+1) i p)
    (Sum.inr (Sum.inr p)) (e ω) is

def tierPotential (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) (ω : Tape D) : ℝ :=
  (is.map fun i=>D.tierUncovered ω t i p).sum

theorem actual_shadow (D : Data X N H) (n : Fin N) (p : X) (γ : ℝ) (hγ : γ≤1/2)
    (hh : D.heavy n) (hp : dist (D.center n) p≤γ*D.r) (ω : Tape D) :
    (D.heavyKey ω (n.val+1) p).isSome=true := by
  obtain ⟨l,_,hl⟩ := D.heavy_agreement n hh ω p (by nlinarith [D.positive])
  simp only [hl,Option.isSome_some]

theorem key_edit_bound (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (ω : Tape D) :
    indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)≤
      D.heavyEdit n p ω+D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω := by
  let z : Label D := Sum.inr (Sum.inr p)
  let f := fun i=>D.tierKey ω n.val i p
  let g := fun i=>D.tierKey ω (n.val+1) i p
  have h := indicator_triangle (D.key is ω n.val p)
    (overlayKey (D.heavyKey ω (n.val+1) p) is f z) (D.key is ω (n.val+1) p)
  have hm := indicator_map (fun e=>overlayKey e is f z)
    (D.heavyKey ω n.val p) (D.heavyKey ω (n.val+1) p)
  have hs := serial_bound (D.heavyKey ω (n.val+1) p) is f g z
  exact h.trans (add_le_add hm hs)

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelKeyLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Full level key edits with the genuine heavy-first serial auxiliary potential. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqKey_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqKey_rc42fe4_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqKey_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def keyPotential (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) (ω : Tape D) : ℝ :=
  D.heavyPotential t p+D.tierPotential is t p ω

def heavyMoverBudget (D : Data X N H) (n : Fin N) (p : X) : ℝ :=
  (if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p then D.r else 0)+
    (if D.heavy n then 0 else dist (D.center n) p)

theorem key_ledger (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p q : X) (a b : ℝ)
    (ha : ∀ ω, D.r*(D.heavyEdit n p ω+D.heavyPotential (n.val+1) q-D.heavyPotential n.val p)≤a)
    (hb : D.r*D.law.expect (fun ω=>D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+
      D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω)≤b) :
    D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)+
      D.keyPotential is (n.val+1) q ω-D.keyPotential is n.val p ω)≤a+b := by
  have he := D.law.expect_mono _ _ ha
  rw [Law.expect_const,Law.expect_mul] at he
  have hbound := mul_le_mul_of_nonneg_left (D.law.expect_mono _ _ (fun ω=>
    add_le_add (D.key_edit_bound n is p ω) (le_refl (D.keyPotential is (n.val+1) q ω-D.keyPotential is n.val p ω)))) D.positive.le
  have hf (ω : Tape D) : D.heavyEdit n p ω+D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+
      (D.keyPotential is (n.val+1) q ω-D.keyPotential is n.val p ω)=
    (D.heavyEdit n p ω+D.heavyPotential (n.val+1) q-D.heavyPotential n.val p)+
    (D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω) := by
    unfold keyPotential; ring
  simp_rw [hf] at hbound
  have hab : D.r*D.law.expect (fun ω=>
      (D.heavyEdit n p ω+D.heavyPotential (n.val+1) q-D.heavyPotential n.val p)+
      (D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω))≤a+b := by
    rw [Law.expect_add,mul_add]
    exact add_le_add he hb
  simpa only [sub_eq_add_neg,add_assoc] using hbound.trans hab

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelMassLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear auxiliary-potential accounting for a stationary submass and one
unit designated mover. The mover is charged separately from post-request mass. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqMassLedger_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqMassLedger_rc42fe4_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMassLedger_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def editCost (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) : ℝ :=
  D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p))

def auxiliary (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) : ℝ :=
  D.r*D.law.expect (D.keyPotential is t p)

theorem auxiliary_bounds (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) :
    0≤D.auxiliary is t p ∧ D.auxiliary is t p≤D.r*(1+is.length) := by
  have hp (ω : Tape D) : 0≤D.keyPotential is t p ω ∧ D.keyPotential is t p ω≤1+is.length := by
    have hh : D.heavyPotential t p∈Set.Icc (0:ℝ) 1 := HeavyEditRamp.parameter_bounds _ _ _
    have ht : 0≤D.tierPotential is t p ω ∧ D.tierPotential is t p ω ≤ is.length := by
      induction is with
      | nil => simp [tierPotential]
      | cons i is ih =>
        have hti : 0≤D.tierUncovered ω t i p ∧ D.tierUncovered ω t i p≤1 := by
          exact KeyEdits.uncovered_bounds _
        simp only [tierPotential,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
        constructor <;> linarith
    unfold keyPotential
    constructor <;> linarith [hh.1,hh.2,ht.1,ht.2]
  constructor
  · exact mul_nonneg D.positive.le (D.law.expect_nonneg _ (fun ω=>(hp ω).1))
  · apply mul_le_mul_of_nonneg_left _ D.positive.le
    calc
      _≤D.law.expect (fun _=>1+(is.length:ℝ)) := D.law.expect_mono _ _ (fun ω=>(hp ω).2)
      _=_ := Law.expect_const _ _

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalLevelAux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The integrated auxiliary function is adapted to the old request history. -/
namespace UniformKServer.LevelMap.Data
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance ixCA_rc42fe4_1 : DecidableEq (Fin N) := fun a b=>Classical.propDecidable (a=b)
local instance iyCA_rc42fe4_1 : DecidableEq (Fin H) := fun a b=>Classical.propDecidable (a=b)
local instance pairCA_rc42fe4_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
lemma heavyPotential_inputs (D : Data X N H) (c d : Fin N→X)
    (h v : Fin N→Prop) (q u : Fin H→Fin N→Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t→c i=d i) (hh : ∀ i : Fin N, i.val<t→(h i↔v i)) (p : X) :
    (D.inputs c h q).heavyPotential t p=(D.inputs d v u).heavyPotential t p := by
  unfold heavyPotential
  congr 1
  apply HeavyProcess.centers_inputs
  · intro j hj
    simp only [heavyFlag,inputs]
    apply exists_congr
    intro hjN
    exact hh ⟨j,hjN⟩ hj
  · exact fun j hj=>point_inputs D c d h v q u t hc j hj

lemma auxiliary_inputs (D : Data X N H) (c d : Fin N→X)
    (h v : Fin N→Prop) (q u : Fin H→Fin N→Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t→c i=d i) (hh : ∀ i : Fin N, i.val<t→(h i↔v i))
    (hq : ∀ a (i : Fin N), i.val<t→(q a i↔u a i)) (is : List (Fin H)) (p : X) :
    (D.inputs c h q).auxiliary is t p=(D.inputs d v u).auxiliary is t p := by
  have he (ω : Tape D) : (D.inputs c h q).keyPotential is t p ω=
      (D.inputs d v u).keyPotential is t p ω := by
    unfold keyPotential
    rw [heavyPotential_inputs D c d h v q u t hc hh p]
    congr 1
    unfold tierPotential
    congr 1
    apply List.map_congr_left
    intro i _
    unfold tierUncovered tierKey inputs
    rw [CausalRosters.labeled_inputs D.r (D.K i) (q i) (u i) c d t (hq i) hc]
  unfold auxiliary
  congr 1
  exact congrArg D.law.expect (funext he)

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Actual admissible pilot templates; no drift/pilot premise is added to the
partition construction. The constants are independent of the finite law. -/
noncomputable section
namespace UniformKServer.PilotEdits
open PilotCompact

def smallGamma (σ L : ℝ) : ℝ := min (σ/64) (1/(1+L))

theorem smallGamma_pos (σ L : ℝ) (hσ : 0<σ) (hL : 0≤L) : 0 < smallGamma σ L := by
  unfold smallGamma
  apply lt_min <;> positivity

def scaleShift (σ R L : ℝ) : ℕ := ⌈100*R/smallGamma σ L⌉₊

theorem shift_valid (σ R L : ℝ) (hσ : 0<σ) (hL : 0≤L) :
    100*R ≤ smallGamma σ L*(2:ℝ)^scaleShift σ R L := by
  have hg := smallGamma_pos σ L hσ hL
  have hc := Nat.le_ceil (100*R/smallGamma σ L)
  have hp : (scaleShift σ R L:ℝ)≤(2:ℝ)^scaleShift σ R L := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self) : scaleShift σ R L≤(2:ℕ)^scaleShift σ R L)
  have ht : 100*R/smallGamma σ L≤(2:ℝ)^scaleShift σ R L := hc.trans hp
  simpa only [mul_comm] using (div_le_iff₀ hg).mp ht

def template (σ R L : ℝ) (hσ : 0<σ) (hσ1 : σ≤1) (hR : 256≤R) (hL : 0≤L) : Template where
  sigma := σ
  R := R
  gamma := smallGamma σ L
  delta := 1/4112
  L := L
  shift := scaleShift σ R L
  sigma_pos := hσ
  sigma_le_one := hσ1
  R_large := hR
  L_nonneg := hL
  gamma_pos := smallGamma_pos σ L hσ hL
  gamma_sigma := min_le_left _ _
  gamma_L := min_le_right _ _
  delta_pos := by norm_num
  delta_small := le_rfl
  shift_large := shift_valid σ R L hσ hL

def heavyTemplate : Template := template 1 512 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def shortTemplate (P : TierPilot.Parameters) : Template :=
  template P.sigma 204800 8 P.sigma_pos P.sigma_le_one (by norm_num) (by norm_num)

end UniformKServer.PilotEdits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Adapted linear auxiliary family for the literal multiscale partition. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def auxiliary (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (p : X) : ℝ :=
  ∑ j∈range J,((A.input (N:=N) (J:=J) D hk ω).level j).data.auxiliary
    ((A.input (N:=N) (J:=J) D hk ω).level j).order t p

def auxiliaryCap (A : Config X) (k J : ℕ) : ℝ :=
  (1+((DyadicTiers.last (Real.log k)+1:ℕ):ℝ))*(∑ j∈range J,GeometricMass.radius A.R A.q j)

theorem level_auxiliary_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v) (p : X) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).data.auxiliary ((A.input (N:=N) (J:=J) D hk ω).level j).order t p=
      ((A.input (N:=N) (J:=J) D hk v).level j).data.auxiliary ((A.input (N:=N) (J:=J) D hk v).level j).order t p := by
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j).data
  let V := ((A.input (N:=N) (J:=J) D hk v).level j).data
  exact LevelMap.Data.auxiliary_inputs I I.center V.center I.heavy V.heavy I.qualify V.qualify t
    (A.past_centers (J:=J) D hk ω v t he) (A.past_heavy (J:=J) D hk ω v t j he)
    (A.past_qualify (J:=J) D hk ω v t j he) _ p

theorem auxiliary_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    A.auxiliary (N:=N) (J:=J) D hk t ω=A.auxiliary (N:=N) (J:=J) D hk t v := by
  funext p
  apply sum_congr rfl
  intro j _
  exact A.level_auxiliary_measurable D hk ω v t j he p

theorem auxiliary_bounds (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (p : X) :
    0≤A.auxiliary (N:=N) (J:=J) D hk t ω p ∧
      A.auxiliary (N:=N) (J:=J) D hk t ω p≤A.auxiliaryCap k J := by
  let I := A.input (N:=N) (J:=J) D hk ω
  have hb (j : ℕ) := (I.level j).data.auxiliary_bounds (I.level j).order t p
  constructor
  · exact sum_nonneg (fun j _=>(hb j).1)
  · unfold auxiliary auxiliaryCap
    have h := sum_le_sum (s:=range J) (fun j _=>(hb j).2)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [I] at *
    simp only [PartitionLevel.Input.order,List.length_ofFn,PartitionLevel.Input.height,
      PartitionScales.Input.level,ActualPartitions.Config.input,PartitionLevel.Input.data,←sum_mul]
    ring

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierShortSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Deterministic expected short-roster functions on the actual chronological
insertion records. These auxiliary experiments never select actual keys. -/
noncomputable section
namespace UniformKServer.TierShortSchedule
open Finset ShortRoster ChronologicalRoster
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

def run (r : ℝ) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) : ℕ → State (Fin N)
  | 0 => State.empty
  | t+1 => if ht : t<N then
      if TierSchedule.trigger r K (TierSchedule.run r K q c t) q c ⟨t,ht⟩ then
        (run r K s hs q c t).next (TierSchedule.run r K q c t) c r K s hs ⟨t,ht⟩
      else run r K s hs q c t
    else run r K s hs q c t

def parameter (r : ℝ) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : X → ℝ :=
  (run r K s hs q c t).parameter c r

end UniformKServer.TierShortSchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualLevelPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

                                                                         
                                                                 
noncomputable section
namespace UniformKServer.PartitionLevel.Input
open Finset PilotCompact
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

def longParameter (I : PartitionLevel.Input X N) (t : ℕ) : X→ℝ :=
  HeavyPilot.parameter I.r (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t)

def shortProb (I : PartitionLevel.Input X N) (i : Fin I.height) : ℝ :=
  1/Real.sqrt (I.data.K i:ℝ)

theorem shortProb_bounds (I : PartitionLevel.Input X N) (i : Fin I.height) :
    I.shortProb i∈Set.Icc (0:ℝ) 1 := by
  have hk : (1:ℝ)≤I.data.K i := by exact_mod_cast (show 1≤I.data.K i by have := I.data.two i; omega)
  have hs : 1≤Real.sqrt (I.data.K i:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hk)
  constructor
  · unfold shortProb; positivity
  · exact (div_le_one (by linarith)).mpr hs

def shortParameter (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) : X→ℝ :=
  TierShortSchedule.parameter I.r (I.data.K i) (I.shortProb i) (I.shortProb_bounds i)
    (I.data.qualify i) I.center t

def longCharge (I : PartitionLevel.Input X N) (t : ℕ) : ℝ :=
  if ht : t<N then
    if HeavySchedule.trigger I.r (I.data.heavyFlag t)
        (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t) (I.data.point t) then
      127*I.r*HeavyPilot.annulusMass I.r (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩)
    else 0
  else 0

def shortCharge (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) : ℝ :=
  if ht : t<N then
    if TierSchedule.trigger I.r (I.data.K i) (TierSchedule.run I.r (I.data.K i) (I.data.qualify i) I.center t)
        (I.data.qualify i) I.center ⟨t,ht⟩ then
      I.r*TierPilot.insertionMass I.P I.r (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩)/(I.data.K i:ℝ)
    else 0
  else 0

end UniformKServer.PartitionLevel.Input

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionCausal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Filtration measurability of actual partition keys, anchors, and pilot
parameters, with a common initially sampled finite tape. -/
noncomputable section
namespace UniformKServer.ActualPartitions.Config
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem anchor_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (z : LevelMap.Tape ((A.input (N:=N) (J:=J) D hk ω).level j).data)
    (l : LevelMap.Label ((A.input (N:=N) (J:=J) D hk ω).level j).data) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).data.anchor z t l=
      ((A.input (N:=N) (J:=J) D hk v).level j).data.anchor z t l := by
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j).data
  let V := ((A.input (N:=N) (J:=J) D hk v).level j).data
  exact LevelMap.Data.anchor_inputs I I.center V.center I.heavy V.heavy I.qualify V.qualify t
    (A.past_centers (J:=J) D hk ω v t he) (A.past_heavy (J:=J) D hk ω v t j he)
    (A.past_qualify (J:=J) D hk ω v t j he) z l

end UniformKServer.ActualPartitions.Config

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Uniform finite pilot family constants: the tier weights sum independently
of the number of tiers and of k. -/
namespace UniformKServer.PilotFamily
open Finset PilotEdits

abbrev Index (k : ℕ) := Option (Fin (DyadicTiers.last (Real.log k)+1))

def rateBound (P : TierPilot.Parameters) : ℝ := rate heavyTemplate+2*rate (shortTemplate P)

end UniformKServer.PilotFamily

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The global pilot finance ledger for the literal partition. Constants do not
 depend on the input law, time horizon, or the number of scales. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits PilotCompact
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def pilotParameter (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) : X→ℝ :=
  if j<J then match i with
    | none => ((A.input (N:=N) (J:=J) D hk ω).level (J-1-j)).longParameter t
    | some a => ((A.input (N:=N) (J:=J) D hk ω).level (J-1-j)).shortParameter a t
  else fun _ => 0

def pilotCharge (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) : ℝ :=
  match i with
    | none => ((A.input (N:=N) (J:=J) D hk ω).level j).longCharge t
    | some a => ((A.input (N:=N) (J:=J) D hk ω).level j).shortCharge a t

def totalPilotCharge (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) : ℝ := ∑ i : PilotFamily.Index k, ∑ j∈range J,
      A.pilotCharge (N:=N) (J:=J) D hk t ω i j

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelAllowances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual insertion charges and local logarithmic motion pay the level ledger. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance ixAllow_rc42fe4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairAllow_rc42fe4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def charges (I : Input X N) (n : Fin N) : ℝ :=
  I.longCharge n.val+(I.order.map fun i=>I.shortCharge i n.val).sum

end UniformKServer.PartitionLevel.Input

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualEditCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Full expected key-edit charge, including the actual posterior unit mover. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def editRate (A : Config X) : ℝ := 198/A.P.gammaH+1/Real.log (1+A.P.deltaH)+(8*A.C+24)

def keyEditCost (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) : ℝ :=
  if ht : t<N then ∑ j∈range J, ∑ p,
    HiddenFlow.filtered D t ω p * ((A.input (N:=N) (J:=J) D hk ω).level j).data.editCost
      ⟨t,ht⟩ ((A.input (N:=N) (J:=J) D hk ω).level j).order p else 0

theorem charges_identity (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) (ω : Ω) (n : Fin N) :
    (∑ j∈range J,((A.input (N:=N) (J:=J) D hk ω).level j).charges n)=
      A.totalPilotCharge (N:=N) (J:=J) D hk n.val ω := by
  unfold totalPilotCharge
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_option]
  unfold pilotCharge PartitionLevel.Input.charges PartitionLevel.Input.order
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq]
  rfl

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualEditFinance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Integrated height-free key edits, financed by actual posterior pilots. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

omit [Fintype X] [MetricSpace X] in
theorem editRate_nonneg (A : Config X) : 0≤A.editRate := by
  have hγ := A.P.gammaH_pos
  have hδ : 0<Real.log (1+A.P.deltaH) := Real.log_pos (by linarith [A.P.deltaH_pos])
  unfold editRate
  have hC : 0≤8*A.C+24 := by linarith [A.C_one]
  positivity

def editBound (A : Config X) : ℝ := 147*PilotFamily.rateBound A.P+A.editRate

def editEndpoint (A : Config X) (k J : ℕ) : ℝ :=
  882*k*(∑ j∈range J,GeometricMass.radius A.R A.q j)+k*A.auxiliaryCap k J

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Exact coarse held-size schedule in companion §03. The deterministic
potential below pays relative refreshes and both hysteretic on/off transitions
from variation of the underlying persistent rank estimates. In particular it
does not restart any initialization allowance when a child becomes active. -/
namespace UniformKServer.AllocationSchedule
noncomputable section
open Finset

def compared (δ b x : ℝ) : Prop := x ≤ (1+δ)*b ∧ b ≤ (1+δ)*x

def relativeUpdate (δ b x : ℝ) : ℝ := by
  classical
  exact if compared δ b x then b else x

def size : Option ℝ → ℝ
  | none => 0
  | some b => b

def update (c δ : ℝ) (s : Option ℝ) (x : ℝ) : Option ℝ :=
  match s with
  | none => if 5*c ≤ x then some x else none
  | some b => if x ≤ 2*c then none else some (relativeUpdate δ b x)

theorem relative_nonneg {δ b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    0 ≤ relativeUpdate δ b x := by unfold relativeUpdate; split <;> assumption

theorem relative_compared {δ b x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    compared δ (relativeUpdate δ b x) x := by
  unfold relativeUpdate
  split
  · assumption
  · constructor <;> nlinarith

theorem update_nonneg {c δ : ℝ} (s : Option ℝ) {x : ℝ}
    (hs : 0 ≤ size s) (hx : 0 ≤ x) : 0 ≤ size (update c δ s x) := by
  cases s with
  | none =>
    simp only [update]
    split
    · exact hx
    · exact le_refl _
  | some b =>
    simp only [update]
    split
    · simp [size]
    · exact relative_nonneg hs hx

def schedule (c δ : ℝ) (x : ℕ → ℝ) : ℕ → Option ℝ
  | 0 => update c δ none (x 0)
  | t+1 => update c δ (schedule c δ x t) (x (t+1))

theorem schedule_nonneg {c δ : ℝ} {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) :
    ∀ t, 0 ≤ size (schedule c δ x t) := by
  intro t
  induction t with
  | zero => exact update_nonneg none (le_refl _) (hx 0)
  | succ t ih => exact update_nonneg _ ih (hx (t+1))

/-- A single relative-held reference, used for the parent and for one side epoch. -/
def held (δ : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | t+1 => relativeUpdate δ (held δ x t) (x (t+1))

theorem held_compared {δ : ℝ} {x : ℕ → ℝ} (hδ : 0 ≤ δ) (hx : ∀ t, 0 ≤ x t)
    (t : ℕ) : compared δ (held δ x t) (x t) := by
  cases t with
  | zero => constructor <;> dsimp [held] <;> nlinarith [hx 0]
  | succ t => exact relative_compared hδ (hx (t+1))

theorem update_inactive {c δ x : ℝ} (hc : 0 ≤ c) (s : Option ℝ)
    (h : update c δ s x=none) : x ≤ 5*c := by
  cases s with
  | none =>
    simp only [update] at h
    split at h
    · contradiction
    · rename_i hx
      exact (lt_of_not_ge hx).le
  | some b =>
    simp only [update] at h
    split at h
    · linarith
    · contradiction

theorem update_active {c δ x b : ℝ} (_hc : 0 ≤ c) (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    (s : Option ℝ) (h : update c δ s x=some b) :
    compared δ b x ∧ 2*c ≤ x := by
  cases s with
  | none =>
    simp only [update] at h
    split at h
    · have hxb : x=b := Option.some.inj h
      subst b
      constructor
      · constructor <;> nlinarith
      · linarith
    · contradiction
  | some a =>
    simp only [update] at h
    split at h
    · contradiction
    · have hab : relativeUpdate δ a x=b := Option.some.inj h
      subst b
      exact ⟨relative_compared hδ hx,by linarith⟩

end
end UniformKServer.AllocationSchedule

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CoarseData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Persistent size/core elementary trackers, and their actual held active
 states.  Constants and initialization allowances are uniform in the law and
 horizon. Companion §03, equations active-size-accuracy and coarse-data-budget. -/
noncomputable section
namespace UniformKServer.CoarseData
open Finset RankTracking RankData
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def sizeEstimate (I : A → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, estimate (I a) sizeRank δ t ω

theorem sizeEstimate_nonneg (I : A → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ sizeEstimate I δ t ω := by
  exact sum_nonneg fun a _ => sizeRank_nonneg _

theorem sizeEstimate_comparison (I : A → Input Ω) {δ : ℝ} (hδ : 0 < δ)
    (t : ℕ) (ω : Ω) :
    (1+δ)⁻¹ * totalSize (fun a => (I a).posterior t ω) ≤ sizeEstimate I δ t ω ∧
    sizeEstimate I δ t ω ≤ (1+δ) * totalSize (fun a => (I a).posterior t ω) := by
  have he (a : A) := estimate_spec (I a) sizeRank δ hδ (fun p _ => sizeRank_nonneg p) t ω
  constructor
  · rw [sizeEstimate,totalSize,mul_sum]
    exact sum_le_sum fun a _ => (he a).1
  · rw [sizeEstimate,totalSize,mul_sum]
    exact sum_le_sum fun a _ => (he a).2

def sizeTolerance : ℝ := 1/1000
def cutoff : ℝ := 1/10000

def activeState (I : A → Input Ω) (t : ℕ) (ω : Ω) : Option ℝ :=
  AllocationSchedule.schedule cutoff sizeTolerance (fun s => sizeEstimate I sizeTolerance s ω) t

def heldSize (I : A → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  AllocationSchedule.size (activeState I t ω)

theorem heldSize_nonneg (I : A → Input Ω) (t : ℕ) (ω : Ω) : 0 ≤ heldSize I t ω :=
  AllocationSchedule.schedule_nonneg (fun s => sizeEstimate_nonneg I sizeTolerance s ω) t

theorem activeState_update (I : A → Input Ω) (t : ℕ) (ω : Ω) :
    ∃ s, activeState I t ω = AllocationSchedule.update cutoff sizeTolerance s
      (sizeEstimate I sizeTolerance t ω) := by
  cases t with
  | zero => exact ⟨none,rfl⟩
  | succ t => exact ⟨activeState I t ω,rfl⟩

theorem active_accuracy (I : A → Input Ω) (t : ℕ) (ω : Ω) {b : ℝ}
    (hb : activeState I t ω = some b) :
    (9/10)*totalSize (fun a => (I a).posterior t ω) ≤ b ∧
    b ≤ (11/10)*totalSize (fun a => (I a).posterior t ω) ∧
    cutoff ≤ totalSize (fun a => (I a).posterior t ω) := by
  obtain ⟨s,hs⟩ := activeState_update I t ω
  rw [hs] at hb
  have hd := AllocationSchedule.update_active (by norm_num [cutoff])
    (by norm_num [sizeTolerance]) (sizeEstimate_nonneg I sizeTolerance t ω) s hb
  have hm := sizeEstimate_comparison I (show 0 < sizeTolerance by norm_num [sizeTolerance]) t ω
  have hn : 0 ≤ totalSize (fun a => (I a).posterior t ω) := sum_nonneg fun a _ => sizeRank_nonneg _
  norm_num [sizeTolerance,cutoff,AllocationSchedule.compared] at *
  constructor
  · linarith
  constructor <;> linarith

theorem inactive_small (I : A → Input Ω) (t : ℕ) (ω : Ω)
    (hb : activeState I t ω = none) :
    totalSize (fun a => (I a).posterior t ω) ≤ 10*cutoff := by
  obtain ⟨s,hs⟩ := activeState_update I t ω
  rw [hs] at hb
  have hd := AllocationSchedule.update_inactive (by norm_num [cutoff]) s hb
  have hm := (sizeEstimate_comparison I (show 0 < sizeTolerance by norm_num [sizeTolerance]) t ω).1
  norm_num [sizeTolerance,cutoff] at *
  linarith

theorem inactive_zero (I : A → Input Ω) (t : ℕ) (ω : Ω) (β : ℝ)
    (hb : activeState I t ω = none) :
    coreCount (fun a => core (I a) t ω) = 0 ∧
    totalRank β (fun a => (I a).posterior t ω) = 0 ∧
    flex (fun a => core (I a) t ω) β (fun a => (I a).posterior t ω) = 0 := by
  apply inactive_ranks
  · intro a ha
    have := core_small (I a) t ω ha
    norm_num [RankFunctions.pstar] at *
    linarith
  · have := inactive_small I t ω hb
    norm_num [cutoff] at *
    exact this

end UniformKServer.CoarseData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FineCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! Companion §03, fine cap algebra.  The tolerance hypotheses below are the
actual absolute choices in Lemma caps; there is no assumed cap feasibility. -/
namespace UniformKServer.FineCaps
noncomputable section
open Finset

/-- Convex interpolation preserves the same multiplicative endpoint error. -/
theorem interpolate {a b A B c ξ : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1)
    (ha : (1+ξ)⁻¹*a ≤ A ∧ A ≤ (1+ξ)*a)
    (hb : (1+ξ)⁻¹*b ≤ B ∧ B ≤ (1+ξ)*b) :
    (1+ξ)⁻¹*((1-c)*a+c*b) ≤ (1-c)*A+c*B ∧
      (1-c)*A+c*B ≤ (1+ξ)*((1-c)*a+c*b) := by
  have h0 : 0 ≤ 1-c := by linarith [hc.2]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 h0,
      mul_le_mul_of_nonneg_left hb.1 hc.1]
  · nlinarith [mul_le_mul_of_nonneg_left ha.2 h0,
      mul_le_mul_of_nonneg_left hb.2 hc.1]

theorem regular_factor {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hy' : y ≤ x/4) :
    1-2*x ≤ (1-x)*(1-y) ∧ (1-x)*(1+y) ≤ 1 := by
  constructor <;> nlinarith [mul_nonneg hx hy]

theorem dominant_factor {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/4)
    (hy : 0 ≤ y) (hy' : y ≤ x/4) :
    1 ≤ (1+x)*(1-y) ∧ (1+x)*(1+y) ≤ 1+2*x := by
  have hprod : x*y ≤ y/4 := by nlinarith [mul_le_mul_of_nonneg_right hx' hy]
  constructor <;> nlinarith

/-- Both explicit factors at once, including zero true flexible mass. -/
theorem caps {ell lam e T F γ ε f : ℝ} (hell : 1 ≤ ell)
    (hlam : 0 ≤ lam) (hlam' : lam ≤ 1/4) (he : 0 ≤ e) (he' : e ≤ lam/4)
    (hγ : 4*lam ≤ γ) (hε : 4*lam ≤ ε) (hT : 0 ≤ T)
    (hF : |F-T| ≤ (e/ell)*T) (hf : f ≤ (1-γ/ell)*T) :
    (f ≤ (1-lam/ell)*F ∧ (1-lam/ell)*F ≤ T) ∧
      (T ≤ (1+lam/ell)*F ∧ (1+lam/ell)*F ≤ (1+ε/ell)*T) := by
  have hell0 : 0 < ell := by linarith
  have hx : 0 ≤ lam/ell := div_nonneg hlam hell0.le
  have hx' : lam/ell ≤ 1/4 := by
    apply (div_le_iff₀ hell0).2
    nlinarith
  have hy : 0 ≤ e/ell := div_nonneg he hell0.le
  have hy' : e/ell ≤ (lam/ell)/4 := by
    apply (div_le_iff₀ hell0).2
    rw [div_mul_eq_mul_div,div_mul_cancel₀ _ (ne_of_gt hell0)]
    exact he'
  have hFlo : (1-e/ell)*T ≤ F := by linarith [(abs_le.mp hF).1]
  have hFhi : F ≤ (1+e/ell)*T := by linarith [(abs_le.mp hF).2]
  have hra := regular_factor hx hy hy'
  have hda := dominant_factor hx hx' hy hy'
  have hγ' : 2*(lam/ell) ≤ γ/ell := by
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hell0.le
  have hε' : 2*(lam/ell) ≤ ε/ell := by
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hell0.le
  have hrlo := mul_le_mul_of_nonneg_left hFlo (by linarith : 0 ≤ 1-lam/ell)
  have hrhi := mul_le_mul_of_nonneg_left hFhi (by linarith : 0 ≤ 1-lam/ell)
  have hdlo := mul_le_mul_of_nonneg_left hFlo (by linarith : 0 ≤ 1+lam/ell)
  have hdhi := mul_le_mul_of_nonneg_left hFhi (by linarith : 0 ≤ 1+lam/ell)
  have hrT := mul_le_mul_of_nonneg_right hra.1 hT
  have hrT' := mul_le_mul_of_nonneg_right hra.2 hT
  have hdT := mul_le_mul_of_nonneg_right hda.1 hT
  have hdT' := mul_le_mul_of_nonneg_right hda.2 hT
  have hγT := mul_le_mul_of_nonneg_right hγ' hT
  have hεT := mul_le_mul_of_nonneg_right hε' hT
  constructor <;> constructor <;> nlinarith only [hf,hrlo,hrhi,hdlo,hdhi,hrT,hrT',hdT,hdT',hγT,hεT]

end
end UniformKServer.FineCaps

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlexEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Persistent endpoint interpolation of the noncore ranks and its true
parameter error. The endpoints and the tolerance are the manuscript's ones. -/
noncomputable section
namespace UniformKServer.FlexEstimates
open Finset RankFunctions RankData RankTracking
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def mix (β : ℝ) : ℝ := 100*(β-3)

theorem mix_range {β : ℝ} (hβ : allowed β) : mix β ∈ Set.Icc (0:ℝ) 1 := by
  norm_num [allowed,mix] at *
  constructor <;> linarith [hβ.1,hβ.2]

theorem rank_mix (β p : ℝ) :
    rank β p = (1-mix β)*rank 3 p+mix β*rank (3+1/100) p := by
  rw [rank_affine β,rank_affine (3+1/100)]
  unfold mix
  ring

def term (I : Input Ω) (β ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (1-mix β)*estimate I (rank 3) ξ t ω+
    mix β*estimate I (rank (3+1/100)) ξ t ω

def estimateFlex (I : A → Input Ω) (β ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if core (I a) t ω then 0 else term (I a) β ξ t ω

def trueFlex (I : A → Input Ω) (β : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  flex (fun a => core (I a) t ω) β (fun a => (I a).posterior t ω)

theorem endpoint_range (I : Input Ω) {β : ℝ} (hβ : allowed β) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    estimate I (rank β) ξ t ω ∈ Set.Icc (0:ℝ) 1 :=
  ⟨rank_nonneg hβ,rank_le_one hβ (reference_range I (rank β) ξ t ω).1⟩

theorem term_range (I : Input Ω) {β : ℝ} (hβ : allowed β) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    term I β ξ t ω ∈ Set.Icc (0:ℝ) 1 := by
  have h0 := endpoint_range I (show allowed 3 by norm_num [allowed]) ξ t ω
  have h1 := endpoint_range I (show allowed (3+1/100) by norm_num [allowed]) ξ t ω
  have hm := mix_range hβ
  have hm' : 0 ≤ 1-mix β := by linarith [hm.2]
  constructor
  · exact add_nonneg (mul_nonneg hm' h0.1) (mul_nonneg hm.1 h1.1)
  · dsimp [term]
    have h := add_le_add (mul_le_mul_of_nonneg_left h0.2 hm')
      (mul_le_mul_of_nonneg_left h1.2 hm.1)
    nlinarith only [h]

theorem term_comparison (I : Input Ω) {β ξ : ℝ} (hβ : allowed β) (hξ : 0 < ξ)
    (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*rank β (I.posterior t ω) ≤ term I β ξ t ω ∧
    term I β ξ t ω ≤ (1+ξ)*rank β (I.posterior t ω) := by
  rw [rank_mix β]
  exact FineCaps.interpolate (mix_range hβ)
    (estimate_spec I (rank 3) ξ hξ (fun _ _ => rank_nonneg (by norm_num [allowed])) t ω)
    (estimate_spec I (rank (3+1/100)) ξ hξ (fun _ _ => rank_nonneg (by norm_num [allowed])) t ω)

theorem flex_comparison (I : A → Input Ω) {β ξ : ℝ} (hβ : allowed β) (hξ : 0 < ξ)
    (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*trueFlex I β t ω ≤ estimateFlex I β ξ t ω ∧
    estimateFlex I β ξ t ω ≤ (1+ξ)*trueFlex I β t ω := by
  unfold trueFlex flex estimateFlex
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro a _
    split_ifs
    · simp
    · exact (term_comparison (I a) hβ hξ t ω).1
  · rw [mul_sum]
    apply sum_le_sum
    intro a _
    split_ifs
    · simp
    · exact (term_comparison (I a) hβ hξ t ω).2

def flexGap (I : A → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if core (I a) t ω then 0 else gap ((I a).posterior t ω)

theorem flex_nonneg (I : A → Input Ω) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) :
    0 ≤ trueFlex I β t ω := by
  apply sum_nonneg
  intro a _
  split_ifs
  · rfl
  · exact rank_nonneg hβ

theorem gap_bounds (I : A → Input Ω) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) :
    trueFlex I β t ω/96 ≤ flexGap I t ω ∧ flexGap I t ω ≤ trueFlex I β t ω := by
  have hp (a : A) (ha : core (I a) t ω=false) : pstar/4 ≤ (I a).posterior t ω := by
    have := noncore_large (I a) t ω ha
    norm_num [pstar] at *
    linarith
  unfold trueFlex flex flexGap
  rw [sum_div]
  constructor
  · apply sum_le_sum
    intro a _
    cases ha : core (I a) t ω
    · simpa [ha] using (gap_comparison hβ (hp a ha)).1
    · simp [ha]
  · apply sum_le_sum
    intro a _
    cases ha : core (I a) t ω
    · simpa [ha] using (gap_comparison hβ (hp a ha)).2
    · simp [ha]

theorem flex_affine (I : A → Input Ω) (β γ : ℝ) (t : ℕ) (ω : Ω) :
    trueFlex I γ t ω = trueFlex I β t ω-(γ-β)*flexGap I t ω := by
  unfold trueFlex flex flexGap
  rw [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  split_ifs
  · ring
  · rw [rank_affine γ,rank_affine β]
    ring

theorem relative_error {ξ T F : ℝ} (hξ : 0 ≤ ξ) (hT : 0 ≤ T)
    (h : (1+ξ)⁻¹*T ≤ F ∧ F ≤ (1+ξ)*T) : |F-T| ≤ ξ*T := by
  have hi : 1-ξ ≤ (1+ξ)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1+ξ)).2
    nlinarith [sq_nonneg ξ]
  have hlo := (mul_le_mul_of_nonneg_right hi hT).trans h.1
  exact abs_le.mpr ⟨by nlinarith only [hlo],by nlinarith only [h.2]⟩

theorem parameter_error (I : A → Input Ω) {β γ ξ δ : ℝ}
    (hβ : allowed β) (hγ : allowed γ) (hξ : 0 < ξ)
    (hbg : β ≤ γ) (hgb : γ ≤ β+δ) (t : ℕ) (ω : Ω) :
    |estimateFlex I γ ξ t ω-trueFlex I β t ω| ≤ (ξ+δ)*trueFlex I β t ω := by
  have hg := gap_bounds I hβ t ω
  have hT := flex_nonneg I hβ t ω
  have hG := flex_nonneg I hγ t ω
  have hgap : 0 ≤ flexGap I t ω := le_trans (div_nonneg hT (by norm_num)) hg.1
  have hmul := mul_le_mul_of_nonneg_left hg.2 (sub_nonneg.mpr hbg)
  have hmul' := mul_le_mul_of_nonneg_right (show γ-β ≤ δ by linarith) hT
  have he := flex_affine I β γ t ω
  have hmono : trueFlex I γ t ω ≤ trueFlex I β t ω := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbg) hgap]
  have hd : |trueFlex I γ t ω-trueFlex I β t ω| ≤ δ*trueFlex I β t ω := by
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    nlinarith only [he,hmul,hmul']
  have hr := relative_error hξ.le hG (flex_comparison I hγ hξ t ω)
  calc
    _ ≤ |estimateFlex I γ ξ t ω-trueFlex I γ t ω|+
        |trueFlex I γ t ω-trueFlex I β t ω| := abs_sub_le _ _ _
    _ ≤ ξ*trueFlex I γ t ω+δ*trueFlex I β t ω := add_le_add hr hd
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmono hξ.le]

theorem child_slack (I : A → Input Ω) {β γ g ell : ℝ} (hβ : allowed β)
    (hbg : g/ell ≤ γ-β) (hg : 0 ≤ g) (hell : 0 < ell) (t : ℕ) (ω : Ω) :
    trueFlex I γ t ω ≤ (1-(g/96)/ell)*trueFlex I β t ω := by
  have hG := (gap_bounds I hβ t ω).1
  have hT := flex_nonneg I hβ t ω
  have hbg' : 0 ≤ γ-β := (div_nonneg hg hell.le).trans hbg
  have hmul := mul_le_mul_of_nonneg_left hG hbg'
  have hmul' := mul_le_mul_of_nonneg_right hbg (div_nonneg hT (by norm_num : (0:ℝ) ≤ 96))
  rw [flex_affine I β γ t ω]
  have hid : (g/ell)*(trueFlex I β t ω/96) = ((g/96)/ell)*trueFlex I β t ω := by ring
  rw [hid] at hmul'
  nlinarith only [hmul,hmul']

end UniformKServer.FlexEstimates

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FineVariation
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

def cap (I : A → Input Ω) (β ξ factor : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  coreCount (fun a => core (I a) t ω)+factor*estimateFlex I β ξ t ω

end UniformKServer.FineVariation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParameterGaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Companion §03, coarse epoch parameter gaps.  These explicit constants prove
 the manuscript's uniform logarithmic comparison without a compactness/minimum
 oracle.  Hypotheses are the exact held-size and non-dominance inequalities. -/
namespace UniformKServer.ParameterGaps
noncomputable section

/-- The regular size-log comparison, with an absolute explicit constant. -/
theorem regular_log {x : ℝ} (hx : (50:ℝ)/43 ≤ x) :
    (1+Real.log x)/50 ≤ Real.log (1+(9:ℝ)/11*((99:ℝ)/100*x-1)) := by
  have hx₀ : 0 < x := by linarith
  let q := 1+(9:ℝ)/11*((99:ℝ)/100*x-1)
  have hq : (x+(21:ℝ)/20)/2 ≤ q := by dsimp [q] <;> linarith
  have hq₀ : 0 < q := by linarith
  have hs : (21:ℝ)/20*x ≤ q^2 := by nlinarith [sq_nonneg (x-(21:ℝ)/20)]
  have hl := Real.log_le_log (show 0 < (21:ℝ)/20*x by positivity) hs
  rw [Real.log_mul (by norm_num : (21:ℝ)/20 ≠ 0) hx₀.ne', Real.log_pow] at hl
  have hc : (1:ℝ)/21 ≤ Real.log ((21:ℝ)/20) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (21:ℝ)/20)
    norm_num at h ⊢
    exact h
  have hxlog := Real.log_nonneg (show 1 ≤ x by linarith)
  change (1+Real.log x)/50 ≤ Real.log q
  norm_num at hl
  linarith

/-- Convert exact active accuracy and superadditivity to the size ratio.
    The side sum may omit inactive children, whose sizes remain nonnegative. -/
theorem ratio_from_sizes {M m a side : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hacc : (9:ℝ)/10*m ≤ a) (hside : 0 ≤ side)
    (hM : m+(10:ℝ)/11*side ≤ M) :
    1+(9:ℝ)/11*(side/a) ≤ M/m := by
  apply (le_div_iff₀ hm).mpr
  have hratio : (9:ℝ)/11*(side/a)*m ≤ (10:ℝ)/11*side := by
    apply (mul_le_mul_iff_left₀ ha).mp
    have hcancel : ((9:ℝ)/11*(side/a)*m)*a = (9:ℝ)/11*side*m := by
      field_simp
    rw [hcancel]
    nlinarith
  nlinarith

/-- A regular active child in an epoch. -/
theorem regular_epoch {A a M m : ℝ} (ha : 0 < a)
    (hsmall : a ≤ (86:ℝ)/100*A)
    (hratio : 1+(9:ℝ)/11*((99:ℝ)/100*A/a-1) ≤ M/m) :
    (1+Real.log (A/a))/50 ≤ Real.log (M/m) := by
  have hx : (50:ℝ)/43 ≤ A/a := by
    apply (le_div_iff₀ ha).mpr
    linarith
  have hq : 0 < 1+(9:ℝ)/11*((99:ℝ)/100*(A/a)-1) := by linarith
  refine (regular_log hx).trans (Real.log_le_log hq ?_)
  simpa only [mul_div_assoc] using hratio

/-- Clipped β parameters are unclipped on active vertices. -/
def beta (c ell k cut M : ℝ) : ℝ := 3 + c / ell * Real.log (k/max M cut)

theorem beta_gap {c ell k cut M m : ℝ}
    (hk : 0 < k) (hm : 0 < m) (hM : 0 < M)
    (hcm : cut ≤ m) (hcM : cut ≤ M) :
    beta c ell k cut m-beta c ell k cut M = c/ell * Real.log (M/m) := by
  simp only [beta,max_eq_left hcm,max_eq_left hcM,Real.log_div hk.ne' hm.ne',
    Real.log_div hk.ne' hM.ne',Real.log_div hM.ne' hm.ne']
  ring

end
end UniformKServer.ParameterGaps

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Actual held vector epochs and persistent dominant identity of companion §03.
 The scalar cumulative-credit budget is linked by an exact projection. -/
noncomputable section
namespace UniformKServer.EpochGeometry
open Finset
variable {ι : Type*} [Fintype ι]

def total (a : ι → ℝ) : ℝ := ∑ i, a i
def variation (a b : ι → ℝ) : ℝ := ∑ i, |b i-a i|
def side (o : ι) (a : ι → ℝ) : ℝ := by
  classical
  exact ∑ i, if i=o then 0 else a i

structure State (ι : Type*) where
  base : ι → ℝ
  credit : ℝ

def valid (a : ι → ℝ) (s : State ι) : Prop :=
  (∀ i, 0 ≤ s.base i) ∧ 0 ≤ s.credit ∧ s.credit ≤ total s.base/100 ∧
    variation s.base a ≤ s.credit

def dominant (s : State ι) : Option ι := by
  classical
  exact if h : ∃ i, 0 < total s.base ∧ (85/100)*total s.base ≤ s.base i
    then some h.choose else none

theorem total_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) : 0 ≤ total a := sum_nonneg fun i _ => ha i

theorem total_difference (a b : ι → ℝ) : |total b-total a| ≤ variation a b := by
  rw [total,total,←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem coordinate_difference (a b : ι → ℝ) (i : ι) : |b i-a i| ≤ variation a b :=
  by
  unfold variation
  exact single_le_sum (fun j _ => abs_nonneg (b j-a j)) (mem_univ i)

theorem total_with_side (a : ι → ℝ) (o : ι) : total a = a o+side o a := by
  classical
  unfold total side
  have he : (∑ i : ι, if i=o then a i else 0)=a o := by simp
  rw [←he,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem dominant_spec {s : State ι} {o : ι} (ho : dominant s=some o) :
    0 < total s.base ∧ (85/100)*total s.base ≤ s.base o := by
  classical
  unfold dominant at ho
  split at ho
  · rename_i h
    have he := Option.some.inj ho
    rw [←he]
    exact h.choose_spec
  · contradiction

theorem absent_spec {s : State ι} (ho : dominant s=none) (i : ι) :
    ¬(0 < total s.base ∧ (85/100)*total s.base ≤ s.base i) := by
  classical
  unfold dominant at ho
  split at ho
  · contradiction
  · rename_i h
    exact fun hi => h ⟨i,hi⟩

theorem two_le_total {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {i j : ι} (hij : i ≠ j) :
    a i+a j ≤ total a := by
  classical
  have h : ∑ r ∈ ({i,j} : Finset ι), a r ≤ total a :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun r _ _ => ha r)
  simpa [sum_pair hij] using h

theorem regular_base {s : State ι} (hs : ∀ i, 0 ≤ s.base i) {i : ι}
    (hi : dominant s ≠ some i) : s.base i ≤ (85/100)*total s.base := by
  have ht := total_nonneg hs
  cases ho : dominant s with
  | none =>
    by_cases hp : 0 < total s.base
    · exact (not_le.mp (fun h => absent_spec ho i ⟨hp,h⟩)).le
    · have hle : s.base i ≤ total s.base := single_le_sum (fun j _ => hs j) (mem_univ i)
      linarith
  | some o =>
    have hij : i ≠ o := by rintro rfl; exact hi ho
    have hdom := dominant_spec ho
    have hsum := two_le_total hs hij
    linarith

theorem regular_size {s : State ι} {a : ι → ℝ} (hs : valid a s) {i : ι}
    (hi : dominant s ≠ some i) : a i ≤ (86/100)*total s.base := by
  have hb := regular_base hs.1 hi
  have hd := coordinate_difference s.base a i
  have hpos := le_abs_self (a i-s.base i)
  linarith [hs.2.2.1,hs.2.2.2]

theorem total_comparison {s : State ι} {a : ι → ℝ} (hs : valid a s) :
    (99/100)*total s.base ≤ total a ∧ total a ≤ (101/100)*total s.base := by
  have h := abs_le.mp ((total_difference s.base a).trans hs.2.2.2)
  constructor <;> linarith [hs.2.2.1]

end UniformKServer.EpochGeometry

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Exact held side parameters and their uniform logarithmic bounds, companion
 §04. No lower bound on a side proportion and no cardinality factor is used. -/
namespace UniformKServer.SideParameters
noncomputable section

def height (A a : ℝ) : ℝ := 1+Real.log (A/a)

theorem height_ge_one {A a : ℝ} (ha : 0 < a) (haA : a ≤ A) : 1 ≤ height A a := by
  unfold height
  have h := Real.log_nonneg ((one_le_div ha).mpr haA)
  linarith

end
end UniformKServer.SideParameters

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Parameters on the actual positive held-size domain of one vector epoch.
These are the geometric hypotheses of the logarithmic proportion minimizer. -/
noncomputable section
namespace UniformKServer.EpochParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem regular_height {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hs : EpochGeometry.valid a s) {i : ι} (ha : 0 < a i)
    (hi : EpochGeometry.dominant s ≠ some i) :
    1 ≤ SideParameters.height (EpochGeometry.total s.base) (a i) := by
  have ht := EpochGeometry.total_nonneg hs.1
  have h := EpochGeometry.regular_size hs hi
  exact SideParameters.height_ge_one ha (by linarith)

theorem side_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (o : ι) :
    0 ≤ EpochGeometry.side o a := by
  classical
  unfold EpochGeometry.side
  exact sum_nonneg fun i _ => by split_ifs <;> first | exact ha i | norm_num

end UniformKServer.EpochParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlpha
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Source logarithmic configurations are built on the actual active-size
 domain, including the automatic one-point domain. -/
noncomputable section
namespace UniformKServer.EpochAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def ell (k : ℕ) : ℝ := 1+Real.log (k+1)

theorem ell_one (k : ℕ) : 1 ≤ ell k := by
  unfold ell
  have h : (1:ℝ) ≤ k+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  linarith [Real.log_nonneg h]

end UniformKServer.EpochAlpha

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParentScale
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

def trueX (I : R → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  max (totalSize (fun r => (I r).posterior t ω)) cutoff

def estimateX (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  max (sizeEstimate I δ t ω) cutoff

def reference (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  held δ (fun s => estimateX I δ s ω) t

def lowerX (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  max cutoff (reference I δ t ω/(1+δ)^2)

theorem estimate_comparison (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    compared δ (estimateX I δ t ω) (trueX I t ω) := by
  have hs := sizeEstimate_comparison I hδ t ω
  have hi : 1+δ ≠ 0 := ne_of_gt (by linarith)
  have hm := mul_le_mul_of_nonneg_left hs.1 (show 0 ≤ 1+δ by linarith)
  rw [←mul_assoc,mul_inv_cancel₀ hi,one_mul] at hm
  have hc : (cutoff:ℝ) ≤ (1+δ)*cutoff := by norm_num [cutoff] at * <;> linarith
  have hpos : 0 ≤ 1+δ := by linarith
  constructor
  · apply max_le
    · exact hm.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos)
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hpos)
  · apply max_le
    · exact hs.2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos)
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hpos)

theorem reference_comparison (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    trueX I t ω ≤ (1+δ)^2*reference I δ t ω ∧
      reference I δ t ω ≤ (1+δ)^2*trueX I t ω := by
  have hh := held_compared hδ.le (fun s =>
    le_trans (show (0:ℝ) ≤ cutoff by norm_num [cutoff]) (le_max_right (sizeEstimate I δ s ω) cutoff)) t
  have hx := estimate_comparison I hδ t ω
  have hpos : 0 ≤ 1+δ := by linarith
  constructor
  · have h := hx.1.trans (mul_le_mul_of_nonneg_left hh.1 hpos)
    change trueX I t ω ≤ (1+δ)*((1+δ)*reference I δ t ω) at h
    nlinarith only [h]
  · have h := hh.2.trans (mul_le_mul_of_nonneg_left hx.2 hpos)
    change reference I δ t ω ≤ (1+δ)*((1+δ)*trueX I t ω) at h
    nlinarith only [h]

theorem lower_bounds (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    cutoff ≤ lowerX I δ t ω ∧ lowerX I δ t ω ≤ trueX I t ω ∧
      trueX I t ω ≤ (1+δ)^4*lowerX I δ t ω := by
  have h := reference_comparison I hδ t ω
  have hp : 0 < (1+δ)^2 := sq_pos_of_pos (by linarith)
  refine ⟨le_max_left _ _,?_,?_⟩
  · apply max_le (le_max_right _ _)
    apply (div_le_iff₀ hp).mpr
    change reference I δ t ω ≤ trueX I t ω*(1+δ)^2
    nlinarith only [h.2]
  · have hd : reference I δ t ω ≤ lowerX I δ t ω*(1+δ)^2 :=
      (div_le_iff₀ hp).mp (le_max_right cutoff _)
    have hm := mul_le_mul_of_nonneg_left hd hp.le
    nlinarith only [h.1,hm]

theorem true_positive (I : R → Input Ω) (t : ℕ) (ω : Ω) : 0 < trueX I t ω :=
  lt_of_lt_of_le (by norm_num [cutoff]) (le_max_right _ _)

theorem lower_positive (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : 0 < lowerX I δ t ω :=
  lt_of_lt_of_le (by norm_num [cutoff]) (le_max_left _ _)

end UniformKServer.ParentScale

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParentBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! A concrete admissible absolute logarithmic coefficient and the parent's
held upper parameter. The source permits any sufficiently small positive
absolute coefficient; this choice preserves its parameter formula. -/
noncomputable section
namespace UniformKServer.ParentBeta
open Finset RankData RankTracking CoarseData ParentScale
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def cBeta : ℝ := 1/2000000

def param (k : ℕ) (X : ℝ) : ℝ := 3+cBeta/EpochAlpha.ell k*Real.log ((k:ℝ)/X)

def trueParam (I : R → Input Ω) (k t : ℕ) (ω : Ω) : ℝ := param k (trueX I t ω)

def heldParam (I : R → Input Ω) (δ : ℝ) (k t : ℕ) (ω : Ω) : ℝ := param k (lowerX I δ t ω)

theorem param_allowed {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hc : cutoff ≤ X) (hX : X ≤ k) :
    RankFunctions.allowed (param k X) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num [cutoff]) hc
  have hl := EpochAlpha.ell_one k
  have hl0 : 0 < EpochAlpha.ell k := by linarith
  have hlog0 : 0 ≤ Real.log ((k:ℝ)/X) := Real.log_nonneg ((le_div_iff₀ hX0).mpr (by simpa))
  have hrat : (k:ℝ)/X ≤ ((k:ℝ)+1)*10000 := by
    apply (div_le_iff₀ hX0).mpr
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ ((k:ℝ)+1)*10000 by positivity)
    norm_num [cutoff] at hh
    nlinarith
  have hlog := Real.log_le_log (div_pos hk0 hX0) hrat
  rw [Real.log_mul (by positivity : (k:ℝ)+1 ≠ 0) (by norm_num : (10000:ℝ) ≠ 0)] at hlog
  have hconst := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10000)
  have hlogBound : Real.log ((k:ℝ)/X) ≤ 10000*EpochAlpha.ell k := by
    unfold EpochAlpha.ell at *
    linarith
  have hupper : cBeta/EpochAlpha.ell k*Real.log ((k:ℝ)/X) ≤ 1/200 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hl0).mpr
    norm_num [cBeta]
    nlinarith only [hlogBound]
  have hlower := mul_nonneg (div_nonneg (show 0 ≤ cBeta by norm_num [cBeta]) hl0.le) hlog0
  constructor
  · unfold param
    linarith only [hlower]
  · unfold param
    linarith only [hupper]

theorem true_allowed (I : R → Input Ω) {k : ℕ} (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (hM : totalSize (fun r => (I r).posterior t ω) ≤ k) :
    RankFunctions.allowed (trueParam I k t ω) := by
  apply param_allowed hk (le_max_right _ _)
  apply max_le hM
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  norm_num [cutoff]
  linarith

theorem held_allowed (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k)
    (t : ℕ) (ω : Ω) (hM : totalSize (fun r => (I r).posterior t ω) ≤ k) :
    RankFunctions.allowed (heldParam I δ k t ω) := by
  have hb := lower_bounds I hδ t ω
  apply param_allowed hk hb.1
  apply hb.2.1.trans
  apply max_le hM
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  norm_num [cutoff]
  linarith

theorem parameter_accuracy (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k)
    (t : ℕ) (ω : Ω) :
    trueParam I k t ω ≤ heldParam I δ k t ω ∧
      heldParam I δ k t ω ≤ trueParam I k t ω+(4*cBeta*δ)/EpochAlpha.ell k := by
  have hx := true_positive I t ω
  have hy := lower_positive I δ t ω
  have hb := lower_bounds I hδ t ω
  have hk0 : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hell : 0 < EpochAlpha.ell k := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (EpochAlpha.ell_one k)
  have hcoeff : 0 ≤ cBeta/EpochAlpha.ell k := div_nonneg (by norm_num [cBeta]) hell.le
  have he : heldParam I δ k t ω-trueParam I k t ω =
      cBeta/EpochAlpha.ell k*Real.log (trueX I t ω/lowerX I δ t ω) := by
    unfold heldParam trueParam param
    rw [Real.log_div hk0.ne' hy.ne',Real.log_div hk0.ne' hx.ne',Real.log_div hx.ne' hy.ne']
    ring
  have hlo : 0 ≤ Real.log (trueX I t ω/lowerX I δ t ω) :=
    Real.log_nonneg ((le_div_iff₀ hy).mpr (by simpa using hb.2.1))
  have hratio : trueX I t ω/lowerX I δ t ω ≤ (1+δ)^4 :=
    (div_le_iff₀ hy).mpr (by nlinarith only [hb.2.2])
  have hlog := Real.log_le_log (div_pos hx hy) hratio
  rw [Real.log_pow] at hlog
  have hlogsmall := Real.log_le_sub_one_of_pos (show 0 < 1+δ by linarith)
  have hhi : Real.log (trueX I t ω/lowerX I δ t ω) ≤ 4*δ := by norm_num at hlog <;> linarith
  have ha := mul_nonneg hcoeff hlo
  have hz := mul_le_mul_of_nonneg_left hhi hcoeff
  constructor
  · linarith only [he,ha]
  · have hid : cBeta/EpochAlpha.ell k*(4*δ)=(4*cBeta*δ)/EpochAlpha.ell k := by ring
    rw [hid] at hz
    linarith only [he,hz]

end UniformKServer.ParentBeta

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CoarseBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Pointwise held-size/core bridges for the actual persistent rank trackers. -/
noncomputable section
namespace UniformKServer.CoarseBridge
open Finset UniformKServer.CoarseData UniformKServer.RankData
open scoped Classical
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem held_some (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) {b : ℝ}
    (hb : activeState I t ω=some b) : heldSize I t ω=b := by
  simp only [heldSize,hb,AllocationSchedule.size]

theorem held_none (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hb : activeState I t ω=none) : heldSize I t ω=0 := by
  simp only [heldSize,hb,AllocationSchedule.size]

theorem held_bound (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    heldSize I t ω ≤ (11/10)*totalSize (fun r => (I r).posterior t ω) := by
  cases hb : activeState I t ω with
  | none =>
    rw [held_none I t ω hb]
    exact mul_nonneg (by norm_num) (sum_nonneg fun r _ => sizeRank_nonneg _)
  | some b => rw [held_some I t ω hb]; exact (active_accuracy I t ω hb).2.1

end UniformKServer.CoarseBridge

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarRanks
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

structure Data (Ω ι : Type*) [Fintype Ω] [Fintype ι] (k : ℕ) where
  weight : Ω → ℝ
  positive : ∀ ω, 0 < weight ω
  total : ∑ ω, weight ω = 1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  count : ℕ → Ω → ι → ℕ
  bound : ∀ t ω, ∑ i, count t ω i ≤ k

def input (d : Data Ω ι k) (i : ι) (j : Fin k) : RankTracking.Input Ω :=
  ConditionalRank.input d.weight (fun ω => le_of_lt (d.positive ω)) d.total
    d.filtration d.refines (fun t ω => d.count t ω i) j

def parentInput (d : Data Ω ι k) (j : Fin k) : RankTracking.Input Ω :=
  ConditionalRank.input d.weight (fun ω => le_of_lt (d.positive ω)) d.total
    d.filtration d.refines (fun t ω => ∑ i, d.count t ω i) j

def held (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  CoarseData.heldSize (input d i) t ω

theorem mass_pos (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    0 < ConditionalLaw.mass d.weight (d.filtration t) ω :=
  lt_of_lt_of_le (d.positive ω) (weight_le_mass (fun v => le_of_lt (d.positive v)) _ _)

theorem size_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ i, totalSize (fun j => (input d i j).posterior t ω)) ≤
      totalSize (fun j => (parentInput d j).posterior t ω) :=
  ConditionalRanks.size_superadditivity d.weight (fun v => le_of_lt (d.positive v))
    (d.filtration t) ω (ne_of_gt (mass_pos d t ω)) (d.count t) k (d.bound t)

theorem parent_size_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    totalSize (fun j => (parentInput d j).posterior t ω) ≤ k := by
  have h := ConditionalRanks.size_le_mean d.weight (fun v => le_of_lt (d.positive v))
    (d.filtration t) ω (ne_of_gt (mass_pos d t ω)) (fun v => ∑ i, d.count t v i) k (d.bound t)
  apply h.trans
  calc
    _ ≤ ∑ v, kernel d.weight (d.filtration t) ω v * (k:ℝ) := by
      apply sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (by change ((∑ i, d.count t v i : ℕ):ℝ) ≤ (k:ℝ); exact_mod_cast d.bound t v)
        (kernel_nonneg (fun v => le_of_lt (d.positive v)) _ _ _)
    _ = k := by
      rw [←sum_mul,ConditionalRanks.normalized_kernel _ _ _ (ne_of_gt (mass_pos d t ω)),one_mul]

theorem held_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ held d t ω i :=
  CoarseData.heldSize_nonneg _ _ _

end UniformKServer.StarRanks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Logarithmic child/parent parameter gaps for the actual finite-count star.
The only epoch input is the invariant of the concrete held-size schedule. -/
noncomputable section
namespace UniformKServer.StarParameters
open Finset RankData RankTracking CoarseData StarRanks EpochGeometry
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def childSize (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  totalSize (fun j => (input d i j).posterior t ω)
def parentSize (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  totalSize (fun j => (parentInput d j).posterior t ω)

theorem positive_accuracy (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) :
    (9/10)*childSize d t ω i ≤ held d t ω i ∧
      held d t ω i ≤ (11/10)*childSize d t ω i ∧ cutoff ≤ childSize d t ω i := by
  cases hb : activeState (input d i) t ω with
  | none =>
    have := CoarseBridge.held_none (input d i) t ω hb
    change held d t ω i=0 at this
    linarith
  | some b =>
    have h := active_accuracy (input d i) t ω hb
    have he := CoarseBridge.held_some (input d i) t ω hb
    change held d t ω i=b at he
    change (9/10)*childSize d t ω i ≤ b ∧ b ≤ (11/10)*childSize d t ω i ∧
      cutoff ≤ childSize d t ω i at h
    rwa [he]

theorem size_with_side (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    childSize d t ω i+(10/11)*side i (held d t ω) ≤ parentSize d t ω := by
  have hi : childSize d t ω i+(10/11)*side i (held d t ω) =
      ∑ j, if j=i then childSize d t ω j else (10/11)*held d t ω j := by
    rw [side,mul_sum]
    have he : childSize d t ω i=∑ j, if j=i then childSize d t ω j else 0 := by simp
    rw [he,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hi]
  apply le_trans _ (size_sum d t ω)
  apply sum_le_sum
  intro j _
  split_ifs
  · rfl
  · have h := CoarseBridge.held_bound (input d j) t ω
    change held d t ω j ≤ (11/10)*childSize d t ω j at h
    change (10/11)*held d t ω j ≤ childSize d t ω j
    linarith

theorem child_le_parent (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    childSize d t ω i ≤ parentSize d t ω := by
  have h := size_with_side d t ω i
  have hs := EpochParameters.side_nonneg (held_nonneg d t ω) i
  linarith

theorem size_ratio (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) :
    1+(9/11)*(side i (held d t ω)/held d t ω i) ≤
      parentSize d t ω/childSize d t ω i := by
  have hc := positive_accuracy d t ω i ha
  exact ParameterGaps.ratio_from_sizes (lt_of_lt_of_le (by norm_num [cutoff]) hc.2.2)
    ha hc.1 (EpochParameters.side_nonneg (held_nonneg d t ω) i) (size_with_side d t ω i)

theorem beta_difference (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) :
    ParentBeta.trueParam (input d i) k t ω-ParentBeta.trueParam (parentInput d) k t ω =
      ParentBeta.cBeta/EpochAlpha.ell k*Real.log (parentSize d t ω/childSize d t ω i) := by
  have hc := (positive_accuracy d t ω i ha).2.2
  have hp := hc.trans (child_le_parent d t ω i)
  have hm0 : 0 < childSize d t ω i := lt_of_lt_of_le (by norm_num [cutoff]) hc
  have hM0 := hm0.trans_le (child_le_parent d t ω i)
  have hk0 : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  change ParameterGaps.beta ParentBeta.cBeta (EpochAlpha.ell k) k cutoff
      (childSize d t ω i)-ParameterGaps.beta ParentBeta.cBeta (EpochAlpha.ell k) k cutoff
      (parentSize d t ω) = _
  exact ParameterGaps.beta_gap hk0 hm0 hM0 hc hp

theorem regular_gap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (s : State ι) (hs : valid (held d t ω) s) (i : ι)
    (ha : 0 < held d t ω i) (hi : dominant s ≠ some i) :
    (ParentBeta.cBeta/50)/EpochAlpha.ell k*
      SideParameters.height (total s.base) (held d t ω i) ≤
      ParentBeta.trueParam (input d i) k t ω-ParentBeta.trueParam (parentInput d) k t ω := by
  have hsides : (99/100)*total s.base/held d t ω i-1 ≤
      side i (held d t ω)/held d t ω i := by
    apply (le_div_iff₀ ha).mpr
    rw [sub_mul,div_mul_cancel₀ _ ha.ne',one_mul]
    linarith [(total_comparison hs).1,total_with_side (held d t ω) i]
  have hr : 1+(9/11)*((99/100)*total s.base/held d t ω i-1) ≤
      parentSize d t ω/childSize d t ω i := by
    have hh := mul_le_mul_of_nonneg_left hsides (show (0:ℝ)≤9/11 by norm_num)
    linarith [size_ratio d t ω i ha]
  have hlog := ParameterGaps.regular_epoch ha (regular_size hs hi) hr
  rw [beta_difference d hk t ω i ha]
  have hcoeff : 0 ≤ ParentBeta.cBeta/EpochAlpha.ell k :=
    div_nonneg (by norm_num [ParentBeta.cBeta]) (le_trans (by norm_num) (EpochAlpha.ell_one k))
  have hm := mul_le_mul_of_nonneg_left hlog hcoeff
  unfold SideParameters.height
  calc
    _ = ParentBeta.cBeta/EpochAlpha.ell k*((1+Real.log (total s.base/held d t ω i))/50) := by ring
    _ ≤ _ := hm

end UniformKServer.StarParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualFineCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Fine caps of the actual persistent rank trackers. No cap feasibility
inequality is assumed; it follows from endpoint errors and the size-log gap. -/
noncomputable section
namespace UniformKServer.ActualFineCaps
open Finset RankFunctions RankData RankTracking CoarseData FlexEstimates
open scoped Classical
variable {Ω R ι : Type*} [Fintype Ω] [Fintype R] [Fintype ι] {k : ℕ}

theorem cap_nonneg (I : R → Input Ω) {β factor : ℝ} (hβ : allowed β)
    (hf : 0 ≤ factor) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ FineVariation.cap I β ξ factor t ω := by
  apply add_nonneg
  · exact sum_nonneg fun r _ => by split_ifs <;> norm_num
  · apply mul_nonneg hf
    exact sum_nonneg fun r _ => by split_ifs <;> first | exact le_rfl | exact (term_range _ hβ _ _ _).1

theorem cap_bound (I : R → Input Ω) {β ξ factor : ℝ} (hβ : allowed β)
    (hξ : 0 < ξ) (hξ' : ξ ≤ 1/2) (hf : factor ∈ Set.Icc (0:ℝ) 2) (t : ℕ) (ω : Ω) :
    FineVariation.cap I β ξ factor t ω ≤ 120*heldSize I t ω := by
  have ht := flex_nonneg I hβ t ω
  have hn : 0 ≤ coreCount (fun r => core (I r) t ω) :=
    sum_nonneg fun r _ => by split_ifs <;> norm_num
  have he := (flex_comparison I hβ hξ t ω).2
  have he0 : 0 ≤ estimateFlex I β ξ t ω :=
    sum_nonneg fun r _ => by split_ifs <;> first | exact le_rfl | exact (term_range _ hβ _ _ _).1
  have hfac : factor*estimateFlex I β ξ t ω ≤ 3*trueFlex I β t ω := by
    have h1 := mul_le_mul_of_nonneg_right hf.2 he0
    have h2 := mul_le_mul_of_nonneg_right hξ' ht
    nlinarith only [he,h1,h2]
  cases hb : activeState I t ω with
  | none =>
    have hz := inactive_zero I t ω β hb
    have hz' : trueFlex I β t ω=0 := hz.2.2
    unfold FineVariation.cap
    rw [hz.1,CoarseBridge.held_none I t ω hb]
    linarith
  | some b =>
    have ha := (active_accuracy I t ω hb).1
    have hd := core_flex_domination (fun r => core (I r) t ω) β
      (fun r => (I r).posterior t ω) hβ (fun r => ((I r).posterior_range t ω).1)
      (fun r hr => by
        have hp := core_small (I r) t ω hr
        norm_num [pstar] at hp ⊢
        linarith)
    change coreCount (fun r => core (I r) t ω)+trueFlex I β t ω ≤ _ at hd
    unfold FineVariation.cap
    rw [CoarseBridge.held_some I t ω hb]
    linarith

theorem coarse_comparison (I : R → Input Ω) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) :
    trueFlex I β t ω/2 ≤ estimateFlex I 3 sizeTolerance t ω ∧
      estimateFlex I 3 sizeTolerance t ω ≤ 2*trueFlex I β t ω := by
  have ht := flex_nonneg I hβ t ω
  have hg := gap_bounds I hβ t ω
  have hg0 : 0 ≤ flexGap I t ω := le_trans (div_nonneg ht (by norm_num)) hg.1
  have hsmall : 0 ≤ β-3 ∧ β-3 ≤ 1/100 := by
    norm_num [allowed] at hβ
    constructor <;> linarith [hβ.1,hβ.2]
  have he := flex_affine I β 3 t ω
  have hm := mul_nonneg hsmall.1 hg0
  have hm' := mul_le_mul hsmall.2 hg.2 hg0 (by norm_num : (0:ℝ) ≤ 1/100)
  have hlo : trueFlex I β t ω ≤ trueFlex I 3 t ω := by nlinarith only [he,hm]
  have hhi : trueFlex I 3 t ω ≤ (101/100)*trueFlex I β t ω := by nlinarith only [he,hm']
  have hc := flex_comparison I (show allowed 3 by norm_num [allowed])
    (show 0 < sizeTolerance by norm_num [sizeTolerance]) t ω
  norm_num [sizeTolerance] at hc ⊢
  constructor <;> linarith [hc.1,hc.2]

theorem held_error (d : StarRanks.Data Ω ι k) (hk : 1 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (t : ℕ) (ω : Ω) (i : ι) :
    |estimateFlex (StarRanks.input d i) (ParentBeta.heldParam (StarRanks.parentInput d) δ k t ω)
      (ρ/EpochAlpha.ell k) t ω-
      trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.parentInput d) k t ω) t ω| ≤
      ((ρ+4*ParentBeta.cBeta*δ)/EpochAlpha.ell k)*
      trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.parentInput d) k t ω) t ω := by
  have hb := ParentBeta.true_allowed (StarRanks.parentInput d) hk t ω (StarRanks.parent_size_bound d t ω)
  have hh := ParentBeta.held_allowed (StarRanks.parentInput d) hδ hk t ω (StarRanks.parent_size_bound d t ω)
  have hp := ParentBeta.parameter_accuracy (StarRanks.parentInput d) hδ hk t ω
  have hell : 0 < EpochAlpha.ell k := lt_of_lt_of_le (by norm_num) (EpochAlpha.ell_one k)
  have he := parameter_error (StarRanks.input d i) hb hh (div_pos hρ hell) hp.1 hp.2 t ω
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem regular_comparison (d : StarRanks.Data Ω ι k) (hk : 1 ≤ k) {δ ρ lam ε : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1/4)
    (he : ρ+4*ParentBeta.cBeta*δ ≤ lam/4)
    (hlg : 4*lam ≤ (ParentBeta.cBeta/50)/96) (hle : 4*lam ≤ ε)
    (t : ℕ) (ω : Ω) (s : EpochGeometry.State ι) (hs : EpochGeometry.valid (StarRanks.held d t ω) s)
    (i : ι) (ha : 0 < StarRanks.held d t ω i) (hi : EpochGeometry.dominant s ≠ some i) :
    trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.input d i) k t ω) t ω ≤
      (1-lam/EpochAlpha.ell k)*estimateFlex (StarRanks.input d i)
        (ParentBeta.heldParam (StarRanks.parentInput d) δ k t ω) (ρ/EpochAlpha.ell k) t ω ∧
      (1-lam/EpochAlpha.ell k)*estimateFlex (StarRanks.input d i)
        (ParentBeta.heldParam (StarRanks.parentInput d) δ k t ω) (ρ/EpochAlpha.ell k) t ω ≤
      trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.parentInput d) k t ω) t ω := by
  have hb := ParentBeta.true_allowed (StarRanks.parentInput d) hk t ω (StarRanks.parent_size_bound d t ω)
  have hell : 0 < EpochAlpha.ell k := lt_of_lt_of_le (by norm_num) (EpochAlpha.ell_one k)
  have hg := StarParameters.regular_gap d hk t ω s hs i ha hi
  have hg0 : 0 ≤ (ParentBeta.cBeta/50)/EpochAlpha.ell k := by
    exact div_nonneg (by norm_num [ParentBeta.cBeta]) hell.le
  have hheight := EpochParameters.regular_height hs ha hi
  have hgap : (ParentBeta.cBeta/50)/EpochAlpha.ell k ≤
      ParentBeta.trueParam (StarRanks.input d i) k t ω-ParentBeta.trueParam (StarRanks.parentInput d) k t ω :=
    le_trans (by simpa using mul_le_mul_of_nonneg_left hheight hg0) hg
  have hf := child_slack (StarRanks.input d i) hb hgap
    (show 0 ≤ ParentBeta.cBeta/50 by norm_num [ParentBeta.cBeta]) hell t ω
  have he0 : 0 ≤ ρ+4*ParentBeta.cBeta*δ := by
    have hcb : 0 ≤ 4*ParentBeta.cBeta := by norm_num [ParentBeta.cBeta]
    exact add_nonneg hρ.le (mul_nonneg hcb hδ.le)
  exact (FineCaps.caps (EpochAlpha.ell_one k) hlam hlam' he0 he hlg hle
    (flex_nonneg _ hb t ω) (held_error d hk hδ hρ t ω i) hf).1

end UniformKServer.ActualFineCaps

end


end

end OAI
end


