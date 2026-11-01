-- Prove2me | Definitions.Def_OAIQ053K036
-- name    : OAIQ053K036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:01:28.908991+00:00
-- url     : https://prove2.me/theorems/9f91ddce-6c23-4be8-9fa3-16494ed19561
-- title:
--   Definitions bundle OAIQ053K036 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 25 definitions, 1 inductive type or structure and 15 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.power`, `OAI.MetricKMedian.PCP.LocalRelation.rejectionWeight`, `OAI.MetricKMedian.PCP.PortCSP.cutHit`, `OAI.MetricKMedian.PCP.PortCSP.rootHit`, `OAI.MetricKMedian.PCP.PortGraph.Walk.hitCount`, `OAI.MetricKMedian.PCP.PortGraph.Walk.ithHit`, `OAI.MetricKMedian.PCP.PortGraph.down`, `OAI.MetricKMedian.PCP.PortGraph.honest`, `OAI.MetricKMedian.PCP.PortGraph.mass`, `OAI.MetricKMedian.PCP.PortGraph.opinion`, `OAI.MetricKMedian.PCP.PortGraph.plurality`, `OAI.MetricKMedian.PCP.PortGraph.up`, `OAI.MetricKMedian.PCP.PortGraph.vote`, `OAI.MetricKMedian.PCP.Tableau.honest`, `OAI.MetricKMedian.Preparation.CoupledLaw`, `OAI.MetricKMedian.Preparation.CoupledLaw.castWeights`, `OAI.MetricKMedian.Preparation.CoupledLaw.reindexStars`, `OAI.MetricKMedian.Preparation.oldAssignment`, `OAI.MetricKMedian.Preparation.physicalCount`, `OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy_2`, `OAI.MetricKMedian.SparseOuterLaw.deficit`, `OAI.MetricKMedian.SparseOuterLaw.nominalMass`, `OAI.MetricKMedian.SparseSignedPreparation.BudgetSpec`, `OAI.MetricKMedian.SparseSignedPreparation.nominalCount`, `OAI.MetricKMedian.SparseSignedPreparation.outside`, `OAI.MetricKMedian.SparseSignedPreparation.raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_Majority`, `KMedian_Amplification_PoweringObjects`, `KMedian_CookLevin_TableauCorrect`, `KMedian_Expanders_PathCount`, `KMedian_PCP_LocalReduction`, `KMedian_Preparation_CoupledGeometry`, `KMedian_Preparation_CoupledPreparation`, `KMedian_Preparation_CoupledReindex`, `KMedian_Preparation_CoupledWeights`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Process_PhysicalOldMass`, `KMedian_Projection_IncidenceOperator`, `KMedian_Projection_PowerTable`, `KMedian_Rounding_RationalPhysicalSurvival`, `KMedian_Sparse_SparseAffineMoments`, `KMedian_Sparse_SparseMap`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseMomentAlgebra`, `KMedian_Sparse_SparseNonnegativeSupport`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseOuterMoments`, `KMedian_Sparse_SparseOuterReal`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseSignedBudget`.
--
--   **Imports.** It imports the bundles `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K023`, `OAIQ053K024`, `OAIQ053K025`, `OAIQ053K026` and `OAIQ053K027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K043`, `OAIQ053K053` and `OAIQ053K062`; the statements `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53`, `OAI.MetricKMedian.PCP.LocalRelation.sound_s53`, `OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53`, `OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53`, `OAI.MetricKMedian.Preparation.physical_old_estimates_s53` and `OAI.MetricKMedian.Preparation.supplier_assignments_s53`; the proofs of `OAI.MetricKMedian.PCP.AlphabetReduction.padded_complete_s53`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53`, `OAI.MetricKMedian.PCP.LocalRelation.sound_s53`, `OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53`, `OAI.MetricKMedian.Preparation.physical_old_estimates_s53` and `OAI.MetricKMedian.Preparation.supplier_assignments_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K023
import Definitions.Def_OAIQ053K024
import Definitions.Def_OAIQ053K025
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K027

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D A : Type} {cap : ℕ} (G : PortGraph V D) [Inhabited A]

def honest (x : V → A) (v : V) : Advice D A cap :=
  fun n c => x (G.trace n.val v c (Fin.last n.val))

def opinion (a : V → Advice D A cap) (n : ℕ) (v : V) (c : Fin n → D) : A :=
  (a ((Walk.ofWord (G := G) v c).vertex (Fin.last n))).get n (Walk.ofWord (G := G) v c).reverse.port

end PortGraph
end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

theorem map_moment (μ : SparseIntegerLaw α) (f : α → β) (v : β → ℚ) :
    (μ.map f).moment v=μ.moment (fun a => v (f a)) := by
  unfold moment map
  simp only [Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMarginalTools
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 theorem moment_mono (μ : SparseIntegerLaw α) (f g : α → ℚ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val] ≤ g μ.states[i.val]) :
    μ.moment f ≤ μ.moment g := by
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (μ.law.rational.nonneg i)

 theorem moment_const (μ : SparseIntegerLaw α) (c : ℚ) : μ.moment (fun _ => c)=c := by
  unfold moment
  rw [← sum_mul,μ.law.rational.total,one_mul]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Majority
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMajority

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D A : Type} [Fintype D] [Nonempty D] [Fintype A] [Inhabited A]
variable (G : PortGraph V D) {cap : ℕ} (a : V → Advice D A cap)

noncomputable def vote (n : ℕ) (v : V) (b : A) : ℝ :=
  testRate (fun c : Fin n → D => G.opinion a n v c = b)

noncomputable def mass (t L : ℕ) (v : V) (b : A) : ℝ :=
  ∑ i ∈ range (L+1), Stopped.stopping t * Stopped.survival t ^ i * G.vote a i v b

omit [Nonempty D] in
lemma exists_plurality (t L : ℕ) (v : V) :
    ∃ b : A, ∀ c : A, G.mass a t L v c ≤ G.mass a t L v b := by
  obtain ⟨b,_,hb⟩ := exists_max_image univ (G.mass a t L v) univ_nonempty
  exact ⟨b, fun c => hb c (mem_univ c)⟩

noncomputable def plurality (t L : ℕ) (v : V) : A :=
  Classical.choose (G.exists_plurality a t L v)

end PortGraph

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

noncomputable def rootHit (a : V → Advice D A cap) (x : V → A) (i j : ℕ)
    (z : (V × (Fin i → D)) × (D × (Fin j → D))) : ℝ := by
  classical
  exact G.edgeHit (C.Bad x) z.1.1 z.2.1 *
    (if G.opinion a i z.1.1 z.1.2 = x z.1.1 then 1 else 0) *
    (if G.opinion a j (G.step z.1.1 z.2.1) z.2.2 = x (G.step z.1.1 z.2.1) then 1 else 0)

noncomputable def cutHit (a : V → Advice D A cap) (x : V → A) (i j : ℕ)
    (p : G.Walk (i+(j+1))) : ℝ := C.rootHit a x i j (PortGraph.Walk.centerEquiv i j p)

end PortCSP
end MetricKMedian.PCP

end Inline_PCPMajority

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_LocalReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

variable (R : Relation K) [DecidablePred (· ∈ R)]

noncomputable def rejectionWeight (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) : ℝ :=
  (quadratic R).rejectionWeight f h +
    boundaryRate (leftEmbed R) f u + boundaryRate (rightEmbed R) f v

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauCorrect

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)

variable [Inhabited σ]
noncomputable def honest (T L : ℕ) (cs : Fin (T+1) → Cfg Γ Λ σ) : Var (K := K) T L → Value M
  | .inl t => ⟨((cs t).l,(cs t).var),emptyResponse M,fun _ => none⟩
  | .inr (.inl t) => ⟨emptyControl,respond M ((cs (now T t)).l,(cs (now T t)).var)
      (stackPrefix M (cs (now T t)).stk),fun _ => none⟩
  | .inr (.inr (t,_,i)) => ⟨emptyControl,emptyResponse M,fun k => ((cs t).stk k)[i.val]?⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauCorrect

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_PathCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPathCount

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D : Type}
variable (G : PortGraph V D) (bad : V × D → Prop)

namespace Walk
variable {G bad} {n : ℕ}
noncomputable def ithHit (p : G.Walk n) (i : ℕ) : ℝ :=
  if h : i < n then G.edgeHit bad (p.vertex ⟨i,by omega⟩) (p.port ⟨i,h⟩) else 0
noncomputable def hitCount (p : G.Walk n) : ℝ := ∑ i ∈ range n, p.ithHit (bad := bad) i

end Walk
end PortGraph
end MetricKMedian.PCP

end Inline_PCPPathCount

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledPreparation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T I : Type} [Fintype E] [DecidableEq E]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

structure CoupledLaw (D : E → Finset T) (a w : E → ℝ) (P : T → Finset I)
    (y : I → ℝ) (p c : T → ℝ) (g γ B : ℝ) (Δ : ℕ) where
  Ω : Type
  [finite : Fintype Ω]
  ν : FiniteLaw Ω
  κ : Ω → FiniteLaw (T → Finset I)
  O : Ω → E → ℕ
  N : Ω → E → ℝ
  R : Ω → T → E → ℕ
  K : Ω → T → ℕ
  C : Ω → (T → Finset I) → T × I → ℕ
  open_cap : ∀ ω, 0 < ν.weight ω → ∀ e, w e ≤ 1 → g*(O ω e:ℝ) ≤ 1
  open_zero : ∀ ω, 0 < ν.weight ω → ∀ e, w e=0 → O ω e=0
  nominal_nonneg : ∀ ω, 0 < ν.weight ω → ∀ e, 0 ≤ N ω e
  nominal_cap : ∀ ω, 0 < ν.weight ω → ∀ e, N ω e ≤ g*(O ω e:ℝ)
  nominal_mean : ∀ e, ν.expect (fun ω => N ω e)=w e
  nominal_variance : ∀ e, ν.variance (fun ω => N ω e) ≤ g*w e
  nominal_pair : ∀ e f, e ≠ f → ν.expect (fun ω => N ω e*N ω f) ≤ w e*w f
  request_cap : ∀ ω, 0 < ν.weight ω → ∀ t e, R ω t e ≤ O ω e
  request_target : ∀ ω t e, t ∉ D e → R ω t e=0
  request_mean : ∀ t e, ν.expect (fun ω => g*(R ω t e:ℝ)) ≤ if t ∈ D e then w e else 0
  exact_total : ∀ ω t, K ω t+(∑ e, R ω t e)=Δ
  half : ∀ ω t, (1/2:ℝ) ≤ g*(K ω t:ℝ)
  total_cap : ∀ ω t, K ω t ≤ Δ
  total_deviation : ∀ t, ν.expect (fun ω => |g*(K ω t:ℝ)-p t|) ≤ γ*c t+Real.sqrt (g*(1+γ)*c t)
  pieces : ∀ ω ξ, 0 < (κ ω).weight ξ → ∀ t,
    (∑ i, C ω ξ (t,i))=K ω t ∧ (∀ i, C ω ξ (t,i) ≤ Δ) ∧
    (∀ i, i ∉ P t → C ω ξ (t,i)=0)
  piece_mean : ∀ ω t i, (κ ω).expect (fun ξ => g*(C ω ξ (t,i):ℝ))=
    if i ∈ P t then (g*(K ω t:ℝ))*y i/p t else 0
  piece_pair : ∀ ω a b, a ≠ b → (κ ω).expect (fun ξ => (g*(C ω ξ a:ℝ))*(g*(C ω ξ b:ℝ))) ≤
    (if a.2 ∈ P a.1 then (g*(K ω a.1:ℝ))*y a.2/p a.1 else 0)*
    (if b.2 ∈ P b.1 then (g*(K ω b.1:ℝ))*y b.2/p b.1 else 0)
  piece_variance : ∀ ω a, (κ ω).variance (fun ξ => g*(C ω ξ a:ℝ)) ≤
    g*(if a.2 ∈ P a.1 then (g*(K ω a.1:ℝ))*y a.2/p a.1 else 0)
  budget : 1-4*g*(1+γ)/γ ≤ ν.prob (fun ω =>
    (∑ e, a e*(g*(O ω e:ℝ)))+(∑ t, g*(K ω t:ℝ)) ≤ B+3*g)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledGeometry
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def physicalCount {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) : Physical I T → ℕ :=
  Sum.elim (fun i => L.O z.1 (.inl i)) (L.C z.1 z.2)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMomentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem moment_add (μ : SparseIntegerLaw α) (f g : α → ℚ) :
    μ.moment (fun a => f a+g a)=μ.moment f+μ.moment g := by
  simp only [moment,mul_add,sum_add_distrib]

theorem moment_mul_right (μ : SparseIntegerLaw α) (f : α → ℚ) (c : ℚ) :
    μ.moment (fun a => f a*c)=μ.moment f*c := by
  simp only [moment,← mul_assoc,sum_mul]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAffineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
variable {α : Type}

theorem moment_sub (μ : SparseIntegerLaw α) (f g : α → ℚ) :
    μ.moment (fun a => f a-g a)=μ.moment f-μ.moment g := by
  simp only [moment,mul_sub,Finset.sum_sub_distrib]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseNonnegativeSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem zero_nonnegative (μ : SparseIntegerLaw α) (f : α → ℚ)
    (hf : ∀ i : Fin μ.length, 0 ≤ f μ.states[i.val])
    (hz : μ.moment f=0) (a : Fin μ.length)
    (ha : 0 < μ.law.rational.weight a) : f μ.states[a.val]=0 := by
  have hh := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*f μ.states[i.val])
    (fun i _ => mul_nonneg (μ.law.rational.nonneg i) (hf i)) (mem_univ a)
  change _ ≤ μ.moment f at hh
  rw [hz] at hh
  have hn := hf a
  nlinarith only [hh,ha,hn]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedBudget
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

def outside (b : Fin m → ℕ) (z : State n m) (e : Fin m) : ℚ :=
  (b e:ℚ)+SparseStarActivation.upper (point z.1 e)

def nominalCount (b : Fin m → ℕ) (z : State n m) (e : Fin m) : ℚ :=
  (b e:ℚ)+SparseBernoulli.flag z.2.2 e

def raw (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ) (z : State n m) : ℚ :=
  ∑ e, (c e*outside b z e-(((D e).card:ℚ)*(b e:ℚ)+(z.2.1 e).card))

def BudgetSpec (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (t : ℚ) (z : State n m) : Prop :=
  (∀ e, z.2.1 e ⊆ D e) ∧
  (∀ e, outside b z e=(b e:ℚ) ∨ outside b z e=(b e:ℚ)+1) ∧
  (∀ e, nominalCount b z e=(b e:ℚ) ∨ nominalCount b z e=(b e:ℚ)+1) ∧
  (∀ e, nominalCount b z e ≤ outside b z e) ∧
  (∀ e i, (b e:ℚ)+(if i∈z.2.1 e then 1 else 0) ≤ outside b z e) ∧
  raw D c b z ≤ t

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem fraction_identity (q : Fin m → ℚ) (e : Fin m) :
    (base q e:ℚ)+point (fraction q) e=q e := by
  simp only [point,fraction,Vector.getElem_ofFn,add_sub_cancel]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

noncomputable def nominalMass (q : Fin m → ℚ) (g : ℝ) (z : State n m) (e : Fin m) : ℝ :=
  g * (SparseSignedPreparation.nominalCount (base q) z e : ℝ)

theorem nominalMass_nonneg (q : Fin m → ℚ) {g : ℝ} (hg : 0 ≤ g)
    (z : State n m) (e : Fin m) : 0 ≤ nominalMass q g z e := by
  apply mul_nonneg hg
  dsimp only [SparseSignedPreparation.nominalCount, SparseBernoulli.flag]
  split_ifs <;> positivity

end MetricKMedian.SparseOuterLaw
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterMoments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open SparseGridRounding (base)
open SparseSignedPreparation (State)
variable {n m : ℕ}

def deficit (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (g : ℚ)
    (z : State n m) (i : Fin n) : ℚ := g*∑ e, activation D q z e i

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem requests_le (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) (e : Fin m) :
    requests D q Δ z j e ≤ activationCount D q z e j := RationalRetain.le _ _ _

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedBudget
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw SparseGridRounding
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem discarded_mass (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℚ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℚ)=1) :
    (g:ℝ)*(discarded D q Δ z j:ℝ)=
      (deficit D q g z j:ℝ)-min (deficit D q g z j:ℝ) (1/2) := by
  have he : (deficit D q g z j:ℝ)=(g:ℝ)*((∑ e,activationCount D q z e j):ℕ) := by
    simp only [deficit,Rat.cast_mul,Rat.cast_sum,Nat.cast_sum,← activationCount_cast,
      Rat.cast_natCast]
  rw [he,(Preparation.grid_clip (by exact_mod_cast hg) heven (by exact_mod_cast hunit)
    (∑ e,activationCount D q z e j)).1]
  simp only [discarded,Rat.cast_sub,Rat.cast_natCast,mul_sub]

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledReindex
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation
open Finset
attribute [instance] CoupledLaw.finite
variable {E E' T I : Type} [Fintype E] [DecidableEq E]
  [Fintype E'] [DecidableEq E'] [Fintype T] [DecidableEq T]
  [Fintype I] [DecidableEq I]

noncomputable def CoupledLaw.reindexStars (e : E ≃ E')
    {D : E' → Finset T} {a w : E' → ℝ} {P : T → Finset I}
    {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (D ∘ e) (a ∘ e) (w ∘ e) P y p c g γ B Δ) :
    CoupledLaw D a w P y p c g γ B Δ where
  Ω := L.Ω
  ν := L.ν
  κ := L.κ
  O := fun z i => L.O z (e.symm i)
  N := fun z i => L.N z (e.symm i)
  R := fun z t i => L.R z t (e.symm i)
  K := L.K
  C := L.C
  open_cap := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z hz i => L.open_cap z hz (e.symm i)
  open_zero := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z hz i => L.open_zero z hz (e.symm i)
  nominal_nonneg := fun z hz i => L.nominal_nonneg z hz (e.symm i)
  nominal_cap := fun z hz i => L.nominal_cap z hz (e.symm i)
  nominal_mean := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun i => L.nominal_mean (e.symm i)
  nominal_variance := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun i => L.nominal_variance (e.symm i)
  nominal_pair := by
    intro i j hij
    simpa only [Function.comp_apply, e.apply_symm_apply] using
      L.nominal_pair (e.symm i) (e.symm j) (e.symm.injective.ne hij)
  request_cap := fun z hz t i => L.request_cap z hz t (e.symm i)
  request_target := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z t i => L.request_target z t (e.symm i)
  request_mean := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun t i => L.request_mean t (e.symm i)
  exact_total := by
    intro z t
    rw [e.symm.sum_comp]
    exact L.exact_total z t
  half := L.half
  total_cap := L.total_cap
  total_deviation := L.total_deviation
  pieces := L.pieces
  piece_mean := L.piece_mean
  piece_pair := L.piece_pair
  piece_variance := L.piece_variance
  budget := by
    have he : ∀ z, (∑ i, a i * (g * (L.O z (e.symm i) : ℝ))) =
        ∑ j, a (e j) * (g * (L.O z j : ℝ)) := by
      intro z
      rw [← e.sum_comp]
      simp only [e.symm_apply_apply]
    simpa only [he, Function.comp_apply] using L.budget

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation
open Finset
attribute [local instance] CoupledLaw.finite
variable {E T I : Type} [Fintype E] [DecidableEq E]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

noncomputable def CoupledLaw.castWeights {D : E → Finset T} {a a' w w' : E → ℝ}
    {P : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw D a w P y p c g γ B Δ) (ha : a=a') (hw : w=w') :
    CoupledLaw D a' w' P y p c g γ B Δ where
  Ω := L.Ω
  ν := L.ν
  κ := L.κ
  O := L.O
  N := L.N
  R := L.R
  K := L.K
  C := L.C
  open_cap := by rw [← hw]; exact L.open_cap
  open_zero := by rw [← hw]; exact L.open_zero
  nominal_nonneg := L.nominal_nonneg
  nominal_cap := L.nominal_cap
  nominal_mean := by rw [← hw]; exact L.nominal_mean
  nominal_variance := by rw [← hw]; exact L.nominal_variance
  nominal_pair := by rw [← hw]; exact L.nominal_pair
  request_cap := L.request_cap
  request_target := L.request_target
  request_mean := by rw [← hw]; exact L.request_mean
  exact_total := L.exact_total
  half := L.half
  total_cap := L.total_cap
  total_deviation := L.total_deviation
  pieces := L.pieces
  piece_mean := L.piece_mean
  piece_pair := L.piece_pair
  piece_variance := L.piece_variance
  budget := by rw [← ha]; exact L.budget

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierPreparation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

theorem scaled_q (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ g : ℚ) (hg : g ≠ 0) (e : Fin (size f n)) :
    (g : ℝ) * (q y P A c γ g e : ℝ) =
      weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) := by
  have hh : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  simp [q, Rat.cast_div, mul_div_cancel₀ _ hh, weight_cast]

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance instLinearOrderCopy_2 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace FixedParameters
theorem grid {τ : ℝ} (qR : FixedBatch.RationalParameters τ) : qR.g*(qR.Δ:ℚ)=1 := by exact_mod_cast qR.unit
end FixedParameters

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalOldMass
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def oldAssignment {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) : Physical I T → ℝ :=
  Sum.elim (fun i => if i ∈ F ∩ outside P then L.N z.1 (.inl i) else 0)
    (fun ti => if ti.2 ∈ F then g*(L.C z.1 z.2 ti:ℝ) else 0)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_IncidenceOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPIncidenceOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A B : Type} (G : PortGraph V D)

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
noncomputable def down (h : V × D → ℝ) (v : V) : ℝ :=
  𝔼 d, (h (v,d)+h (G.rotate (v,d)))/2
noncomputable def up (h : V → ℝ) (p : V × D) : ℝ :=
  (h p.1+h (G.rotate p).1)/2

end PortGraph
end MetricKMedian.PCP

end Inline_PCPIncidenceOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_PowerTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionPowerTable
namespace MetricKMedian.PCP
open scoped Classical

namespace Compiler
open Binary Binary.Automatic

namespace ProjectionTable
variable {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
noncomputable def power (t : ProjectionTable A B) : (n : ℕ)→ProjectionTable (Nested A n) (Nested B n)
  | 0 => build BiProjection.trivial (Equiv.ofUnique Unit (Fin 1)) (Ordered.fixed Unit) (Ordered.fixed Unit)
  | n+1 => product t (power t n)
variable {U V D S : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {m : ℕ} (ue : U≃Fin m) (vo : Ordered V) (so : Ordered S)
omit [Fintype A] [Fintype B] [Inhabited B] [Fintype U] [Fintype V] [Fintype D]
  [Fintype S] [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B] in
lemma power_build (n : ℕ) : power (build G ue vo so) n=
    build (G.power n) (nestedEquiv ue n) (vo.nested n) (so.nested n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change product (build G ue vo so) (power (build G ue vo so) n)=_
    rw [ih,product_build]
    apply Prod.ext
    · simp only [build,pow_succ']
    · rfl
end ProjectionTable
end Compiler
end MetricKMedian.PCP

end Inline_PCPProjectionPowerTable

end OAI
end


