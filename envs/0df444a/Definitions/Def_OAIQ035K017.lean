-- Prove2me | Definitions.Def_OAIQ035K017
-- name    : OAIQ035K017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:55:43.079492+00:00
-- url     : https://prove2.me/theorems/78d885ca-344e-4969-9c3c-8734b46df758
-- title:
--   Definitions bundle OAIQ035K017 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 13 definitions, 1 inductive type or structure and 6 theorems. The definitions and types are `OAI.MetricKMedian.IntegerBranching.branchNumerator`, `OAI.MetricKMedian.RationalBatchData.Event`, `OAI.MetricKMedian.RationalBatchData.balanced`, `OAI.MetricKMedian.RationalBatchData.conflicts`, `OAI.MetricKMedian.RationalBatchData.enumeration`, `OAI.MetricKMedian.RationalBatchData.graph`, `OAI.MetricKMedian.RationalBatchData.graphMass`, `OAI.MetricKMedian.RationalBatchData.heavy`, `OAI.MetricKMedian.RationalLaw.integer`, `OAI.MetricKMedian.RationalPhysicalKernel.Payload`, `OAI.MetricKMedian.RationalPhysicalKernel.State`, `OAI.MetricKMedian.SparseIntegerLaw`, `OAI.MetricKMedian.SparseIntegerLaw.map`, `OAI.MetricKMedian.SparseIntegerLaw.moment`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_RationalIntegerLaw`, `KMedian_Compression_RationalScaling`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalNearestCopies`, `KMedian_Preparation_PreparationMoments`, `KMedian_Programs_MaximumProgram`, `KMedian_Rounding_RationalBatchData`, `KMedian_Rounding_RationalBatchEnumeration`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Rounding_RationalRoundEvents`, `KMedian_Sparse_SparseIntegerLaw`, `KMedian_Sparse_SparseMap`.
--
--   **Imports.** It imports the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004` and `OAIQ035K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K031`, `OAIQ035K032`, `OAIQ035K033`, `OAIQ035K035`, `OAIQ035K036`, `OAIQ035K038`, `OAIQ035K044`, `OAIQ035K058` and `OAIQ035K062`; the statement `OAI_MetricKMedian_SparseBernoulli_count_variance`; the proof of `OAI.MetricKMedian.FiniteLaw.restricted_moments`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalScaling
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem denominator_pos (q : Ω → ℚ) : 0 < denominator q := by
  apply prod_pos
  intro i _
  exact_mod_cast (q i).den_pos

end MetricKMedian.RationalScaling

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalIntegerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def integer (μ : RationalLaw Ω) : IntegerLaw Ω where
  denominator := RationalScaling.denominator μ.weight
  denominator_pos := RationalScaling.denominator_pos μ.weight
  numerator := RationalScaling.numerator μ.weight
  numerator_nonneg i := by
    have hh : (0:ℚ) ≤ (RationalScaling.numerator μ.weight i:ℚ) := by
      rw [RationalScaling.numerator_cast]
      exact mul_nonneg (μ.nonneg i) (by exact_mod_cast (RationalScaling.denominator_pos μ.weight).le)
    exact_mod_cast hh
  total := by
    apply Int.cast_injective (α:=ℚ)
    rw [Int.cast_sum]
    simp only [RationalScaling.numerator_cast,← sum_mul,μ.total,one_mul]

@[simp] theorem integer_weight (μ : RationalLaw Ω) (i : Ω) :
    μ.integer.rational.weight i=μ.weight i := by
  change (RationalScaling.numerator μ.weight i:ℚ)/(RationalScaling.denominator μ.weight:ℚ)=_
  rw [RationalScaling.numerator_cast,mul_div_cancel_right₀]
  exact_mod_cast (RationalScaling.denominator_pos μ.weight).ne'

@[simp] theorem integer_numerator_zero (μ : RationalLaw Ω) (i : Ω) :
    μ.integer.numerator i=0 ↔ μ.weight i=0 := by
  have hD : (RationalScaling.denominator μ.weight:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos μ.weight).ne'
  change RationalScaling.numerator μ.weight i=0 ↔ _
  rw [← Int.cast_eq_zero (α:=ℚ),RationalScaling.numerator_cast,mul_eq_zero,or_iff_left hD]

end MetricKMedian.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_IntegerBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

def branchNumerator (p : Fin n → ℚ) (i : Fin n) (b : Fin 2) : ℤ :=
  if b=0 then RationalScaling.numerator p i
    else RationalScaling.denominator p-RationalScaling.numerator p i

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalNearestCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α : Type} [LinearOrder α]

theorem takeNearest_spec (d : α → ℚ) (k : ℕ) (U : Finset α) (hk : k ≤ U.card) :
    takeNearest d k U ⊆ U ∧ (takeNearest d k U).card=k ∧
    ∀ S : Finset α, S ⊆ U → S.card=k → (∑ a∈takeNearest d k U,d a) ≤ ∑ a∈S,d a := by
  induction k generalizing U with
  | zero =>
    simp only [takeNearest,empty_subset,card_empty,true_and,sum_empty]
    intro S _ hS
    simp [card_eq_zero.mp hS]
  | succ k ih =>
    have hU : U.Nonempty := card_pos.mp (by omega)
    let a := least U d hU
    have ha : a∈U := (least_spec U d hU).1
    have hamin : ∀ b∈U, d a ≤ d b := (least_spec U d hU).2
    have hk' : k ≤ (U.erase a).card := by rw [card_erase_of_mem ha]; omega
    obtain ⟨hsub,hcard,hmin⟩ := ih (U.erase a) hk'
    have han : a∉takeNearest d k (U.erase a) := fun h => (mem_erase.mp (hsub h)).1 rfl
    simp only [takeNearest,dite_eq_left hU]
    change insert a (takeNearest d k (U.erase a)) ⊆ U ∧ _
    refine ⟨insert_subset ha (hsub.trans (erase_subset _ _)),?_,?_⟩
    · rw [card_insert_of_notMem han,hcard]
    · intro S hSU hSk
      rw [sum_insert han]
      by_cases haS : a∈S
      · have hsubS : S.erase a ⊆ U.erase a := erase_subset_erase a hSU
        have hSc : (S.erase a).card=k := by rw [card_erase_of_mem haS,hSk]; omega
        have hh := hmin _ hsubS hSc
        have he := sum_erase_add S d haS
        linarith only [hh,he]
      · have hS : S.Nonempty := card_pos.mp (by omega)
        obtain ⟨b,hb⟩ := hS
        have hsubS : S.erase b ⊆ U.erase a := by
          intro z hz
          have hzS := mem_of_mem_erase hz
          exact mem_erase.mpr ⟨fun he => haS (he ▸ hzS),hSU hzS⟩
        have hSc : (S.erase b).card=k := by rw [card_erase_of_mem hb,hSk]; omega
        have hh := hmin _ hsubS hSc
        have he := sum_erase_add S d hb
        have hd := hamin b (hSU hb)
        linarith only [hh,he,hd]

end MetricKMedian.Preparation.RationalNearest
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem variance_sum_le (μ : FiniteLaw Ω) (X : I → Ω → ℝ) (q v : I → ℝ)
    (hmean : ∀ i, μ.expect (X i)=q i)
    (hvar : ∀ i, μ.variance (X i) ≤ v i)
    (hpair : ∀ i j, i ≠ j → μ.expect (fun ω => X i ω*X j ω) ≤ q i*q j) :
    μ.variance (fun ω => ∑ i, X i ω) ≤ ∑ i, v i := by
  classical
  have hs : μ.expect (fun ω => (∑ i, X i ω)^2) ≤ (∑ i, q i)^2+∑ i, v i := by
    have hp : ∀ i j, μ.expect (fun ω => X i ω*X j ω) ≤ q i*q j+(if i=j then v i else 0) := by
      intro i j
      by_cases h : i=j
      · subst j
        have hv := hvar i
        rw [variance_eq, hmean i] at hv
        simpa only [ite_true, sq] using (by linarith only [hv] : μ.expect (fun ω => (X i ω)^2) ≤ q i^2+v i)
      · simpa only [ite_eq_right h, add_zero] using hpair i j h
    calc
      _ = ∑ i, ∑ j, μ.expect (fun ω => X i ω*X j ω) := by
        simp_rw [sq, sum_mul_sum, expect_sum]
      _ ≤ ∑ i, ∑ j, (q i*q j+if i=j then v i else 0) :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
      _ = _ := by
        simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul, sq]
  rw [variance_eq, expect_sum]
  simp only [hmean] at *
  linarith only [hs]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseIntegerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

structure SparseIntegerLaw (α : Type) where
  length : ℕ
  states : Vector α length
  law : IntegerLaw (Fin length)

namespace SparseIntegerLaw
variable {α : Type}

def moment (μ : SparseIntegerLaw α) (f : α → ℚ) : ℚ :=
  ∑ i : Fin μ.length, μ.law.rational.weight i*f μ.states[i.val]

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

def map (μ : SparseIntegerLaw α) (f : α → β) : SparseIntegerLaw β where
  length := μ.length
  law := μ.law
  states := μ.states.map f

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_MaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
 theorem maximum_eq_finset (xs : List ℚ) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : maximum xs=U.max' hU := by
  have hne : xs≠[] := by
    intro he
    obtain ⟨q,hq⟩ := hU
    have hx := (hm q).mpr hq
    rw [he] at hx
    cases hx
  have hd : xs.head?.getD 0∈xs := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact List.mem_cons_self
  apply LPBinary.foldl_max_eq
  · exact le_max' U _ ((hm _).mp hd)
  · exact (hm _).mpr (max'_mem U hU)
  · intro q hq
    exact le_max' U q ((hm q).mp hq)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

def graph (G : I → Finset I) : Actions I I where
  source := id
  erase := fun h => univ.filter (fun i => h ∈ G i)
  ordinary := univ

def heavy (Full : Actions I I) (H : Finset I) : Actions I (HeavyAction Full H) where
  source := fun e => Full.source (heavyParent Full H e)
  erase := Sum.elim (fun h => Full.erase h) (fun p => {p.val.2})
  ordinary := univ.filter (fun e : HeavyAction Full H => e.isLeft = true)

def balanced (D : Actions I E) (Δ : ℕ) : Finset E :=
  D.ordinary.filter (fun e => (D.erase e).card=Δ)

def conflicts (D : Actions I E) (Δ : ℕ) (e : E) : Finset E :=
  if e ∈ balanced D Δ then
    (balanced D Δ).filter (fun f => f≠e ∧ (D.erase e ∩ D.erase f).Nonempty) else ∅

def graphMass (G : I → Finset I) (g : ℚ) (h : I) : ℚ := g*((graph G).erase h).card

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

def enumeration (Full : Actions I I) (H : Finset I) :
    Fin (Fintype.card (HeavyAction Full H)) ≃ HeavyAction Full H := by
  letI : LinearOrder (I × I) :=
    LinearOrder.lift' (fun p : I × I => toLex p) (fun _ _ h => h)
  letI : LinearOrder (HeavyAction Full H) :=
    LinearOrder.lift' (fun e : HeavyAction Full H => toLex e) (fun _ _ h => h)
  exact (Fintype.orderIsoFinOfCardEq (HeavyAction Full H) rfl).toEquiv

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRoundEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

abbrev Event (I : Type) [DecidableEq I] [Fintype I] (g β : ℚ) :=
  (G : I → Finset I) × Finset (HeavyAction (graph G) (heavySet (graphMass G g) β))

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

abbrev Payload (F : Type) [LinearOrder F] (Δ : ℕ) (g β : ℚ) :=
  (A : Finset (CopyState.Copy (F := F) Δ)) × RationalBatchData.Event A g β

abbrev State (F : Type) [LinearOrder F] (Δ : ℕ) (g β : ℚ) :=
  Finset (CopyState.Copy (F := F) Δ) × Option (Payload F Δ g β)

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end


