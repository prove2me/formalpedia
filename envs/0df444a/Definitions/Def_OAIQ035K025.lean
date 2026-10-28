-- Prove2me | Definitions.Def_OAIQ035K025
-- name    : OAIQ035K025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:52.337536+00:00
-- url     : https://prove2.me/theorems/f7beb860-7ca6-4a42-a9e5-055b5fadfd64
-- title:
--   Definitions bundle OAIQ035K025 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 17 definitions, 2 inductive types or structures and 22 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.CoupledLaw`, `OAI.MetricKMedian.Preparation.SupplierStars.connectionCharge`, `OAI.MetricKMedian.Preparation.SupplierStars.supplier`, `OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy_1`, `OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalCountCopyOrder`, `OAI.MetricKMedian.Reduction.CloseCenters`, `OAI.MetricKMedian.Reduction.CloseCenters.backup`, `OAI.MetricKMedian.Reduction.CloseCenters.matched`, `OAI.MetricKMedian.Reduction.CloseCenters.region`, `OAI.MetricKMedian.Reduction.completionGeometryPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.localCompletionPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.rationalCandidates`, `OAI.MetricKMedian.Reduction.rationalRegion`, `OAI.MetricKMedian.Reduction.witnessedRestriction`, `OAI.MetricKMedian.SparseBundleEncoding.decode`, `OAI.MetricKMedian.SparseBundleEncoding.encode`, `OAI.MetricKMedian.SparsePrepared.discarded`, `OAI.MetricKMedian.SparsePrepared.requests`, `OAI.MetricKMedian.SparseRescaledInner.encodedCount`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Preparation_CoupledPreparation`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_SupplierCharges`, `KMedian_Preparation_SupplierMap`, `KMedian_Reduction_CompletionGeometry`, `KMedian_Reduction_LocalCompletion`, `KMedian_Reduction_RationalLocalChoice`, `KMedian_Reduction_SparsifyEnumeration`, `KMedian_Rounding_RationalLastFraction`, `KMedian_Rounding_RationalPhysicalCount`, `KMedian_Rounding_RationalPhysicalGraphInstance`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalWeightedInvariants`, `KMedian_Rounding_RationalWeightedStep`, `KMedian_Rounding_WeightedRounding`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseRescaledInner`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K006`, `OAIQ035K008`, `OAIQ035K010` and `OAIQ035K011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K035` and `OAIQ035K036`; the statements `OAI.MetricKMedian.Preparation.request_connection_radius`, `OAI.MetricKMedian.Preparation.supplier_assignments` and `OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices`; the proofs of `OAI.MetricKMedian.Preparation.request_connection_radius`, `OAI.MetricKMedian.Preparation.shortfall_from_deviation`, `OAI.MetricKMedian.Preparation.supplier_assignments` and `OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K010
import Definitions.Def_OAIQ035K011

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

omit [Fintype I] in
theorem sign_distinct {i j k l : I} {r : ℝ} (hr : 0 ≤ r) (hkl : k ≠ l) :
    sign i j r k*sign i j r l ≤ 0 := by
  unfold sign
  split_ifs <;> simp_all

omit [Fintype I] in

theorem endpoint_mean (p : I → ℝ) (i j k : I) (r : ℝ) {u d : ℝ}
    (hu : 0 < u) (hd : 0 < d) :
    d/(u+d)*move p i j r u k+(1-d/(u+d))*move p i j r (-d) k=p k := by
  unfold move
  field_simp
  ring

omit [Fintype I] in
theorem endpoint_pair (p : I → ℝ) (i j : I) {k l : I} (hkl : k ≠ l) {r u d : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hd : 0 < d) :
    d/(u+d)*(move p i j r u k*move p i j r u l)+
      (1-d/(u+d))*(move p i j r (-d) k*move p i j r (-d) l) ≤ p k*p l := by
  have hpos : 0 < u+d := add_pos hu hd
  have hid : d/(u+d)*(move p i j r u k*move p i j r u l)+
      (1-d/(u+d))*(move p i j r (-d) k*move p i j r (-d) l) =
      p k*p l+u*d*(sign i j r k*sign i j r l) := by
    unfold move
    field_simp
    ring
  rw [hid]
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu.le hd.le)
    (sign_distinct hr hkl))

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledPreparation
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationStars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

omit [DecidableEq T] in

theorem mass_partition (y : I → ℝ) (P : T → Finset I)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t))) (F : Finset I) :
    (∑ i ∈ F ∩ outside P, y i)+(∑ t, ∑ i ∈ F ∩ P t, y i)=∑ i ∈ F, y i := by
  simp_rw [← sum_ite_mem]
  rw [sum_comm,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : ∃ t, i ∈ P t
  · obtain ⟨t,ht⟩ := hi
    have hu : i ∉ outside P := by simp only [outside,mem_filter,mem_univ,true_and]; exact fun h => h t ht
    rw [ite_eq_right hu,sum_eq_single t,ite_eq_left ht,zero_add]
    · intro s _ hst
      exact ite_eq_right (fun hs => (disjoint_left.mp (hP hst)) hs ht)
    · simp
  · have hu : i ∈ outside P := by simp only [outside,mem_filter,mem_univ,true_and]; exact fun t ht => hi ⟨t,ht⟩
    have hn : ∀ t, i ∉ P t := fun t ht => hi ⟨t,ht⟩
    simp only [ite_eq_left hu,hn,ite_false,sum_const_zero,add_zero]

theorem targeted_weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hc : ∀ t, ∑ i ∈ A t, y i=c t) (t : T) :
    (∑ e, if t ∈ targets A e then weight y P A c γ e else 0)=(1+γ)*c t := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [targets,weight,mem_filter,mem_univ,true_and,mem_singleton]
  have ho : (∑ i, if i ∈ A t then (if i ∈ outside P then y i else 0) else 0)=
      ∑ i ∈ A t ∩ outside P, y i := by
    rw [sum_ite_mem,univ_inter,sum_ite_mem]
  have hb : (∑ s, ∑ r, if t=s then ∑ i ∈ A s ∩ P r, y i else 0)=
      ∑ r, ∑ i ∈ A t ∩ P r, y i := by
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]
  rw [ho,hb,sum_ite_eq,ite_eq_left (mem_univ t)]
  have hp := mass_partition y P hP (A t)
  rw [hc t] at hp
  linarith only [hp]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def connectionCharge (P A : T → Finset I) (y d : I → ℝ)
    (L : T → ℝ) (κ β δ : ℝ) : Star I T → ℝ
  | .inl i => d i
  | .inr (.inl st) => κ*((∑ i ∈ A st.1 ∩ P st.2, y i*d i)/(∑ i ∈ A st.1 ∩ P st.2, y i))
  | .inr (.inr t) => (β+1+δ)*L t

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def supplier (next : T → T) : Star I T → I ⊕ T
  | .inl i => .inl i
  | .inr (.inl st) => .inr st.2
  | .inr (.inr t) => .inr (next t)

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)
local instance completionGeometryPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

structure CloseCenters (G : Finset (Fin I.n)) (O : Finset (Fin I.n)) (δ : ℝ) where
  radius : ↥G → ℝ
  radius_nonneg : ∀ t, 0 ≤ radius t
  separated : ∀ t u, t ≠ u → radius t ≤ dist t.val u.val
  matchTo : ↥G → Fin I.n
  match_mem : ∀ t, matchTo t ∈ O
  close : ∀ t, dist t.val (matchTo t) < δ*radius t

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_LocalCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance localCompletionPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

noncomputable def region (C : CloseCenters I G O δ) (t : ↥G) : Finset (Fin I.n) :=
  I.clients.filter (fun j => dist j t.val ≤ C.radius t/3)

noncomputable def matched (C : CloseCenters I G O δ) : Finset (Fin I.n) :=
  univ.image C.matchTo

noncomputable def backup (C : CloseCenters I G O δ) : Finset (Fin I.n) :=
  O \ C.matched

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalLocalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalRegion (I : Instance) (r : Fin I.n → ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  I.clients.filter (fun j => 3*I.distance j t ≤ r t)

def rationalCandidates (I : Instance) (F : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  F.filter (fun a => I.distance t a ≤ δ*r t)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_SparsifyEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def witnessedRestriction (I : Instance) (F : Finset (Fin I.n))
    (P : Finset (Fin I.n × Fin I.n)) : Finset (Fin I.n) :=
  F.filter (fun i => ∀ p ∈ P, I.distance p.1 p.2 ≤ I.distance p.1 i)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalWeightedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) (k : Fin n) :
    probability β p*point (endpoint β p 0) k+
      (1-probability β p)*point (endpoint β p 1) k=point p k := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_mean (realPoint p) a.val.1 a.val.2 k (r:ℝ) hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalWeightedInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability β p*(point (endpoint β p 0) k*point (endpoint β p 0) l)+
      (1-probability β p)*(point (endpoint β p 1) k*point (endpoint β p 1) l) ≤
        point p k*point p l := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hrr : (0:ℝ) ≤ r := by exact_mod_cast hr.le
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_pair (realPoint p) a.val.1 a.val.2 hkl hrr hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add,le_refl]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalLastFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalLastFraction
open Finset RationalWeightedStep
variable {n : ℕ}

theorem nonfractional (p : Vector ℚ n)
    (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (k : Fin n)
    (hk : k ∉ fractional p) : point p k=0 ∨ point p k=1 := by
  have h := hp k
  simp only [fractional,mem_filter,mem_univ,true_and,not_and_or,not_lt] at hk
  rcases hk with hk | hk
  · exact Or.inl (le_antisymm hk h.1)
  · exact Or.inr (le_antisymm h.2 hk)

end MetricKMedian.RationalLastFraction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem selected_indicator (q : Vector ℚ n)
    (hq : ∀ i, point q i=0 ∨ point q i=1) (i : Fin n) :
    (if i ∈ selected q then (1:ℚ) else 0)=point q i := by
  rcases hq i with h | h <;> simp [selected,h]

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalGraphInstance
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
local instance instLinearOrderCopy_1 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalCount
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
local instance rationalPhysicalCountCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

theorem endpoint_mean (β : Fin n → ℚ) (p : Vector ℚ n) (k : Fin n) :
    probability β p*point (endpoint β p 0) k+
      (1-probability β p)*point (endpoint β p 1) k=point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_mean (realPoint p) a.val.1 a.val.2 k (r:ℝ) hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add]

theorem endpoint_pair (β : Fin n → ℚ) 
    (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability β p*(point (endpoint β p 0) k*point (endpoint β p 0) l)+
      (1-probability β p)*(point (endpoint β p 1) k*point (endpoint β p 1) l) ≤
        point p k*point p l := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hrr : (0:ℝ) ≤ r := by exact_mod_cast hr.le
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_pair (realPoint p) a.val.1 a.val.2 hkl hrr hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add,le_refl]

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

theorem base_sum_le (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (K : ℕ)
    (hs : (∑ i, q i)=(K:ℚ)) : (∑ i, base q i) ≤ K := by
  have hh : (∑ i, (base q i:ℚ)) ≤ (K:ℚ) :=
    (sum_le_sum (fun i _ => Nat.floor_le (hq i))).trans_eq hs
  exact_mod_cast hh

theorem fraction_sum (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (K : ℕ)
    (hs : (∑ i, q i)=(K:ℚ)) :
    (∑ i, point (fraction q) i)=(K-∑ i,base q i:ℕ) := by
  simp only [fraction,point,Vector.getElem_ofFn,sum_sub_distrib,hs,
    Nat.cast_sub (base_sum_le q hq K hs),Nat.cast_sum]

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRescaledInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

theorem piece_cap (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (Δ : ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (hK : ∀ j,K j ≤ Δ) :
    ∀ i j,piece P y p K i j ≤ Δ := by
  intro i j
  by_cases hi : i∈P j
  · have hyP : y i ≤ p j := (single_le_sum (fun i _ => hy i) hi).trans_eq (hm j)
    have he : piece P y p K i j ≤ (K j:ℚ) := by
      simp only [piece,ite_eq_left hi]
      apply (div_le_iff₀ (hp j)).mpr
      exact mul_le_mul_of_nonneg_left hyP (Nat.cast_nonneg _)
    exact he.trans (Nat.cast_le.mpr (hK j))
  · simp only [piece,ite_eq_right hi]
    exact Nat.cast_nonneg _

theorem piece_sum (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j) :
    ∀ j,(∑ i,piece P y p K i j)=(K j:ℚ) := by
  intro j
  simp only [piece,sum_ite_mem,univ_inter,← sum_div,← mul_sum,hm]
  exact mul_div_cancel_right₀ _ (hp j).ne'

end MetricKMedian.SparseRescaledInner
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

def encode (q : Fin n → Fin m → ℚ) (G : SparseCounts.Table n m) :
    Fin m → Finset (Fin n) :=
  fun j => univ.filter (fun i => G j i = SparseGridRounding.base (fun i => q i j) i + 1)

def decode (q : Fin n → Fin m → ℚ) (ξ : Fin m → Finset (Fin n)) :
    SparseCounts.Table n m :=
  fun j i => SparseGridRounding.base (fun i => q i j) i + if i ∈ ξ j then 1 else 0

theorem decode_encode (q : Fin n → Fin m → ℚ) (G : SparseCounts.Table n m)
    (hG : ∀ j i, G j i = SparseGridRounding.base (fun i => q i j) i ∨
      G j i = SparseGridRounding.base (fun i => q i j) i + 1) :
    decode q (encode q G) = G := by
  funext j i
  rcases hG j i with h | h <;> simp [decode, encode, h]

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

def encodedCount (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (ξ : Fin t → Finset (Fin n)) (a : Fin t × Fin n) : ℕ :=
  SparseBundleEncoding.decode (piece P y p K) ξ a.1 a.2

theorem cast_scaled_piece (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (g : ℝ) (i : Fin n) (j : Fin t) :
    g * (piece P y p K i j : ℝ) =
      if i ∈ P j then (g * (K j : ℝ)) * (y i : ℝ) / (p j : ℝ) else 0 := by
  simp only [piece, apply_ite, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_zero]
  split_ifs <;> ring

end MetricKMedian.SparseRescaledInner
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedLaw
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

def requests (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : Fin n → Fin m → ℕ :=
  fun j => RationalRetain.keep (fun e => activationCount D q z e j) (Δ/2)

theorem requests_le (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) (e : Fin m) :
    requests D q Δ z j e ≤ activationCount D q z e j := RationalRetain.le _ _ _

theorem exact_total (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) :
    total D q Δ z j+(∑ e,requests D q Δ z j e)=Δ := by
  unfold total requests
  rw [RationalRetain.total]
  exact Nat.sub_add_cancel ((min_le_right _ _).trans (Nat.div_le_self _ _))

theorem total_le (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) : total D q Δ z j ≤ Δ := Nat.sub_le _ _

theorem total_half (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℝ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℝ)=1) : (1/2:ℝ) ≤ g*(total D q Δ z j:ℝ) :=
  (Preparation.grid_clip hg heven hunit (∑ e,activationCount D q z e j)).2.2.1

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedBudget
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

theorem activation_sum (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) :
    (∑ j,activationCount D q z e j)=(D e).card*base q e+(z.2.1 e).card := by
  simp only [activationCount,sum_add_distrib,sum_ite_mem,univ_inter,sum_const,
    nsmul_eq_mul,mul_one,Nat.cast_id]

def discarded (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) : ℚ :=
  ((∑ e,activationCount D q z e j):ℕ)-
    (min (∑ e,activationCount D q z e j) (Δ/2):ℕ)

end MetricKMedian.SparsePrepared
end
end

end OAI
end


