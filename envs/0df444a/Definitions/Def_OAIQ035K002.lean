-- Prove2me | Definitions.Def_OAIQ035K002
-- name    : OAIQ035K002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:06.642527+00:00
-- url     : https://prove2.me/theorems/a7500807-a568-49ea-b622-8678a1e06cc4
-- title:
--   Definitions bundle OAIQ035K002 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 86 definitions, 1 inductive type or structure, 1 instance and 18 theorems. The definitions and types are `OAI.MetricKMedian.Binary.Automatic.Poly.natMember`, `OAI.MetricKMedian.Binary.BooleanLists.Phase`, `OAI.MetricKMedian.Binary.Dyadic.powers`, `OAI.MetricKMedian.Binary.Dyadic.twice`, `OAI.MetricKMedian.Binary.IntegerList.Row`, `OAI.MetricKMedian.Binary.IntegerList.Rows`, `OAI.MetricKMedian.Binary.IntegerList.denominator`, `OAI.MetricKMedian.Binary.IntegerList.numerators`, `OAI.MetricKMedian.Binary.Iteration.State`, `OAI.MetricKMedian.Binary.Iteration.body`, `OAI.MetricKMedian.Binary.Iteration.bound`, `OAI.MetricKMedian.Binary.Iteration.iterates`, `OAI.MetricKMedian.Binary.MatrixList.transpose`, `OAI.MetricKMedian.Binary.PolyProgram.checked`, `OAI.MetricKMedian.Binary.Repeat.body`, `OAI.MetricKMedian.Certificates.B0`, `OAI.MetricKMedian.Certificates.B1`, `OAI.MetricKMedian.Certificates.B2`, `OAI.MetricKMedian.Certificates.H`, `OAI.MetricKMedian.Certificates.N`, `OAI.MetricKMedian.Certificates.Q0`, `OAI.MetricKMedian.Certificates.Q1`, `OAI.MetricKMedian.Certificates.T1`, `OAI.MetricKMedian.Certificates.T2`, `OAI.MetricKMedian.Certificates.Tk`, `OAI.MetricKMedian.Certificates.Y`, `OAI.MetricKMedian.Certificates.Yprime`, `OAI.MetricKMedian.Certificates.aSeries`, `OAI.MetricKMedian.Certificates.bernCoeff`, `OAI.MetricKMedian.Certificates.bit`, `OAI.MetricKMedian.Certificates.c`, `OAI.MetricKMedian.Certificates.d`, `OAI.MetricKMedian.Certificates.discr`, `OAI.MetricKMedian.Certificates.h`, `OAI.MetricKMedian.Certificates.hh`, `OAI.MetricKMedian.Certificates.k`, `OAI.MetricKMedian.Certificates.l`, `OAI.MetricKMedian.Certificates.p`, `OAI.MetricKMedian.Certificates.pSeries`, `OAI.MetricKMedian.Certificates.total` and 47 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_CertificatePolynomials`, `KMedian_Analysis_ChargeTransfer`, `KMedian_Analysis_FiniteAverages`, `KMedian_Analysis_QuadraticEnvelopes`, `KMedian_Binary_BinaryAutoFiniteLists`, `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryDyadicPowers`, `KMedian_Binary_BinaryGuard`, `KMedian_Binary_BinaryIterations`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryMatrix`, `KMedian_Binary_BinaryRepeat`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_IntegerListProgram`, `KMedian_Compression_RationalScaling`, `KMedian_Geometry_GraphListOperations`, `KMedian_Geometry_RationalCompletedCost`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Process_BatchActionList`, `KMedian_Process_BatchGraphData`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperListProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_TaggedBestProgram`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseProductProgram`, `KMedian_Sparse_SparseSelect`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K026`, `OAIQ035K036`, `OAIQ035K038`, `OAIQ035K044`, `OAIQ035K058` and `OAIQ035K062`; the statements `OAI.MetricKMedian.Certificates.Yprime_actual_bounds`, `OAI.MetricKMedian.Certificates.a_approximation`, `OAI.MetricKMedian.Certificates.h_lower`, `OAI.MetricKMedian.Certificates.h_upper`, `OAI.MetricKMedian.Certificates.k_envelope`, `OAI.MetricKMedian.Certificates.p_approximation`, `OAI.MetricKMedian.Certificates.polynomial_charge_margin`, `OAI.MetricKMedian.ChargeTransfer.charge_error` and `OAI_MetricKMedian_CopyState_assignment_copies`; the proofs of `OAI.MetricKMedian.Certificates.T1_actual_pos`, `OAI.MetricKMedian.Certificates.T2_actual_pos`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds`, `OAI.MetricKMedian.Certificates.a_approximation`, `OAI.MetricKMedian.Certificates.h_lower`, `OAI.MetricKMedian.Certificates.h_upper`, `OAI.MetricKMedian.Certificates.k_envelope`, `OAI.MetricKMedian.Certificates.p_approximation`, `OAI.MetricKMedian.Certificates.polynomial_charge_margin` and `OAI.MetricKMedian.ChargeTransfer.charge_error`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_CertificatePolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates
noncomputable def p (X : ℝ) : ℝ := (1651507 / 6250000) + (8026757 / 50000000) * X + (1150379 / 20000000) * X ^ 2 + (262741 / 20000000) * X ^ 3 + (228387 / 50000000) * X ^ 4

noncomputable def v (X : ℝ) : ℝ := (10848493 / 6250000) + (-52832269 / 100000000) * X + (-16191093 / 100000000) * X ^ 2 + (-1721469 / 50000000) * X ^ 3 + (-277397 / 25000000) * X ^ 4

noncomputable def k (X : ℝ) : ℝ := (767 / 10000) + (141 / 2500) * X + (71 / 5000) * X ^ 2 + (123 / 5000) * X ^ 3

noncomputable def h (X : ℝ) : ℝ := (197 / 500) + (-21 / 50) * X ^ 2 + (1 / 25) * X ^ 3

noncomputable def pSeries (X : ℝ) : ℝ := (23036089103 / 87178291200) + (1750134643 / 10897286400) * X + (413838773 / 7264857600) * X ^ 2 + (319059131 / 21794572800) * X ^ 3 + (5755571 / 1937295360) * X ^ 4 + (7559 / 15135120) * X ^ 5 + (18619 / 259459200) * X ^ 6 + (32639 / 3632428800) * X ^ 7 + (9829 / 9686476800) * X ^ 8 + (41 / 435891456) * X ^ 9 + (23 / 1981324800) * X ^ 10 + (1 / 7264857600) * X ^ 11 + (1 / 6706022400) * X ^ 12

noncomputable def aSeries (X : ℝ) : ℝ := (150119537 / 86486400) + (-329086987 / 622702080) * X + (-20001539 / 124540416) * X ^ 2 + (-118239629 / 3113510400) * X ^ 3 + (-2532221 / 345945600) * X ^ 4 + (-7613 / 6406400) * X ^ 5 + (-9601 / 57657600) * X ^ 6 + (-1517 / 74131200) * X ^ 7 + (-1181 / 518918400) * X ^ 8 + (-31 / 148262400) * X ^ 9 + (-79 / 3113510400) * X ^ 10 + (-1 / 3113510400) * X ^ 11 + (-1 / 3113510400) * X ^ 12

noncomputable def bit (s : Bool) : ℝ := if s then 1 else 0
noncomputable def d (s : Bool) : ℝ := if s then 2 / 5 else 13 / 25
noncomputable def H (s : Bool) (X : ℝ) : ℝ := if s then 1 / 4 else h X
noncomputable def c (s : Bool) (X : ℝ) : ℝ := 1 - bit s * p X
noncomputable def N (s : Bool) (X : ℝ) : ℝ := c s X - (1 - bit s) * k X
noncomputable def l (s : Bool) (X : ℝ) : ℝ := c s X + 1 - v X + bit s * p X * (1 - X)
noncomputable def hh (s : Bool) : ℝ := 8 / 5 + (2 / 5) * d s
noncomputable def uZero (s : Bool) : ℝ := d s / hh s
noncomputable def uOne (s : Bool) : ℝ := (2 - bit s) * (1 + d s) / (2 * hh s)
noncomputable def Tk (X : ℝ) : ℝ := 4 * k X - (p X + 3 / 400000) * (1 + k X) ^ 2
noncomputable def T1 (X : ℝ) : ℝ := 1 - p X - (28 / 25) * p X * (2 - X) + (2 / 5) * (p X) ^ 2 * X * (2 - X)
noncomputable def T2 (X : ℝ) : ℝ := ((1 - p X)^2 - (19 / 50) * p X * X + p X * (1 - X)) * (2 - X) - 2 * (1-X) * (1-p X)
noncomputable def Q0 (s : Bool) (W X : ℝ) : ℝ := N s X - d s * v X + p X * W * (hh s * W - 2 * d s)
noncomputable def Q1 (s : Bool) (X : ℝ) : ℝ := N s X - (2-bit s) * p X * (1-X) - d s * (c s X * p X - l s X) - hh s * p X * (uOne s)^2
noncomputable def Y (s : Bool) (X : ℝ) : ℝ := N s X - p X * ((2-bit s) * (1-X) + (2-bit s)^2 / (32/5))
noncomputable def Yprime (X : ℝ) : ℝ := N false X + p X * ((8/5) * X^2 - 2)

noncomputable def B0 (s : Bool) (i : ℕ) (X : ℝ) : ℝ :=
  p X * X^2 * (((8/5) * v X + (2/5) * N s X) * ((i:ℝ)*(i-1)/6) +
    (8/5) * (2*p X*X) * (if i = 3 then 1 else 0)) - (1/5000) * X^2 * ((i:ℝ)*(i-1)/6)
noncomputable def B1 (s : Bool) (i : ℕ) (X : ℝ) : ℝ :=
  (c s X * H s X - (2-bit s)*p X*(1-X))*v X + N s X*l s X +
  ((c s X*H s X-(2-bit s)*p X*(1-X))*(2*p X*X) -
    (2-bit s)*p X*X*v X - N s X*(2-bit s)*p X*X) * ((i:ℝ)/3) -
  (2-bit s)*p X*X*(2*p X*X)*((i:ℝ)*(i-1)/6) -
  p X*X^2*(((8/5)*(v X-c s X*p X)+(2/5)*c s X*H s X)*((i:ℝ)*(i-1)/6) +
    (8/5)*(2*p X*X)*(if i = 3 then 1 else 0)) - 1/5000
noncomputable def B2 (s : Bool) (i : ℕ) (X : ℝ) : ℝ :=
  ((2-bit s)*p X*(1-X)-c s X*H s X)*(v X-c s X*p X) - c s X*H s X*l s X +
  (((2-bit s)*p X*(1-X)-c s X*H s X)*(2*p X*X) +
    (2-bit s)*p X*X*(v X-c s X*p X) + c s X*H s X*(2-bit s)*p X*X)*((i:ℝ)/3) +
  (2-bit s)*p X*X*(2*p X*X)*((i:ℝ)*(i-1)/6)
noncomputable def discr (s : Bool) (i : ℕ) (X : ℝ) : ℝ := 4 * B0 s i X * B2 s i X - (B1 s i X)^2
noncomputable def total (s : Bool) (i : ℕ) (X : ℝ) : ℝ := B0 s i X + B1 s i X + B2 s i X


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ChargeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ChargeTransfer

noncomputable def bit (s : Bool) : ℝ := if s then 1 else 0
noncomputable def c (p : ℝ) (s : Bool) : ℝ := 1-bit s*p
noncomputable def F1 (p H x w r : ℝ) (s : Bool) : ℝ :=
  (c p s*H-(2-bit s)*p*(x+w))*r+(8/5)*p*w^2
noncomputable def F2 (p a w r : ℝ) (s : Bool) : ℝ :=
  (1-r)*(a+2*p*w)+c p s*p*r
noncomputable def F3 (p k H r : ℝ) (s : Bool) : ℝ :=
  c p s-(1-bit s)*k-c p s*H*r
noncomputable def F4 (p a x w r : ℝ) (s : Bool) : ℝ :=
  (2-a-bit s*p*(1-x)-(2-bit s)*p*w)*r+(2/5)*p*w^2
noncomputable def charge (p a k H x w r : ℝ) (s : Bool) : ℝ :=
  F1 p H x w r s*F2 p a w r s+F3 p k H r s*F4 p a x w r s

end MetricKMedian.ChargeTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

noncomputable def C (p : ℝ) (s : Bool) : ℝ := if s then 1 - p else 1

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_QuadraticEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

noncomputable def bernCoeff (s : Bool) (i : ℕ) (X r : ℝ) : ℝ :=
  B0 s i X + B1 s i X*r+B2 s i X*r^2

end MetricKMedian.Certificates


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α : Type}
 theorem foldChoice (p : α × α → Bool) (as : List α) (b : α) :
    as.foldl (fun b a => if p (b,a) then a else b) b=b ∨ as.foldl (fun b a => if p (b,a) then a else b) b∈as := by
  induction as generalizing b with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      cases hp : p (b,a)
      · simpa only [hp,Bool.false_eq_true,ite_false] using (ih b).imp_right (fun h => List.mem_cons_of_mem _ h)
      · simp only [ite_true]
        rcases ih a with he|hmem
        · exact Or.inr (by rw [he]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
end ListAlgorithms
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev Row := List ℚ

 theorem foldl_max_le {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hx : ∀ x∈xs, x≤b) : xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      exact ih (max a x) (max_le ha (hx x List.mem_cons_self)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

 theorem le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a : α) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

 theorem member_le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a b : α) (hb : b∈xs) : b ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hb
  | cons x xs ih =>
      rcases List.mem_cons.mp hb with rfl|hb
      · exact (le_max_right a b).trans (le_foldl_max xs (max a b))
      · exact ih (max a x) hb

 theorem foldl_max_eq {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hb : b∈xs) (hx : ∀ x∈xs, x≤b) : xs.foldl max a=b :=
  le_antisymm (foldl_max_le xs a b ha hx) (member_le_foldl_max xs a b hb)

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryAutoFiniteLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary.Automatic.Poly

def natMember (x : List ℕ × ℕ) : Bool := (x.1.map (fun a => decide (a=x.2))).any id
end MetricKMedian.Binary.Automatic.Poly

namespace MetricKMedian.EncodingLists
open Finset
 theorem length_filter_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp
 theorem bool_card {n : ℕ} (s : Finset (Fin n)) :
    ((List.ofFn fun i => decide (i∈s)).filter id).length=s.card := by
  rw [length_filter_ofFn]
  simp
end MetricKMedian.EncodingLists
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryBooleanLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
inductive Phase | start | value | stop deriving DecidableEq
instance instFintypePhase : Fintype Phase := ⟨{.start,.value,.stop},by intro p; cases p <;> simp⟩
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryIterations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Iteration
variable {α : Type}
def iterates (f : α → α) (a : α) : ℕ → List α
  | 0 => []
  | n+1 => a::iterates f (f a) n

theorem iterates_eq (f : α → α) (a : α) (n : ℕ) :
    iterates f a n=(List.range n).map (fun i => f^[i] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [iterates,ih,List.range_succ_eq_map,List.map_cons,List.map_map]
      congr 1

abbrev State (α : Type) := ℕ × (α × List α)
def body (f : α → α) (s : State α) : List α ⊕ State α :=
  if s.1=0 then .inl s.2.2.reverse else .inr (s.1-1,(f s.2.1,s.2.1::s.2.2))

def bound (N A : ℕ) := 2*(N+1)+1+2*A+1+N*(2*A+1)

end Iteration

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryDyadicPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Dyadic

def twice (q : ℚ) : ℚ := q*2
def powers (n : ℕ) : List ℚ := Iteration.iterates twice 1 (n.size+1)
theorem iterate_twice (i : ℕ) : twice^[i] 1=(2:ℚ)^i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih]; exact (pow_succ ..).symm
theorem powers_eq (n : ℕ) : powers n=(List.range (n.size+1)).map (fun t => (2:ℚ)^t) := by
  simp only [powers,Iteration.iterates_eq,iterate_twice]
end Dyadic
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

def checked (p : α → Prop) [DecidablePred p] (a0 : {a // p a}) (a : α) : {a // p a} :=
  if h : p a then ⟨a,h⟩ else a0

end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
universe uα uβ
variable {α : Type uα} {β : Type uβ}

 theorem get_ofFn {n : ℕ} (f : Fin n → α) (p : Fin n) (a0 : α) :
    (List.ofFn f)[p.val]?.getD a0=f p := by
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using p.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace MatrixList
variable {α β : Type}

def transpose (a0 : α) (x : List β × List (List α)) : List (List α) :=
  (List.range x.1.length).map (fun j => x.2.map (fun row => row[j]?.getD a0))

theorem transpose_ofFn {r n : ℕ} (a0 : α) (slots : List β) (hs : slots.length=n)
    (v : Fin r → Fin n → α) :
    transpose a0 (slots,List.ofFn (fun i => List.ofFn (v i))) =
      List.ofFn (fun j => List.ofFn (fun i => v i j)) := by
  have he : List.range n=List.ofFn (fun i : Fin n => i.val) := by
    apply List.ext_getElem <;> intros <;> simp
  simp only [transpose,hs,he,List.map_ofFn,Function.comp_def,Gaussian.ListOperation.get_ofFn]

end MatrixList
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Repeat
variable {α : Type}
def body (f : α → α) (s : ℕ × α) : α ⊕ (ℕ × α) :=
  if s.1=0 then .inl s.2 else .inr (s.1-1,f s.2)

end Repeat

end MetricKMedian.Binary
end

end OAI
end

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

def denominator (q : Ω → ℚ) : ℤ := ∏ i, (q i).den

def numerator (q : Ω → ℚ) (i : Ω) : ℤ :=
  (q i).num * ∏ j ∈ univ.erase i, ((q j).den:ℤ)

theorem numerator_cast (q : Ω → ℚ) (i : Ω) :
    (numerator q i:ℚ)=q i*(denominator q:ℚ) := by
  have he : (q i).den*(∏ j ∈ univ.erase i, ((q j).den:ℤ))=denominator q :=
    mul_prod_erase univ (fun j => ((q j).den:ℤ)) (mem_univ i)
  rw [← he]
  simp only [numerator,Int.cast_mul]
  push_cast
  rw [← mul_assoc,(q i).mul_den_eq_num]

end MetricKMedian.RationalScaling

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace IntegerList
abbrev Row := List ℤ
abbrev Rows := List Row

def denominator (qs : List ℚ) : ℤ := (qs.map (fun q => (q.den:ℤ))).prod
def numerators (qs : List ℚ) : Row := qs.map (fun q => (q*(denominator qs:ℚ)).num)

theorem denominator_ofFn {n : ℕ} (q : Fin n → ℚ) :
    denominator (List.ofFn q)=RationalScaling.denominator q := by
  simp only [denominator,List.map_ofFn,List.prod_ofFn,Function.comp_def,RationalScaling.denominator]

theorem numerators_ofFn {n : ℕ} (q : Fin n → ℚ) :
    numerators (List.ofFn q)=List.ofFn (RationalScaling.numerator q) := by
  simp only [numerators,denominator_ofFn,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  rw [← RationalScaling.numerator_cast,Rat.num_intCast]

end IntegerList
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPMinimumSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

def minimum (xs : Row) : ℚ := xs.foldl min (xs.head?.getD 0)

theorem minimum_eq_finset (xs : Row) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : minimum xs=U.min' hU := by
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
  apply @foldl_max_eq ℚᵒᵈ _ xs _ _
  · exact min'_le U _ ((hm _).mp hd)
  · exact (hm _).mpr (min'_mem U hU)
  · intro q hq
    exact min'_le U q ((hm q).mp hq)

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev Row := Binary.IntegerList.Row

abbrev LawData := ℤ × Row

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
abbrev LawData := IntegerLaw.ListPivot.LawData
variable {α : Type}
abbrev Data (α : Type) := LawData × List α
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev Row := List Bool
abbrev Table := List Row

def indices {α : Type} (xs : List α) : List ℕ := List.range xs.length
def setView {n : ℕ} (S : Finset (Fin n)) : Row := List.ofFn (fun h => decide (h∈S))
end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

def aCoef (P d t : ℚ) : ℚ := if t*d ≤ 1-P then 1 else if 1 ≤ t*d then 0 else 1/P

def bCoef (P d t : ℚ) : ℚ := if t*d ≤ 1-P then 0 else if 1 ≤ t*d then 0 else d/P

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def rationalMarginal (P d r : ℚ) : ℚ := min 1 (max (1-r*d) 0/P)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalCompletedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational
open Finset
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

def score (d : Fin j → F → ℚ) (O : Finset F) : ℚ :=
  ∑ c, if h : O.Nonempty then (O.image (d c)).min' (h.image _) else 0

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev Row := List Bool

def units : ℕ → Row → List Unit
  | 0,_ => [()]
  | d+1,q => (false::q).flatMap (fun _ => units d q)

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchActionList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.RationalBatchData.ActionList
open Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
def parent (n c : ℕ) : ℕ := if c<n then c else (c-n)/n
def child (n c : ℕ) : ℕ := (c-n)%n
end MetricKMedian.RationalBatchData.ActionList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchGraphData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.RationalBatchData.GraphData
open Binary Binary.Automatic Binary.Automatic.Poly Finset
open SparseGraph.ListOperation (Row Table setView indices )

def amount (m : List ℚ) : ℚ := (m.map (fun q => max (1-q) 0)).sum
end MetricKMedian.RationalBatchData.GraphData
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset
abbrev Row := List ℚ
abbrev Raw := (ℚ × ℚ) × Row

def upper (ds : Row) : ℚ := 1+(ds.map (fun q => 1/q)).sum
def breaks (x : ℚ × Row) : Row := 0::upper x.2::((x.2.map (fun q => (1-x.1)/q))++x.2.map (fun q => 1/q))
def aSum (x : (ℚ × Row) × ℚ) : ℚ := (x.1.2.map (fun q => aCoef x.1.1 q x.2)).sum
def bSum (x : (ℚ × Row) × ℚ) : ℚ := (x.1.2.map (fun q => bCoef x.1.1 q x.2)).sum
def candidateList (x : Raw) : Row :=
  let bs := breaks (x.1.2,x.2)
  bs++bs.flatMap (fun a => bs.map (fun b => (aSum ((x.1.2,x.2),(a+b)/2)-1/x.1.1)/bSum ((x.1.2,x.2),(a+b)/2)))
def mass (x : Raw × ℚ) : ℚ := (x.1.2.map (fun d => x.1.1.1*rationalMarginal x.1.1.2 d x.2)).sum
def roots (x : Raw) : Row := (candidateList x).filter (fun q => decide (0<q) && decide (mass (x,q)=1))
end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α β A B : Type}

def prodData (x : Data A × Data B) : Data (A × B) :=
  ((x.1.1.1*x.2.1.1, x.1.1.2.flatMap (fun z => x.2.1.2.map (fun w => z*w))),
    x.1.2.flatMap (fun a => x.2.2.map (fun b => (a,b))))

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

def selectedRow (p : List ℚ) : List Bool := p.map (fun q => decide (q=1))
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
abbrev Row := List ℚ
abbrev BRow := List Bool
abbrev Raw := ((ℚ × ℚ) × ℕ) × List (Row × BRow)

end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

def best (P : α → Bool) (cost : α → ℚ) : List α → Option α
  | [] => none
  | a::L => if P a then
      match best P cost L with
      | none => some a
      | some b => some (if cost a ≤ cost b then a else b)
    else best P cost L

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_TaggedBestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseSelect

variable {α β : Type}
theorem best_map (P : α → Bool) (cost : α → ℚ) (Q : β → Bool) (score : β → ℚ)
    (f : α → β) (hP : ∀ a,Q (f a)=P a) (hc : ∀ a,score (f a)=cost a) (L : List α) :
    (best P cost L).map f=best Q score (L.map f) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [best,List.map_cons,hP,← ih]
    split
    · cases hb : best P cost L with
      | none => rfl
      | some b =>
        simp only [Option.map_some,hc]
        split <;> rfl
    · rfl
end MetricKMedian.SparseSelect
end

end OAI
end


