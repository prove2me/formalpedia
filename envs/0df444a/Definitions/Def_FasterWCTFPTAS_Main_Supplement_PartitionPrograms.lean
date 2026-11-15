-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Supplement_PartitionPrograms
-- name    : FasterWCTFPTAS_Main_Supplement_PartitionPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:08:03.976193+00:00
-- url     : https://prove2.me/theorems/35610fe3-8e45-4860-b6ed-53441a3562dd
-- title:
--   Uniform partition decision programs and encodings
-- statement:
--   For fixed $k$, encode the grouped set problem as $[s,q,W]$ followed by all $n$ values in row order. Encode the multiset problem as $[s,q,W,t_1,\ldots,t_{k-1}]$ followed by those values, with no empty-row headers. One real memory cell holds each number. A grouped solver has one admissible program and a constant $C>0$, both chosen before every instance, deciding Yes and No with the standard $[1]/[0]$ outputs within
--
--   $$C n^\beta W^{k-1-\eta}.$$
--
--   A multiset promise solver has the same requirements only for Yes or No instances, with bound $C\max(1,n)^\beta\max(1,W)^{k-1-\eta}$. The padding changes only zero cases; on positive instances this is the displayed source monomial. No correctness or time condition is imposed outside the promise. Exponents are real, so $k-1-\eta$ is allowed to be zero or negative. These predicates describe actual executions of the published machine, rather than an unspecified solver oracle.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.20 (PDF p.21), problem inputs; pp.20,26 (PDF pp.21,27), Theorem A.3 and Corollary A.7.

import Definitions.Def_FasterWCTFPTAS_Main_Supplement_CNFSETH
import Definitions.Def_FasterWCTFPTAS_Main_Supplement_Partition

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- All n item values in row order, with no empty-row headers. -/
def itemCells {k : ℕ} (I : PartitionData k) : List ℝ :=
  (List.ofFn fun i => List.ofFn fun j => (I.a i j : ℝ)).flatten

/-- k is fixed with the program. The input is [s,q,W] then all items in row order. -/
def groupedInput {k : ℕ} (I : PartitionData k) : List ℝ :=
  [(I.s : ℝ), (I.q : ℝ), (I.W : ℝ)] ++ itemCells I

/-- [s,q,W,t_1,...,t_(k-1)] then all items in row order. -/
def weakInput {k : ℕ} (I : WeakInstance k) : List ℝ :=
  [(I.data.s : ℝ), (I.data.q : ℝ), (I.data.W : ℝ)] ++
    List.ofFn (fun ℓ => (I.target ℓ : ℝ)) ++ itemCells I.data

/-- A uniform O(n^β W^(k-1-η)) algorithm for the set decision problem. -/
def FastGrouped (k : ℕ) (η β : ℝ) : Prop :=
  ∃ (P : Machine.Program) (C : ℝ), Machine.Admissible P ∧ 0 < C ∧
    ∀ I : PartitionData k, GroupedValid I →
      CorrectDecision P (groupedInput I) (GroupedYes I) ∧
      Machine.HaltsWithin P (groupedInput I)
        (C * (I.n : ℝ) ^ β * (I.W : ℝ) ^ ((k : ℝ) - 1 - η))

/-- A uniform solver for the FULL multiset promise problem. Runtime and correctness are
required only on Yes or No inputs; the gap between the promise sets is unrestricted.
Padding only defines zero n,W, on which the printed monomial is undefined or zero. -/
def FastWeak (k : ℕ) (η β : ℝ) : Prop :=
  ∃ (P : Machine.Program) (C : ℝ), Machine.Admissible P ∧ 0 < C ∧
    ∀ I : WeakInstance k, WeakValid I → WeakYes I ∨ WeakNo I →
      (WeakYes I → Machine.output P (weakInput I) = some [1]) ∧
      (WeakNo I → Machine.output P (weakInput I) = some [0]) ∧
      Machine.HaltsWithin P (weakInput I)
        (C * ((max 1 I.data.n : ℕ) : ℝ) ^ β *
          ((max 1 I.data.W : ℕ) : ℝ) ^ ((k : ℝ) - 1 - η))

end FasterWCTFPTAS.Main.Supplement


