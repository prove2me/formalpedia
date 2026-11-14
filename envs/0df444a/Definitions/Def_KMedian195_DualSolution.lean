-- Prove2me | Definitions.Def_KMedian195_DualSolution
-- name    : KMedian195_DualSolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:01.37145+00:00
-- url     : https://prove2.me/theorems/7cab88c3-fc20-4877-9b2d-6e0cf90c6d69
-- title:
--   KMedian195.DualSolution
-- statement:
--   This is module `KMedian195.DualSolution` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 27 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_DualSolution`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/DualSolution.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/DualSolution.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`).
-/
module

public import Definitions.Def_KMedian195_DualProgram
public import Mathlib.Data.Finset.Max

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.DualSolution` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

variable {n : ℕ}

/-- Values strictly between `0` and `1`, used for the paper's "fractional entry" condition. -/
def IsFractional (x : ℝ) : Prop :=
  0 < x ∧ x < 1

/--
Input data for the adaptive construction. The extra hypothesis `final_bid_one` is the
paper's standing assumption `b_{n,j} = 1`, which makes the first nonzero bid time well-defined.
-/
structure ProcedureInput (n : ℕ) [NeZero n] where
  program : DualProgram n
  final_bid_one : ∀ j, program.bidding (lastIdx n) j = true

namespace ProcedureInput

variable {n : ℕ} [NeZero n]

def activeTimes (I : ProcedureInput n) (j : Idx n) : Finset (Idx n) :=
  (suffixRange j).filter fun i => I.program.bidding i j

@[simp] theorem mem_activeTimes {I : ProcedureInput n} {j i : Idx n} :
    i ∈ I.activeTimes j ↔ j ≤ i ∧ I.program.bidding i j = true := by
  simp [activeTimes]

theorem activeTimes_nonempty (I : ProcedureInput n) (j : Idx n) :
    (I.activeTimes j).Nonempty := by
  refine ⟨lastIdx n, ?_⟩
  simp [mem_activeTimes, le_lastIdx, I.final_bid_one j]

/-- The paper's `f_j`: the first index with a nonzero bid for client `j`. -/
def firstBidTime (I : ProcedureInput n) (j : Idx n) : Idx n :=
  (I.activeTimes j).min' (I.activeTimes_nonempty j)

theorem firstBidTime_mem (I : ProcedureInput n) (j : Idx n) :
    I.firstBidTime j ∈ I.activeTimes j := by
  exact Finset.min'_mem _ _

theorem le_firstBidTime (I : ProcedureInput n) (j : Idx n) : j ≤ I.firstBidTime j := by
  have hmem := I.firstBidTime_mem j
  exact (mem_activeTimes.mp hmem).1

theorem firstBidTime_isOne (I : ProcedureInput n) (j : Idx n) :
    I.program.bidding (I.firstBidTime j) j = true := by
  have hmem := I.firstBidTime_mem j
  exact (mem_activeTimes.mp hmem).2

/-- The paper's set `ones{i} = {j : f_j = i}`. -/
def frontier (I : ProcedureInput n) (i : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun j => I.firstBidTime j = i

@[simp] theorem mem_frontier {I : ProcedureInput n} {i j : Idx n} :
    j ∈ I.frontier i ↔ I.firstBidTime j = i := by
  simp [frontier]

theorem frontier_client_le (I : ProcedureInput n) {i j : Idx n} (h : j ∈ I.frontier i) :
    j ≤ i := by
  have htime : I.firstBidTime j = i := by
    simpa [mem_frontier] using h
  simpa [htime] using I.le_firstBidTime j

end ProcedureInput

variable {n : ℕ} [NeZero n]

/--
Advice variables from Definition `auxiliary-input`. We store `μ*` as a total function with
support on the frontier `ones(t₃*)`; outside the frontier it is forced to be `0`.
-/
structure Advice (I : ProcedureInput n) where
  t3Star : Idx n
  muStar : Idx n → ℝ
  hatGLast : ℝ
  muStar_support : ∀ ⦃j : Idx n⦄, I.firstBidTime j ≠ t3Star → muStar j = 0
  hatGLast_mem : 0 ≤ hatGLast ∧ hatGLast ≤ 1

namespace Advice

variable {n : ℕ} [NeZero n] {I : ProcedureInput n}

def OnFrontier (Γ : Advice I) (j : Idx n) : Prop :=
  I.firstBidTime j = Γ.t3Star

theorem muStar_eq_zero_of_not_onFrontier (Γ : Advice I) {j : Idx n} :
    ¬ Γ.OnFrontier j → Γ.muStar j = 0 := by
  intro hj
  exact Γ.muStar_support hj

/-- "At most one fractional entry" from the admissibility condition. -/
def AtMostOneFractional (Γ : Advice I) : Prop :=
  ∀ ⦃j₁ j₂ : Idx n⦄,
    Γ.OnFrontier j₁ →
    Γ.OnFrontier j₂ →
    IsFractional (Γ.muStar j₁) →
    IsFractional (Γ.muStar j₂) →
    j₁ = j₂

/-- Non-increasing along the frontier, in the client order used by the paper. -/
def MonotoneOnFrontier (Γ : Advice I) : Prop :=
  ∀ ⦃j₁ j₂ : Idx n⦄,
    j₁ ≤ j₂ →
    Γ.OnFrontier j₁ →
    Γ.OnFrontier j₂ →
    Γ.muStar j₂ ≤ Γ.muStar j₁

/-- Extra condition required in the special case `t₃* = n`. -/
def AllOnesAtLast (Γ : Advice I) : Prop :=
  Γ.t3Star = lastIdx n → ∀ ⦃j : Idx n⦄, Γ.OnFrontier j → Γ.muStar j = 1

/-- Paper-level admissibility for the frontier advice. -/
def Admissible (Γ : Advice I) : Prop :=
  (∀ j, 0 ≤ Γ.muStar j ∧ Γ.muStar j ≤ 1) ∧
    Γ.MonotoneOnFrontier ∧
    Γ.AtMostOneFractional ∧
    Γ.AllOnesAtLast

end Advice

inductive ClientGroup
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The paper's membership weights `(μ^A, μ^B, μ^C, μ^D)`. -/
structure MembershipWeights (n : ℕ) where
  muA : Idx n → ℝ
  muB : Idx n → ℝ
  muC : Idx n → ℝ
  muD : Idx n → ℝ

namespace MembershipWeights

variable {n : ℕ}

def total (μ : MembershipWeights n) (j : Idx n) : ℝ :=
  μ.muA j + μ.muB j + μ.muC j + μ.muD j

def Nonnegative (μ : MembershipWeights n) : Prop :=
  (∀ j, 0 ≤ μ.muA j) ∧
    (∀ j, 0 ≤ μ.muB j) ∧
    (∀ j, 0 ≤ μ.muC j) ∧
    (∀ j, 0 ≤ μ.muD j)

def Normalized (μ : MembershipWeights n) : Prop :=
  ∀ j, μ.total j = 1

end MembershipWeights

variable {n : ℕ} [NeZero n] {I : ProcedureInput n}

/-- Abstract type of the adaptive procedure from the paper. -/
abbrev AdaptiveProcedure (I : ProcedureInput n) := Advice I → Option (DualSolution n)

/-- The paper's notion of a "correct" advice: the procedure does not return `⊥`. -/
def CorrectAdvice (procedure : AdaptiveProcedure I) (Γ : Advice I) : Prop :=
  ∃ x, procedure Γ = some x

/-- Interface for the later correctness theorem of the adaptive construction. -/
def ProcedureBoundedBy (I : ProcedureInput n) (procedure : AdaptiveProcedure I) (bound : ℝ) :
    Prop :=
  ∀ Γ x, procedure Γ = some x → DualSolution.Feasible x I.program ∧ x.rho ≤ bound

end KMedian195


