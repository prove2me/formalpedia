-- Prove2me | Definitions.Def_OAIQ053K011
-- name    : OAIQ053K011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:39.487033+00:00
-- url     : https://prove2.me/theorems/522c227d-4d4f-486f-b9ea-60e66c23e5a9
-- title:
--   Definitions bundle OAIQ053K011 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 73 definitions, 2 inductive types or structures and 24 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.LocalCompiler.Label`, `OAI.MetricKMedian.PCP.Compiler.LocalCompiler.relation`, `OAI.MetricKMedian.PCP.Compiler.ProjectionRow`, `OAI.MetricKMedian.PCP.Compiler.ProjectionTable`, `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.combine`, `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.product`, `OAI.MetricKMedian.PCP.Compiler.SeedCombinators.numbered`, `OAI.MetricKMedian.PCP.Compiler.SeedCombinators.project`, `OAI.MetricKMedian.PCP.Compiler.SeedCombinators.source`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.VC`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.varCode`, `OAI.MetricKMedian.PCP.Compiler.unaryPower`, `OAI.MetricKMedian.PCP.FiniteCSP`, `OAI.MetricKMedian.PCP.FiniteCSP.Label`, `OAI.MetricKMedian.PCP.FiniteCSP.Satisfies`, `OAI.MetricKMedian.PCP.FiniteCSP.decoded`, `OAI.MetricKMedian.PCP.FiniteCSP.honest`, `OAI.MetricKMedian.PCP.MassNormalize.normalized`, `OAI.MetricKMedian.PCP.MixedNorm.inner`, `OAI.MetricKMedian.PCP.PortGraph.average`, `OAI.MetricKMedian.PCP.PortGraph.lift`, `OAI.MetricKMedian.PCP.PortGraph.residual`, `OAI.MetricKMedian.PCP.PortGraph.totalMass`, `OAI.MetricKMedian.PCP.Stopped.stopping`, `OAI.MetricKMedian.PCP.Stopped.survival`, `OAI.MetricKMedian.PCP.Tableau.BoundaryClause`, `OAI.MetricKMedian.PCP.Tableau.Clause`, `OAI.MetricKMedian.PCP.Tableau.Padded.next`, `OAI.MetricKMedian.PCP.Tableau.Row`, `OAI.MetricKMedian.PCP.Tableau.Safe`, `OAI.MetricKMedian.PCP.Tableau.ValidRow`, `OAI.MetricKMedian.PCP.Tableau.Var`, `OAI.MetricKMedian.PCP.Tableau.appendCfg`, `OAI.MetricKMedian.PCP.Tableau.boundaryTime`, `OAI.MetricKMedian.PCP.Tableau.cell`, `OAI.MetricKMedian.PCP.Tableau.clamp`, `OAI.MetricKMedian.PCP.Tableau.clampedCell`, `OAI.MetricKMedian.PCP.Tableau.clauseEquiv`, `OAI.MetricKMedian.PCP.Tableau.ctrl`, `OAI.MetricKMedian.PCP.Tableau.later` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_Majority`, `KMedian_Amplification_TestSum`, `KMedian_Analysis_ScalarTransfer`, `KMedian_CookLevin_CookSize`, `KMedian_CookLevin_FiniteConstraints`, `KMedian_CookLevin_TM2Locality`, `KMedian_CookLevin_TableauBoundary`, `KMedian_CookLevin_TableauDirectories`, `KMedian_CookLevin_TableauLocal`, `KMedian_CookLevin_TableauRows`, `KMedian_CookLevin_TableauRun`, `KMedian_CookLevin_TableauSystem`, `KMedian_Expanders_Cloud`, `KMedian_Expanders_Stopped`, `KMedian_Machines_LocalCompiler`, `KMedian_Machines_UnaryPolynomial`, `KMedian_PCP_Linearity`, `KMedian_PCP_Tester`, `KMedian_Preparation_NearestAssignmentGeometry`, `KMedian_Preparation_PreparationParameters`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_SupplierAllocation`, `KMedian_Process_PhysicalBatchLaw`, `KMedian_Programs_RestrictionProgram`, `KMedian_Projection_MassNormalize`, `KMedian_Projection_Norm`, `KMedian_Projection_ProductTable`, `KMedian_Projection_SeedCombinators`, `KMedian_Projection_Tables`, `KMedian_Reduction_RationalLocalChoice`, `KMedian_Reduction_RationalThreshold`, `KMedian_Rounding_ExceptionalStar`, `KMedian_Rounding_GridClipping`, `KMedian_Rounding_RationalRetain`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseOuterMoments`, `KMedian_Sparse_SparseStarActivation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K025`, `OAIQ053K026` and `OAIQ053K027`; the statements `OAI.MetricKMedian.Certificates.T1_actual_pos_s53`, `OAI.MetricKMedian.Certificates.T2_actual_pos_s53`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53` and `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`; the proofs of `OAI.MetricKMedian.Certificates.T1_actual_pos_s53`, `OAI.MetricKMedian.Certificates.T2_actual_pos_s53`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53` and `OAI.MetricKMedian.Preparation.exists_rational_all_parameters_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Linearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLinearity

namespace MetricKMedian.PCP
open Finset

section Linearity
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H] [DecidableEq H]

def derivative (f : G → H) (x y : G) : H := f (x + y) - f y

noncomputable def linearityRejects (f : G → H) : ℕ := by
  classical
  exact (univ.filter (fun p : G × G => f (p.1 + p.2) ≠ f p.1 + f p.2)).card

noncomputable def correctionErrors (f : G → H) (x : G) (a : H) : ℕ := by
  classical
  exact (univ.filter (fun y : G => derivative f x y ≠ a)).card

theorem exists_best_anchor (f : G → H) (x : G) :
    ∃ y : G, ∀ z : G, correctionErrors f x (derivative f x y) ≤
      correctionErrors f x (derivative f x z) := by
  classical
  obtain ⟨y, _, hy⟩ := univ.exists_min_image
    (fun z : G => correctionErrors f x (derivative f x z))
    (show (univ : Finset G).Nonempty from ⟨0, mem_univ 0⟩)
  exact ⟨y, fun z => hy z (mem_univ z)⟩

noncomputable def corrected (f : G → H) (x : G) : H :=
  derivative f x (Classical.choose (exists_best_anchor f x))

theorem corrected_min (f : G → H) (x y : G) :
    correctionErrors f x (corrected f x) ≤
      correctionErrors f x (derivative f x y) :=
  (Classical.choose_spec (exists_best_anchor f x)) y

def derivativePairEquiv (x : G) : (G × G) ≃ (G × G) where
  toFun p := (x + p.1, p.2 - p.1)
  invFun q := (q.1 - x, q.2 + q.1 - x)
  left_inv p := by ext <;> dsimp <;> abel
  right_inv q := by ext <;> dsimp <;> abel

theorem shifted_reject_count (f : G → H) (x : G) :
    (univ.filter (fun p : G × G =>
      f (x + p.2) ≠ f (x + p.1) + f (p.2 - p.1))).card =
      linearityRejects f := by
  classical
  apply card_equiv (derivativePairEquiv x)
  intro p
  simp only [mem_filter, mem_univ, true_and, derivativePairEquiv,
    Equiv.coe_fn_mk]
  abel_nf

theorem different_derivatives_bound (f : G → H) (x : G) :
    (univ.filter (fun p : G × G => derivative f x p.1 ≠ derivative f x p.2)).card ≤
      2 * linearityRejects f := by
  classical
  let A := univ.filter (fun p : G × G =>
    f (x + p.2) ≠ f (x + p.1) + f (p.2 - p.1))
  let B := univ.filter (fun p : G × G => f p.2 ≠ f p.1 + f (p.2 - p.1))
  have hsub : (univ.filter (fun p : G × G =>
      derivative f x p.1 ≠ derivative f x p.2)) ⊆ A ∪ B := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_union, A, B] at hp ⊢
    by_contra h
    push Not at h
    apply hp
    simp only [derivative, h.1, h.2]
    abel
  have hA : A.card = linearityRejects f := shifted_reject_count f x
  have hB : B.card = linearityRejects f := by
    simpa only [zero_add] using shifted_reject_count f (0 : G)
  calc
    _ ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le _ _
    _ = _ := by rw [hA, hB]; omega

theorem correction_error_bound (f : G → H) (x : G) :
    Fintype.card G * correctionErrors f x (corrected f x) ≤
      2 * linearityRejects f := by
  classical
  have hsum : (∑ y : G, correctionErrors f x (derivative f x y)) =
      (univ.filter (fun p : G × G => derivative f x p.1 ≠ derivative f x p.2)).card := by
    simp only [correctionErrors, card_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro z _
    simp only [ne_comm]
  calc
    _ = ∑ _y : G, correctionErrors f x (corrected f x) := by simp
    _ ≤ ∑ y : G, correctionErrors f x (derivative f x y) := by
      exact sum_le_sum (fun y _ => corrected_min f x y)
    _ ≤ _ := by rw [hsum]; exact different_derivatives_bound f x

theorem count_translate (p : G → Prop) [DecidablePred p] (y : G) :
    (univ.filter (fun z => p (y + z))).card = (univ.filter p).card := by
  classical
  exact card_equiv (Equiv.addLeft y) (by simp)

omit [AddCommGroup G] in
theorem card_le_of_three_cover (p q r : G → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (h : ∀ z, p z ∨ q z ∨ r z) :
    Fintype.card G ≤ (univ.filter p).card + (univ.filter q).card +
      (univ.filter r).card := by
  classical
  have hs : (univ : Finset G) ⊆ (univ.filter p ∪ univ.filter q) ∪ univ.filter r := by
    intro z _
    simpa only [mem_union, mem_filter, mem_univ, true_and, or_assoc] using h z
  have h₁ := card_union_le (univ.filter p ∪ univ.filter q) (univ.filter r)
  have h₂ := card_union_le (univ.filter p) (univ.filter q)
  have h₃ := card_le_card hs
  simp only [card_univ] at h₃
  omega

theorem corrected_add (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G)
    (x y : G) : corrected f (x + y) = corrected f x + corrected f y := by
  classical
  by_contra hbad
  have hc : ∀ z : G,
      derivative f (x+y) z ≠ corrected f (x+y) ∨
      derivative f x (y+z) ≠ corrected f x ∨
      derivative f y z ≠ corrected f y := by
    intro z
    by_contra hz
    push Not at hz
    apply hbad
    rw [← hz.1, ← hz.2.1, ← hz.2.2]
    dsimp [derivative]
    rw [add_assoc]
    abel
  have hh := card_le_of_three_cover _ _ _ hc
  rw [count_translate (fun z => derivative f x z ≠ corrected f x) y] at hh
  change Fintype.card G ≤ correctionErrors f (x+y) (corrected f (x+y)) +
    correctionErrors f x (corrected f x) + correctionErrors f y (corrected f y) at hh
  have hm := Nat.mul_le_mul_left (Fintype.card G) hh
  have hxy := correction_error_bound f (x+y)
  have hx := correction_error_bound f x
  have hy := correction_error_bound f y
  nlinarith

noncomputable def correctedHom (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G) : G →+ H where
  toFun := corrected f
  map_zero' := by
    have h := corrected_add f hsmall 0 0
    simp only [zero_add] at h
    exact (add_left_cancel (a := corrected f 0) (by simpa using h.symm))
  map_add' := corrected_add f hsmall

noncomputable def tableErrors (f g : G → H) : ℕ := by
  classical
  exact (univ.filter (fun x => f x ≠ g x)).card

end Linearity
end MetricKMedian.PCP

end Inline_PCPLinearity

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Stopped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPStopped

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
variable (t : ℕ)

noncomputable def survival : ℝ := (t:ℝ)/(t+1)
noncomputable def stopping : ℝ := 1/(t+1)

end Stopped

end MetricKMedian.PCP

end Inline_PCPStopped

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Majority
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
variable {cap : ℕ}

noncomputable def totalMass (t L : ℕ) : ℝ :=
  ∑ i ∈ range (L+1), Stopped.stopping t * Stopped.survival t ^ i

end PortGraph

end MetricKMedian.PCP

end Inline_PCPMajority

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_TestSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTestSum

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

noncomputable def testSum {S : Type} [Fintype S] (p : S → Prop) : ℝ :=
  ∑ s, if p s then 1 else 0

end MetricKMedian.PCP

end Inline_PCPTestSum

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def d (s : Bool) : ℝ := if s then 2/5 else 13/25
noncomputable def hh (s : Bool) : ℝ := 8/5 + (2/5) * d s
noncomputable def uZero (s : Bool) : ℝ := d s / hh s
noncomputable def T1 (p x : ℝ) : ℝ :=
  1-p-(28/25)*p*(1+x)+(2/5)*p^2*(1-x)*(1+x)
noncomputable def T2 (p x : ℝ) : ℝ :=
  ((1-p)^2-(19/50)*p*(1-x)+p*x)*(1+x)-2*x*(1-p)
noncomputable def Yprime (p k x : ℝ) : ℝ :=
  1-k+p*((8/5)*(1-x)^2-2)

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Tester
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTester

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace QuadraticSystem

@[simp] theorem derivative_hom {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (g : G →+ H) (x y : G) : derivative g x y = g x := by
  simp [derivative]

end QuadraticSystem
end MetricKMedian.PCP

end Inline_PCPTester

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_FiniteConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteConstraints

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

structure FiniteCSP (V T Q A : Type) where
  query : T → Q → V
  accept : T → Finset (Q → A)
namespace FiniteCSP
variable {V T Q A : Type} [Fintype Q] [Fintype A] [DecidableEq A]
variable [Nonempty Q] [Inhabited A]
variable (C : FiniteCSP V T Q A)
def Satisfies (a : V → A) : Prop := ∀ t, (a ∘ C.query t)∈C.accept t
abbrev Label := A ⊕ (Q → A)
def honest (a : V → A) : V ⊕ T → Label (Q := Q) (A := A) :=
  Sum.elim (fun v => .inl (a v)) (fun t => .inr (a ∘ C.query t))
def decoded (a : V ⊕ T → Label (Q := Q) (A := A)) : V → A :=
  fun v => (a (.inl v)).elim id (fun _ => default)
end FiniteCSP
end MetricKMedian.PCP

end Inline_PCPFiniteConstraints

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TM2Locality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTM2Locality

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def Safe (r : ℕ) (P T : ∀ k, List (Γ k)) : Prop :=
  ∀ k, r≤(P k).length ∨ T k=[]
def appendCfg (c : Cfg Γ Λ σ) (T : ∀ k, List (Γ k)) : Cfg Γ Λ σ :=
  ⟨c.l,c.var,fun k => c.stk k++T k⟩

end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Locality

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRows

namespace MetricKMedian.PCP.Tableau
open scoped Classical

variable {A : Type}
lemma blank_propagates (f : ℕ → Option A) (L : ℕ)
    (h : ∀ i<L, f i=none → f (i+1)=none) (h0 : f 0=none) :
    ∀ i≤L, f i=none := by
  intro i hi
  induction i with
  | zero => exact h0
  | succ i ih => exact h i (by omega) (ih (by omega))
lemma row_list (f : ℕ → Option A) (L : ℕ) (hend : f L=none)
    (h : ∀ i<L, f i=none → f (i+1)=none) :
    ∃ l : List A, l.length≤L ∧ ∀ i≤L, l[i]?=f i := by
  induction L generalizing f with
  | zero =>
    refine ⟨[],by simp,?_⟩
    intro i hi
    have he : i=0 := by omega
    subst i
    simpa using hend.symm
  | succ L ih =>
    cases h0 : f 0 with
    | none =>
      exact ⟨[],by simp,fun i hi => by simpa using (blank_propagates f (L+1) h h0 i hi).symm⟩
    | some a =>
      obtain ⟨l,hl,he⟩ := ih (fun i => f (i+1)) hend (by
        intro i hi hn
        exact h (i+1) (by omega) hn)
      refine ⟨a::l,by simp only [List.length_cons]; omega,?_⟩
      intro i hi
      cases i with
      | zero => simpa using h0.symm
      | succ i => simpa using he i (by omega)

abbrev Row (A : Type) (L : ℕ) := Fin (L+1) → Option A
def rowCell (L : ℕ) (row : Row A L) (i : ℕ) : Option A :=
  if h : i≤L then row ⟨i,by omega⟩ else none
def ValidRow (L : ℕ) (row : Row A L) : Prop :=
  row ⟨L,by omega⟩=none ∧ ∀ i : Fin L,
    row ⟨i.val,by omega⟩=none → row ⟨i.val+1,by omega⟩=none
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRows

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauLocal

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)

def clampedCell {Alphabet : Type} (L : ℕ) (row : Row Alphabet L) (j : ℕ) : Option Alphabet :=
  row ⟨min j L,by omega⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauLocal

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauSystem

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
abbrev Var (T L : ℕ) := Fin (T+1) ⊕ Fin T ⊕ (Fin (T+1) × K × Fin (L+1))
def ctrl (T L : ℕ) (t : Fin (T+1)) : Var (K := K) T L := .inl t
def resp (T L : ℕ) (t : Fin T) : Var (K := K) T L := .inr (.inl t)
def cell (T L : ℕ) (t : Fin (T+1)) (k : K) (i : Fin (L+1)) : Var (K := K) T L :=
  .inr (.inr (t,k,i))
def time0 (T : ℕ) : Fin (T+1) := ⟨0,by omega⟩
def now (T : ℕ) (t : Fin T) : Fin (T+1) := ⟨t.val,by omega⟩
def later (T : ℕ) (t : Fin T) : Fin (T+1) := ⟨t.val+1,by omega⟩
def clamp (L i : ℕ) : Fin (L+1) := ⟨min i L,by omega⟩

inductive Clause (T L : ℕ)
  | shape : Fin (T+1) → K → Fin L → Clause T L
  | end : Fin (T+1) → K → Clause T L
  | prefix : Fin T → Clause T L
  | control : Fin T → Clause T L
  | update : Fin T → K → Fin (L+1) → Clause T L
  deriving DecidableEq, Fintype

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauBoundary

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
abbrev BoundaryClause (L : ℕ) := Bool × (Unit ⊕ (K × Fin (L+1)))
def timeLast (T : ℕ) : Fin (T+1) := ⟨T,by omega⟩
def boundaryTime (T : ℕ) (side : Bool) : Fin (T+1) := if side then timeLast T else time0 T
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauBoundary

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRun

namespace MetricKMedian.PCP.Tableau
open Function Relation

namespace Padded
variable {A : Type} (f : A → Option A)
def next (a : A) : A := (f a).getD a
end Padded

open Turing.TM2

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRun

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation

noncomputable def parameterEnvelopeFar (a : ℝ) : ℝ :=
  max (1/(1-a)) (1+2*a/(1-a^2-a))*((1+a)/(1-a))+(a^2+1+a)*a^5
noncomputable def parameterEnvelopeNear (a : ℝ) : ℝ :=
  1/(1-a)+9*(a^2+1+a)*a^2
noncomputable def parameterEnvelope (a : ℝ) : ℝ :=
  max (parameterEnvelopeFar a) (parameterEnvelopeNear a)/(1-8*a^8)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def unbalanced (Z : Finset E) (ω : E → Bool) : Finset E :=
  univ.filter (fun e => ω e=true ∧ e ∉ Z)

end MetricKMedian.PhysicalBatchLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def target (q : Fin n → Fin m → ℚ) (t : ℕ) (h : Fin n) (i : Fin m) : ℚ :=
  if i.val<t then q h i else 0

theorem target_succ_eq (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m) (h : Fin n) :
    target q (t+1) h ⟨t,ht⟩=q h ⟨t,ht⟩ := by simp [target]

theorem target_succ_ne (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m)
    (h : Fin n) (i : Fin m) (hi : i≠⟨t,ht⟩) : target q (t+1) h i=target q t h i := by
  have hv : i.val≠t := fun he => hi (Fin.ext he)
  have hh : i.val<t+1 ↔ i.val<t := by omega
  simp only [target,hh]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_ExceptionalStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

noncomputable def upperBit (q : ℝ) : ℝ := if 0 < q then 1 else 0

 theorem upperBit_bounds {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ≤ upperBit q ∧ upperBit q ≤ 1 := by
  unfold upperBit
  split_ifs with h
  · exact ⟨hq1, le_rfl⟩
  · exact ⟨le_of_not_gt h, zero_le_one⟩

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {E T Ω : Type} [Fintype E] [DecidableEq T]

theorem grid_clip {Δ : ℕ} {g : ℝ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℝ)=1) (Z : ℕ) :
    min (g*(Z:ℝ)) (1/2)=g*(min Z (Δ/2):ℕ) ∧
    1-min (g*(Z:ℝ)) (1/2)=g*(Δ-min Z (Δ/2):ℕ) ∧
    (1/2:ℝ) ≤ g*(Δ-min Z (Δ/2):ℕ) ∧
    g*(Δ-min Z (Δ/2):ℕ) ≤ 1 := by
  have htwo : Δ/2+Δ/2=Δ := by
    obtain ⟨n,hn⟩ := heven
    omega
  have hhalf : g*(Δ/2:ℕ)= (1/2:ℝ) := by
    have hh : (Δ/2:ℕ)+(Δ/2:ℕ)=(Δ:ℝ) := by exact_mod_cast htwo
    have he := congrArg (fun x : ℝ => g*x) hh
    rw [mul_add,hunit] at he
    linarith only [he]
  have hle : min Z (Δ/2) ≤ Δ := (min_le_right _ _).trans (Nat.div_le_self _ _)
  have hc : min (g*(Z:ℝ)) (1/2)=g*(min Z (Δ/2):ℕ) := by
    rw [← hhalf,Nat.cast_min,mul_min_of_nonneg _ _ hg.le]
  have hm : 1-min (g*(Z:ℝ)) (1/2)=g*(Δ-min Z (Δ/2):ℕ) := by
    rw [hc,Nat.cast_sub hle,mul_sub,hunit]
  refine ⟨hc,hm,?_,?_⟩
  · rw [← hm]
    have hc' : min (g*(Z:ℝ)) (1/2) ≤ (1/2:ℝ) := min_le_right _ _
    linarith only [hc']
  · rw [← hm]
    have hz : 0 ≤ min (g*(Z:ℝ)) (1/2) := le_min (mul_nonneg hg.le (Nat.cast_nonneg _)) (by norm_num)
    linarith only [hz]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationStars
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

 theorem target_card_sum {E : Type} [Fintype E] (D : E → Finset T) (w : E → ℝ) :
    (∑ e, ((D e).card:ℝ)*w e)=∑ t, ∑ e, if t ∈ D e then w e else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

def target (q : Fin n → Fin m → ℚ) (t : ℕ) (h : Fin n) (i : Fin m) : ℚ :=
  if i.val<t then q h i else 0

theorem target_succ_eq (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m) (h : Fin n) :
    target q (t+1) h ⟨t,ht⟩=q h ⟨t,ht⟩ := by simp [target]

theorem target_succ_ne (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m)
    (h : Fin n) (i : Fin m) (hi : i≠⟨t,ht⟩) : target q (t+1) h i=target q t h i := by
  have hv : i.val≠t := fun he => hi (Fin.ext he)
  have hh : i.val<t+1 ↔ i.val<t := by omega
  simp only [target,hh]

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseStarActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

def upper (q : ℚ) : ℚ := if 0 < q then 1 else 0

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
variable {n m : ℕ}

def targetMean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (i : Fin n) : ℚ :=
  ∑ e, if i∈D e then q e else 0

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRetain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalRetain
open Finset

def keep : {n : ℕ} → (Fin n → ℕ) → ℕ → (Fin n → ℕ)
  | 0,_,_ => Fin.elim0
  | n+1,q,k => Fin.cons (min (q 0) k) (keep (fun i : Fin n => q i.succ) (k-min (q 0) k))

theorem le {n : ℕ} (q : Fin n → ℕ) (k : ℕ) : ∀ i, keep q k i ≤ q i := by
  induction n generalizing k with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [keep,Fin.cons_zero] using min_le_left (q 0) k
    · simpa only [keep,Fin.cons_succ] using ih (fun j => q j.succ) (k-min (q 0) k) j

theorem total {n : ℕ} (q : Fin n → ℕ) (k : ℕ) :
    (∑ i,keep q k i)=min (∑ i,q i) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [keep,Fin.cons_zero,Fin.cons_succ]
    rw [ih]
    omega

end MetricKMedian.RationalRetain
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_NearestAssignmentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

noncomputable def relevantRadius (c L R : ℝ) : ℝ := if 0 < c then L else R

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T E : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype E]

def supplierOutside (σ : E → I ⊕ T) (q : E → ℝ) (i : I) : ℝ :=
  ∑ e, if σ e=Sum.inl i then q e else 0

def supplierBundle (σ : E → I ⊕ T) (q : E → ℝ) (t : T) : ℝ :=
  ∑ e, if σ e=Sum.inr t then q e else 0

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def deletionChoices {I : Type} [DecidableEq I] (T : Finset I) (c : ℕ) : Finset (Finset I) :=
  (range (c+1)).biUnion (fun m => T.powersetCard m)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalLocalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def pickSingleton {X : Type*} [LinearOrder X] (K : Finset X) (w : X → ℚ) : Finset X :=
  if hK : K.Nonempty then
    let m := (K.image w).min' (hK.image w)
    let A := K.filter (fun a => w a=m)
    have hA : A.Nonempty := by
      obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (K.image w) (hK.image w))
      exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
    {A.min' hA}
  else ∅

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RestrictionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset
 theorem mem_orderList {n : ℕ} (T : Finset (Fin n)) (i : Fin n) : i∈List.ofFn (T.orderEmbOfFin rfl) ↔ i∈T := by
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨a,rfl⟩; exact T.orderEmbOfFin_mem rfl a
  · intro hi
    have h : i ∈ Set.range (T.orderEmbOfFin rfl) := by rw [T.range_orderEmbOfFin rfl]; exact hi
    exact h
 def pairs {n : ℕ} (T : Finset (Fin n)) : List (Fin n × Fin n) :=
  (List.ofFn (T.orderEmbOfFin rfl)).flatMap (fun i => (List.ofFn (T.orderEmbOfFin rfl)).map (fun j => (i,j)))
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Cloud
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloud

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type} [Fintype V] [Fintype D] [Nonempty D]
  [Fintype S] [Nonempty S]

noncomputable def average (f : V × D → ℝ) : V → ℝ := fun v => 𝔼 d, f (v,d)
def lift (f : V → ℝ) : V × D → ℝ := fun p => f p.1
noncomputable def residual (f : V × D → ℝ) : V × D → ℝ := fun p => f p-lift (average f) p

end PortGraph
end MetricKMedian.PCP

end Inline_PCPCloud

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookSize

namespace MetricKMedian.PCP
open Finset
open scoped Classical

namespace Tableau
variable {K : Type} [Fintype K]
def clauseEquiv (T L : ℕ) : Clause (K := K) T L ≃
    ((Fin (T+1) × K × Fin L) ⊕ (Fin (T+1) × K) ⊕ Fin T ⊕ Fin T ⊕ (Fin T × K × Fin (L+1))) where
  toFun
  | .shape t k i => .inl (t,k,i)
  | .end t k => .inr (.inl (t,k))
  | .prefix t => .inr (.inr (.inl t))
  | .control t => .inr (.inr (.inr (.inl t)))
  | .update t k i => .inr (.inr (.inr (.inr (t,k,i))))
  invFun
  | .inl (t,k,i) => .shape t k i
  | .inr (.inl (t,k)) => .end t k
  | .inr (.inr (.inl t)) => .prefix t
  | .inr (.inr (.inr (.inl t))) => .control t
  | .inr (.inr (.inr (.inr (t,k,i)))) => .update t k i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p|p; rcases p with ⟨a,b,c⟩; rfl; rcases p with p|p; rcases p with ⟨a,b⟩; rfl; rcases p with p|p; rfl; rcases p with p|p; rfl; rfl
end Tableau
end MetricKMedian.PCP

end Inline_PCPCookSize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauDirectories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauDirectories
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Tableau
open scoped Classical

variable {K : Type} (k0 : K)
abbrev VC := Fin 3 × (ℕ × (K × ℕ))
def varCode {T L : ℕ} : Var (K := K) T L → VC (K := K)
  | .inl t => (0,t.val,k0,0)
  | .inr (.inl t) => (1,t.val,k0,0)
  | .inr (.inr (t,k,i)) => (2,t.val,k,i.val)
lemma varCode_injective (T L : ℕ) : Function.Injective (varCode k0 (T := T) (L := L)) := by
  rintro (a|a) (b|b) hab
  · exact congrArg Sum.inl (Fin.ext (congrArg (fun z => z.2.1) hab))
  · rcases b with b|⟨b,k,i⟩ <;> cases congrArg (fun z => z.1.val) hab
  · rcases a with a|⟨a,k,i⟩ <;> cases congrArg (fun z => z.1.val) hab
  · rcases a with a|⟨a,k,i⟩ <;> rcases b with b|⟨b,l,j⟩
    · exact congrArg (fun t => Sum.inr (Sum.inl t)) (Fin.ext (congrArg (fun z => z.2.1) hab))
    · cases congrArg (fun z => z.1.val) hab
    · cases congrArg (fun z => z.1.val) hab
    · have ht : a=b := Fin.ext (congrArg (fun z => z.2.1) hab)
      have hk : k=l := congrArg (fun z => z.2.2.1) hab
      have hi : i=j := Fin.ext (congrArg (fun z => z.2.2.2) hab)
      subst b; subst l; subst j; rfl
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauDirectories

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalCompiler
namespace MetricKMedian.PCP.Compiler
open scoped Classical

namespace LocalCompiler
variable {X VC TC Q A : Type}
  [Fintype Q]
  [Fintype A]
  [DecidableEq A]
  [DecidableEq VC]
  [DecidableEq TC]
  [Inhabited X]
  [Inhabited VC]
  [Inhabited TC]
  [Inhabited Q]
  [Inhabited A]
abbrev Label := FiniteCSP.Label (Q := Q) (A := A)
noncomputable def relation (r : Finset (Q → A)) (q : Q) : Finset (Label (Q := Q) (A := A) × Label (Q := Q) (A := A)) :=
  Finset.univ.filter (fun p => ∃ a b, p=(Sum.inl a,Sum.inr b) ∧ b∈r ∧ a=b q)
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_UnaryPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUnaryPolynomial
namespace MetricKMedian.PCP.Compiler
open Polynomial
open scoped Classical

lemma unitList_eq_length {xs ys : List Unit} (h : xs.length=ys.length) : xs=ys :=
  List.ext_getElem h (by intros; exact Subsingleton.elim _ _)
noncomputable def unaryPower : ℕ → List Unit → List Unit
  | 0, _ => [()]
  | n+1, xs => xs.flatMap (fun _ => unaryPower n xs)
end MetricKMedian.PCP.Compiler

end Inline_PCPUnaryPolynomial

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_MassNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMassNormalize

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MassNormalize
variable {A : Type} [Fintype A] [Inhabited A]
noncomputable def normalized (f : A → ℝ) (H : ℝ) (a : A) : ℝ :=
  if (∑ a, f a)=0 then (if a=default then H else 0) else (H/(∑ a, f a))*f a

end MassNormalize
end MetricKMedian.PCP

end Inline_PCPMassNormalize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionNorm

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {V T : Type} [Fintype V] [Fintype T]

noncomputable def inner (f g : V → T → ℝ) : ℝ := 𝔼 v, ∑ t, f v t*g v t

end MixedNorm
end MetricKMedian.PCP

end Inline_PCPProjectionNorm

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionTables
namespace MetricKMedian.PCP.Compiler
open scoped Classical

abbrev ProjectionRow (A B : Type) := ℕ × (A→B)
abbrev ProjectionTable (A B : Type) := List Unit × List (List (ProjectionRow A B))
namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable {nu : ℕ}
  (ue : U≃Fin nu)
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
include ue in
lemma nu_pos : 0<nu := by
  have hh := Fintype.card_congr ue
  have hp := Fintype.card_pos (α:=U)
  simp only [Fintype.card_fin] at hh
  omega
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_ProductTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionProductTable
namespace MetricKMedian.PCP.Compiler.ProjectionTable
open scoped Classical

variable {A B A' B' : Type} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Inhabited B] [Inhabited B']
noncomputable def combine (n : ℕ) (e : ProjectionRow A B) (f : ProjectionRow A' B') :
    ProjectionRow (A×A') (B×B') := (f.1+n*e.1,fun a=>(e.2 a.1,f.2 a.2))
noncomputable def product (t : ProjectionTable A B) (u : ProjectionTable A' B') : ProjectionTable (A×A') (B×B') :=
  (t.1.flatMap (fun _=>u.1),t.2.flatMap (fun row => u.2.map (fun row' => row.flatMap (fun e => row'.map (combine u.1.length e)))))
end MetricKMedian.PCP.Compiler.ProjectionTable

end Inline_PCPProjectionProductTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedCombinators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedCombinators
namespace MetricKMedian.PCP.Compiler.SeedCombinators

variable {T D A : Type}
noncomputable def source (r : T→ℕ→D→ℕ×D) (t : T) (v : ℕ) (s : D×Bool) : ℕ×D :=
  if s.2 then r t v s.1 else (v,s.1)
variable [Fintype A]
  [Inhabited A]
noncomputable def project (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A) (t : T) (v : ℕ) (s : D×Bool) : (A×A)→A := fun a =>
  let q := source r t v s
  let b := fix t q.1 q.2 a
  if s.2 then b.2 else b.1
noncomputable def numbered (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A)
    (index : D→ℕ) (n : ℕ) (t : T) (v : ℕ) (s : D×Bool) : ℕ×((A×A)→A) :=
  let q := source r t v s
  (index q.2+n*q.1,project r fix t v s)
end MetricKMedian.PCP.Compiler.SeedCombinators

end Inline_PCPSeedCombinators

end OAI
end


