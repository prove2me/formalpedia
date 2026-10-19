-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
-- name    : OAI_Combinatorics_ExpectationThreshold_RoundingMasses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:22:36.279183+00:00
-- url     : https://prove2.me/theorems/8e76b29f-f758-49f4-ab65-ff3bda6b61d3
-- title:
--   Spreading fractional weight over members to obtain probability vectors
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A family $\mathcal{G}$ covers $\mathcal{F}$ if every $H\in\mathcal{F}$ contains some $S\in\mathcal{G}$; its cost at density $p$ is $\sum_{S\in\mathcal{G}}p^{|S|}$, and $\mathcal{F}$ is $p$-small if some cover has cost at most $\frac12$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ such that $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost is $\sum_{S\subseteq X}g(S)p^{|S|}$. Fix a fractional cover $g$ and $H\subseteq X$.
--
--   1. **Member mass.** $M_g(H)=\sum_{\emptyset\ne S\subseteq H}g(S)$, so that $M_g(H)+g(\emptyset)=\sum_{S\subseteq H}g(S)$.
--   2. **Rounding mass.** Each nonempty $S\subseteq H$ splits its weight equally among its elements:
--   $$
--   \pi_H(x)=\frac{1}{M_g(H)}\sum_{\substack{\emptyset\ne S\subseteq H\\ x\in S}}\frac{g(S)}{|S|}.
--   $$
--   3. **Properties.** If $H\in\mathcal{F}$ and $g$ has cost at most $\frac12$ at some $r\ge0$, then $M_g(H)\ge\frac12>0$. In that case $\pi_H$ is nonnegative, vanishes outside $H$, and sums to $1$. The average of a function $a$ over $S$ is $\frac1{|S|}\sum_{x\in S}a(x)$.
--
--   These probability vectors are the member masses fed into the selector argument. Their means relate color averages over subsets to the fractional weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingMasses.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingMasses.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandExpectationThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Concrete rounding masses

Each nonempty subset's fractional weight is split equally among its members.
Normalizing by the total nonempty-subset weight gives the probability mass used
by the common selector. Both normalization and the mean identity are finite
double-sum calculations.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

def nonemptySubsets (H : Finset α) : Finset (Finset α) := H.powerset.erase ∅

def memberMass (g : Finset α → ℝ) (H : Finset α) : ℝ :=
  ∑ S ∈ nonemptySubsets H, g S

def subsetAverage (a : α → ℝ) (S : Finset α) : ℝ :=
  (∑ x ∈ S, a x) / (S.card : ℝ)

def roundingMass (g : Finset α → ℝ) (H : Finset α) (x : α) : ℝ :=
  (∑ S ∈ nonemptySubsets H, if x ∈ S then g S / (S.card : ℝ) else 0) /
    memberMass g H

omit [Fintype α] in
@[simp] theorem mem_nonemptySubsets {S H : Finset α} :
    S ∈ nonemptySubsets H ↔ S ≠ ∅ ∧ S ⊆ H := by
  simp only [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset]

omit [Fintype α] in
theorem memberMass_add_empty (g : Finset α → ℝ) (H : Finset α) :
    memberMass g H + g ∅ = ∑ S ∈ H.powerset, g S := by
  exact Finset.sum_erase_add H.powerset g (Finset.empty_mem_powerset H)

omit [DecidableEq α] in
theorem empty_weight_le_half {r : ℝ} {g : Finset α → ℝ}
    (hr : 0 ≤ r) (hg : ∀ S, 0 ≤ g S) (hcost : fracCost r g ≤ 1 / 2) :
    g ∅ ≤ 1 / 2 :=
  (empty_weight_le_fracCost hr hg).trans hcost

theorem memberMass_ge_half {F : Family α} {g : Finset α → ℝ}
    {H : Finset α} {r : ℝ} (hcover : FractionalCover F g) (hH : H ∈ F)
    (hr : 0 ≤ r) (hcost : fracCost r g ≤ 1 / 2) :
    1 / 2 ≤ memberMass g H := by
  have hcoverage := hcover.2 H hH
  have hempty := empty_weight_le_half hr hcover.nonneg hcost
  have hsplit := memberMass_add_empty g H
  linarith

theorem memberMass_pos_of_fractionalCover {F : Family α} {g : Finset α → ℝ}
    {H : Finset α} {r : ℝ} (hcover : FractionalCover F g) (hH : H ∈ F)
    (hr : 0 ≤ r) (hcost : fracCost r g ≤ 1 / 2) :
    0 < memberMass g H := by
  have hmass := memberMass_ge_half hcover hH hr hcost
  linarith

omit [Fintype α] in
theorem roundingMass_nonneg (g : Finset α → ℝ) (H : Finset α)
    (hg : ∀ S, 0 ≤ g S) (hM : 0 < memberMass g H) (x : α) :
    0 ≤ roundingMass g H x := by
  apply div_nonneg _ hM.le
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact div_nonneg (hg S) (Nat.cast_nonneg _)
  · exact le_rfl

omit [Fintype α] in
theorem roundingMass_eq_zero_of_not_mem (g : Finset α → ℝ) (H : Finset α)
    {x : α} (hx : x ∉ H) : roundingMass g H x = 0 := by
  have hsum :
      (∑ S ∈ nonemptySubsets H, if x ∈ S then g S / (S.card : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hxS : x ∉ S := fun h => hx ((mem_nonemptySubsets.mp hS).2 h)
    simp only [ite_eq_right hxS]
  unfold roundingMass
  rw [hsum, zero_div]

/-- A nonempty set distributes exactly its original weight. -/
theorem sum_uniform_subset_weight (g : Finset α → ℝ) (S : Finset α)
    (hS : S ≠ ∅) :
    (∑ x : α, if x ∈ S then g S / (S.card : ℝ) else 0) = g S := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
  rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ (g S) hcard

/-- Counting each set's members evaluates the full double sum. -/
theorem sum_rounding_numerator (g : Finset α → ℝ) (H : Finset α) :
    (∑ x : α, ∑ S ∈ nonemptySubsets H,
      if x ∈ S then g S / (S.card : ℝ) else 0) = memberMass g H := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  exact sum_uniform_subset_weight g S (mem_nonemptySubsets.mp hS).1

theorem roundingMass_sum (g : Finset α → ℝ) (H : Finset α)
    (hM : 0 < memberMass g H) : (∑ x : α, roundingMass g H x) = 1 := by
  simp only [roundingMass, ← Finset.sum_div]
  rw [sum_rounding_numerator, div_self hM.ne']

end
end TalagrandThreshold

end OAI


