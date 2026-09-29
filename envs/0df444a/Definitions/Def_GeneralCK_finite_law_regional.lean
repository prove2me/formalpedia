-- Prove2me | Definitions.Def_GeneralCK_finite_law_regional
-- name    : GeneralCK_finite_law_regional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T23:03:09.984696+00:00
-- url     : https://prove2.me/theorems/89bbabf4-5799-4213-9ddf-912fc5736acc
-- title:
--   Finite interior laws and the two canonical Bellman regions
-- statement:
--   A finite interior law consists of nonnegative weights summing to one and two values in $(0,1)$ at each index. Its means are $a,b$, its mean binary entropies are $e,f$, its average edge cost is cost, and its Bellman gap is $B((a+b)/2,(e+f)/2)-(B(a,e)+B(b,f))/2$. The exact source definitions include swapping the two values and complementing both. The proposition Inputs requires gap $\le$ cost for every canonical law with $a\le b$ and $a+b\le1$, separately when $b\le1/2$ and $b\ge1/2$. These are full regional mathematical obligations; the bundle asserts neither one.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FiniteLaw.lean#L8-L102

import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GeneralCK
open scoped BigOperators

structure InteriorLaw (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  left : ι → ℝ
  right : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  left_interior : ∀ i, 0 < left i ∧ left i < 1
  right_interior : ∀ i, 0 < right i ∧ right i < 1

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

noncomputable def avg (μ : InteriorLaw ι) (v : ι → ℝ) : ℝ := ∑ i, μ.weight i * v i
noncomputable def a (μ : InteriorLaw ι) : ℝ := μ.avg μ.left
noncomputable def b (μ : InteriorLaw ι) : ℝ := μ.avg μ.right
noncomputable def e (μ : InteriorLaw ι) : ℝ := μ.avg (H ∘ μ.left)
noncomputable def f (μ : InteriorLaw ι) : ℝ := μ.avg (H ∘ μ.right)
noncomputable def cost (μ : InteriorLaw ι) : ℝ :=
  μ.avg (fun i => interiorCost (μ.left i) (μ.right i))
noncomputable def gap (μ : InteriorLaw ι) : ℝ :=
  B ((μ.a + μ.b) / 2) ((μ.e + μ.f) / 2) - (B μ.a μ.e + B μ.b μ.f) / 2
























def swap (μ : InteriorLaw ι) : InteriorLaw ι where
  weight := μ.weight
  left := μ.right
  right := μ.left
  weight_nonneg := μ.weight_nonneg
  weight_sum := μ.weight_sum
  left_interior := μ.right_interior
  right_interior := μ.left_interior

def complement (μ : InteriorLaw ι) : InteriorLaw ι where
  weight := μ.weight
  left := fun i => 1 - μ.left i
  right := fun i => 1 - μ.right i
  weight_nonneg := μ.weight_nonneg
  weight_sum := μ.weight_sum
  left_interior := fun i => by have := μ.left_interior i; constructor <;> linarith
  right_interior := fun i => by have := μ.right_interior i; constructor <;> linarith










end InteriorLaw







namespace InteriorLaw
variable {ι : Type*} [Fintype ι]








end InteriorLaw



end GeneralCK

namespace GeneralCK.ArchiveRegionalBoundary

structure Inputs : Prop where
  sameSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → μ.b ≤ 1 / 2 → μ.gap ≤ μ.cost
  oppositeSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b → μ.gap ≤ μ.cost








end GeneralCK.ArchiveRegionalBoundary


