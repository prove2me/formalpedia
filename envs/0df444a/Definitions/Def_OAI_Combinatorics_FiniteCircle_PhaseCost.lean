-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
-- name    : OAI_Combinatorics_FiniteCircle_PhaseCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:39:07.31159+00:00
-- url     : https://prove2.me/theorems/bff6171b-91e5-4c0e-a84e-21bcc3b716df
-- title:
--   Circle cost on $\mathbb{Z}/M$ and averaged phase costs on abelian groups
-- statement:
--   Let $M\in\mathbb{N}$ and write $\mathbb{Z}/M$ for the integers modulo $M$. The module introduces translation-invariant cost functions on abelian groups and an averaging operation that produces new ones.
--
--   1. **Circle cost.** For $x\in\mathbb{Z}/M$ let $\tilde x\in\mathbb{Z}$ be the representative of $x$ of least absolute value (the one in $(-M/2,M/2]$) and put
--   $$
--   \operatorname{cc}(x)=\frac{|\tilde x|}{M}.
--   $$
--   For $M\ge1$ this is the distance from $x/M$ to the nearest integer, i.e. the normalized circular distance from $0$ to $x$ on a cycle of length $M$. The module proves $\operatorname{cc}(0)=0$, $\operatorname{cc}(x)\ge0$, $\operatorname{cc}(-x)=\operatorname{cc}(x)$ and $\operatorname{cc}(x+y)\le\operatorname{cc}(x)+\operatorname{cc}(y)$.
--   2. **Phase costs.** For an abelian group $G$, a phase cost is a function $f:G\to\mathbb{R}$ such that, for all $x,y\in G$, $f(x)\ge0$, $f(0)=0$, $f(-x)=f(x)$ and $f(x+y)\le f(x)+f(y)$; equivalently $(x,y)\mapsto f(x-y)$ is a translation-invariant pseudometric. The circle cost is a phase cost on $\mathbb{Z}/M$.
--   3. **Averages along a mask.** Let $J$ be a finite index set, $H$ an abelian group and $\sigma:H\to G^J$ a group homomorphism, which assigns to each $s\in H$ a family of shifts $\sigma(s)_j$. For a phase cost $f$, $x\in G$ and $s\in H$,
--   $$
--   \operatorname{avg}_{f,\sigma}(x,s)=\frac{1}{|J|}\sum_{j\in J}f\bigl(x+\sigma(s)_j\bigr).
--   $$
--   When $J$ is nonempty, $\operatorname{avg}_{f,\sigma}(x,0)=f(x)$; moreover $\operatorname{avg}(-x,-s)=\operatorname{avg}(x,s)$ and $\operatorname{avg}(x+y,s+t)\le\operatorname{avg}(x,s)+\operatorname{avg}(y,t)$.
--   4. **Minimized average and the step operation.** For finite $H$, the minimized average is $\min_{s\in H}\operatorname{avg}_{f,\sigma}(x,s)$. The module shows that the minimum is attained, that it is nonnegative, vanishes at $x=0$, is even in $x$ and is subadditive in $x$. Hence
--   $$
--   (\operatorname{step}_\sigma f)(x)=\min_{s\in H}\frac{1}{|J|}\sum_{j\in J}f\bigl(x+\sigma(s)_j\bigr)
--   $$
--   is again a phase cost on $G$.
--
--   Iterating the step operation along a hierarchy of masks produces the level-by-level costs that bound from below how much a finite-circle word changes when its phases are rotated. Because each step returns a phase cost, the triangle inequality survives every level and the recursion can be continued.
--
--   **Formalization Note** `circleCost` uses `ZMod.valMinAbs`; for $M=0$ (where `ZMod 0` is the integers) Lean's convention of division by zero makes the cost identically $0$. `PhaseCost G` is a structure bundling the function with its four axioms and is coerced to a function; `average` divides by the cardinality of $J$ (giving $0$ when $J$ is empty), `infAverage` is a finite infimum `Finset.inf'` over $H$, and `step` packages `infAverage` with the proofs of the axioms; `circlePhaseCost M` is the circle cost as a phase cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/PhaseCost.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/PhaseCost.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

noncomputable def circleCost {M : ℕ} (x : ZMod M) : ℝ := x.valMinAbs.natAbs / (M : ℝ)

@[simp] theorem circleCost_zero (M : ℕ) : circleCost (0 : ZMod M) = 0 := by
  simp [circleCost]

theorem circleCost_nonneg {M : ℕ} (x : ZMod M) : 0 ≤ circleCost x := by
  unfold circleCost
  positivity

@[simp] theorem circleCost_neg {M : ℕ} (x : ZMod M) : circleCost (-x) = circleCost x := by
  simp [circleCost, ZMod.natAbs_valMinAbs_neg]

theorem circleCost_add_le {M : ℕ} (x y : ZMod M) :
    circleCost (x+y) ≤ circleCost x + circleCost y := by
  have h := (ZMod.natAbs_valMinAbs_add_le x y).trans (Int.natAbs_add_le _ _)
  unfold circleCost
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h

structure PhaseCost (G : Type*) [AddCommGroup G] where
  toFun : G → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  zero : toFun 0 = 0
  neg : ∀ x, toFun (-x) = toFun x
  add_le : ∀ x y, toFun (x+y) ≤ toFun x + toFun y

instance {G : Type*} [AddCommGroup G] : CoeFun (PhaseCost G) (fun _ => G → ℝ) := ⟨PhaseCost.toFun⟩

noncomputable def circlePhaseCost (M : ℕ) : PhaseCost (ZMod M) :=
  ⟨circleCost, circleCost_nonneg, circleCost_zero M, circleCost_neg, circleCost_add_le⟩

namespace PhaseCost
variable {G H J : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H] [Fintype J]

noncomputable def average (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) (s : H) : ℝ :=
  (∑ j, f (x + σ s j)) / Fintype.card J

noncomputable def infAverage (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (f.average σ x)

theorem infAverage_le (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) (s : H) :
    f.infAverage σ x ≤ f.average σ x s :=
  Finset.inf'_le _ (Finset.mem_univ s)

theorem exists_average_eq (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    ∃ s : H, f.infAverage σ x = f.average σ x s := by
  obtain ⟨s,_,hs⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (f.average σ x)
  exact ⟨s,hs⟩

theorem infAverage_nonneg (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    0 ≤ f.infAverage σ x := by
  apply Finset.le_inf'
  intro s _
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => f.nonneg _)) (by positivity)

omit [Fintype H] in
@[simp] theorem average_zero_mask [Nonempty J] (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    f.average σ x 0 = f x := by
  simp only [average, map_zero, Pi.zero_apply, add_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J).ne')

@[simp] theorem infAverage_zero (f : PhaseCost G) (σ : H →+ (J → G)) :
    f.infAverage σ 0 = 0 := by
  apply le_antisymm
  · refine (f.infAverage_le σ 0 0).trans_eq ?_
    simp only [average, map_zero, Pi.zero_apply, add_zero, f.zero,
      Finset.sum_const_zero, zero_div]
  · exact f.infAverage_nonneg σ 0

omit [Fintype H] in
@[simp] theorem average_neg (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) (s : H) :
    f.average σ (-x) (-s) = f.average σ x s := by
  unfold average
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he : -x+σ (-s) j = -(x+σ s j) := by simp [add_comm]
  rw [he, f.neg]

@[simp] theorem infAverage_neg (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    f.infAverage σ (-x) = f.infAverage σ x := by
  have aux (x : G) : f.infAverage σ (-x) ≤ f.infAverage σ x := by
    obtain ⟨s,hs⟩ := f.exists_average_eq σ x
    rw [hs]
    simpa using f.infAverage_le σ (-x) (-s)
  exact le_antisymm (aux x) (by simpa using aux (-x))

omit [Fintype H] in
theorem average_add_le (f : PhaseCost G) (σ : H →+ (J → G)) (x y : G) (s t : H) :
    f.average σ (x+y) (s+t) ≤ f.average σ x s + f.average σ y t := by
  unfold average
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have he : x+y+σ (s+t) j = (x+σ s j)+(y+σ t j) := by
    simp only [map_add, Pi.add_apply]
    abel
  rw [he]
  exact f.add_le _ _

theorem infAverage_add_le (f : PhaseCost G) (σ : H →+ (J → G)) (x y : G) :
    f.infAverage σ (x+y) ≤ f.infAverage σ x + f.infAverage σ y := by
  obtain ⟨s,hs⟩ := f.exists_average_eq σ x
  obtain ⟨t,ht⟩ := f.exists_average_eq σ y
  rw [hs,ht]
  exact (f.infAverage_le σ (x+y) (s+t)).trans (f.average_add_le σ x y s t)

noncomputable def step (f : PhaseCost G) (σ : H →+ (J → G)) : PhaseCost G :=
  ⟨f.infAverage σ, f.infAverage_nonneg σ, f.infAverage_zero σ,
    f.infAverage_neg σ, f.infAverage_add_le σ⟩

end PhaseCost

end FiniteCircle

end OAI


