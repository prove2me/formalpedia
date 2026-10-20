-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
-- name    : OAI_Analysis_Cotype_ProjectionSpectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:48:52.403817+00:00
-- url     : https://prove2.me/theorems/fb738757-c7f2-45f4-8ebb-53382f17a725
-- title:
--   Spectral patterns of commuting projections
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$.
--
--   1. **Patterns.** For $\varepsilon\in\{0,1\}^m$, $Q_\varepsilon=\prod_i\bigl(1-P_i\text{ if }\varepsilon_i=1,\ \text{else }P_i\bigr)$.
--   2. **Spectral decomposition.** Products of patterns satisfy $Q_\varepsilon Q_\eta=[\varepsilon=\eta]\,Q_\varepsilon$ when the $P_i$ are commuting idempotents, and
--   $$
--   \sum_\varepsilon Q_\varepsilon=1 .
--   $$
--   So $T(r)=\sum_\varepsilon r^{|\varepsilon|}Q_\varepsilon$ and $L=\sum_{|\varepsilon|=1}Q_\varepsilon$, with $L$ the projection onto degree one. Pointwise products of products are products of pointwise products, and a zero factor kills a product.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionSpectrum.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionSpectrum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def projectionPattern {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (ε : Cube m) : Y →L[ℝ] Y :=
  projectionProduct (fun i => if ε i then 1-P i else P i)

theorem projectionProduct_pointwise_mul {m : ℕ} (P Q : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (Q j)) :
    projectionProduct P * projectionProduct Q = projectionProduct (fun i => P i * Q i) := by
  induction m with
  | zero => simp [projectionProduct]
  | succ m ih =>
    have hm := projectionProduct_commute (fun i => P i.succ) (Q 0)
      (fun i => hc i.succ 0)
    have ht := ih (fun i => P i.succ) (fun i => Q i.succ)
      (fun i j => hc i.succ j.succ)
    simp only [projectionProduct]
    rw [mul_assoc, ← mul_assoc (projectionProduct _), hm.eq, mul_assoc, ht, ← mul_assoc]

theorem projectionProduct_zero_of_factor {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (i : Fin m) (hi : P i = 0) : projectionProduct P = 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i hi
    · intro h
      simp [projectionProduct, h]
    · intro h
      simp only [projectionProduct]
      rw [ih (fun j => P j.succ) j h, mul_zero]

theorem projectionPattern_factor_commute (P Q : Y →L[ℝ] Y)
    (h : Commute P Q) (b c : Bool) :
    Commute (if b then 1-P else P) (if c then 1-Q else Q) := by
  have h1 : Commute P (1-Q) := (Commute.one_right P).sub_right h
  have h2 : Commute (1-P) Q := (Commute.one_left Q).sub_left h
  have h3 : Commute (1-P) (1-Q) := (Commute.one_right _).sub_right h2
  cases b <;> cases c
  · exact h
  · exact h1
  · exact h2
  · exact h3

theorem projectionPattern_mul {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube m) :
    projectionPattern P ε * projectionPattern P η =
      if ε = η then projectionPattern P ε else 0 := by
  classical
  unfold projectionPattern
  rw [projectionProduct_pointwise_mul _ _
    (fun i j => projectionPattern_factor_commute _ _ (hc i j) _ _)]
  by_cases he : ε = η
  · subst η
    rw [ite_eq_left rfl]
    congr 1
    funext i
    cases ε i
    · exact hp i
    · simp only [ite_true, sub_mul, mul_sub, one_mul, mul_one, hp i]
      abel
  · rw [ite_eq_right he]
    obtain ⟨i, hi⟩ : ∃ i, ε i ≠ η i := by
      by_contra! h
      exact he (funext h)
    apply projectionProduct_zero_of_factor _ i
    cases hε : ε i <;> cases hη : η i <;> simp_all [sub_mul, mul_sub]

theorem projectionPattern_sum {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    (∑ ε : Cube m, projectionPattern P ε) = 1 := by
  have h := projectionProduct_weighted_sum (fun (_ : Fin m) (_ : Bool) => (1 : ℝ))
    (fun i (b : Bool) => if b then 1-P i else P i)
  simpa [Fintype.sum_bool, projectionPattern, projectionProduct_one] using h.symm

end Cotype

end

end OAI


