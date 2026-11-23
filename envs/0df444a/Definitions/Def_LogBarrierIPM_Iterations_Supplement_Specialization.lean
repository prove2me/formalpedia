-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_Supplement_Specialization
-- name    : LogBarrierIPM_Iterations_Supplement_Specialization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:11:02.704909+00:00
-- url     : https://prove2.me/theorems/a7922dae-55f1-4358-938a-c468de75c25e
-- title:
--   Specialization thresholds, neighborhood slices and δ(t)
-- statement:
--   A specialization threshold $t_0>0$ has all three properties of Lemma 18 for every $t>t_0$: strict feasibility, the common optimal value $\nu(t)=c(t)^\top x^*(t)=-b(t)^\top y^*(t)$, and optimality of the evaluated optimal pair. It also exceeds the convergence radii of the finitely many data and optimal-solution series. The fixed-$\mu$ neighborhood slice uses the published wide neighborhood and duality measure.
--   In the common $(x,w,s,y)$ layout, equation (21) is
--   $$\delta(t)=2d_H\bigl(\log_t\mathcal F(t),\operatorname{val}(\mathcal F)\bigr).$$
--   It is nonnegative and may be $+\infty$. No finite default substitutes for an infinite distance.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 17, def-delta

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalLP

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

/-- Both optimal solutions and their common value ν=cᵀx*=-bᵀy*. -/
def OptimalPairReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (z : PDPoint n m) : Prop :=
  z ∈ primalDualFeasible A b c ∧
  (∀ x : Fin n → ℝ, ∀ w : Fin m → ℝ,
    A *ᵥ x + w = b → (∀ j, 0 ≤ x j) → (∀ i, 0 ≤ w i) → c ⬝ᵥ z.1 ≤ c ⬝ᵥ x) ∧
  (∀ s : Fin n → ℝ, ∀ y : Fin m → ℝ,
    s - Aᵀ *ᵥ y = c → (∀ j, 0 ≤ s j) → (∀ i, 0 ≤ y i) →
    b ⬝ᵥ z.2.2.2 ≤ b ⬝ᵥ y) ∧ c ⬝ᵥ z.1 = -(b ⬝ᵥ z.2.2.2)

def ConvergesAt (f : Puiseux) (t : ℝ) : Prop :=
  Summable (fun α : ℝ => |f.coeff α| * t ^ α)

/-- All three properties of Lemma 18, beyond the absolute-convergence radii. -/
def SpecializationThreshold {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (zstar : PuiseuxSlackPoint n m) (t0 : ℝ) : Prop :=
  0 < t0 ∧ ∀ t : ℝ, t0 < t →
    (∀ i j, ConvergesAt (A i j) t) ∧ (∀ i, ConvergesAt (b i) t) ∧
    (∀ j, ConvergesAt (c j) t) ∧
    (strictlyFeasible (evalMatrix A t) (evalFun b t) (evalFun c t)).Nonempty ∧
    OptimalPairReal (evalMatrix A t) (evalFun b t) (evalFun c t) (evalPoint zstar t) ∧
    (∀ i, ConvergesAt (zstar.1 i) t) ∧ (∀ i, ConvergesAt (zstar.2.1 i) t) ∧
    (∀ i, ConvergesAt (zstar.2.2.1 i) t) ∧ ∀ i, ConvergesAt (zstar.2.2.2 i) t

noncomputable def realFeasibleImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (t : ℝ) :
    Set (Fin ((n + m) + (n + m)) → ℝ) :=
  flattenReal '' primalDualFeasible (evalMatrix A t) (evalFun b t) (evalFun c t)

/-- Equation (21); δ(t) is nonnegative and may be +∞. -/
noncomputable def delta {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (t : ℝ) : EReal :=
  2 * hausdorffH (logImage t (realFeasibleImage A b c t)) (tropicalFeasible A b c)

/-- The fixed-μ slice of the existing wide neighborhood, with the same coordinate layout. -/
noncomputable def neighborhoodSlice {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (θ t μ : ℝ) :
    Set (Fin ((n + m) + (n + m)) → ℝ) :=
  flattenReal '' {z ∈ wideNeighborhood (evalMatrix A t) (evalFun b t) (evalFun c t) θ |
    dualityMeasure z = μ}

end LogBarrierIPM.Iterations.Supplement


