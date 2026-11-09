-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Curves
-- name    : GaussProcSparsify_Optimal_Curves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:41.441534+00:00
-- url     : https://prove2.me/theorems/878a8891-dc52-470b-b51d-5b336c6960ad
-- title:
--   Almost-everywhere ODE solutions and L² representatives
-- statement:
--   For a vector field $F:[0,1]\times\mathbb R^N\to\mathbb R^N$, an initial value $a_0$, and a path $a$, the solution convention is
--   $$a\text{ is absolutely continuous on }[0,1],\quad a(0)=a_0,\quad a'(\theta)=F(\theta,a(\theta))\text{ for a.e. }\theta\in[0,1].$$
--   Absolute continuity is Mathlib's metric definition by finite disjoint families of intervals. The equation uses an actual derivative within the interval; existence of a solution is not part of the definition. There is no uniqueness requirement.
--
--   A function $f:\mathbb R^n\to\mathbb R$ represents $h\in L^2(\gamma_n)$ when $h(g)=f(g)$ for $\gamma_n$-almost every $g$. This relation lets Lemma 24 construct the softmax curve and its derivative in the genuine normed $L^2$ space without making an arbitrary choice of pointwise representatives. The definitions encode analytic notions only, and contain no approximation or existence claim.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), §3.1, Step 2, PDF p. 15 (printed p. 14); Lemmas 23–24, PDF pp. 38–39 (printed pp. 37–38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory

namespace GaussProcSparsify.Optimal

/-- The a.e. ODE solution convention of §3.1, Step 2 (PDF p. 15) and Lemma 23
(PDF p. 38). No uniqueness or Lipschitz condition on the vector field is included. -/
def IsODESolution {N : ℕ} (F : ℝ × Vec N → Vec N) (a₀ : Vec N)
    (a : ℝ → Vec N) : Prop :=
  AbsolutelyContinuousOnInterval a 0 1 ∧ a 0 = a₀ ∧
    ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      HasDerivWithinAt a (F (θ, a θ)) (Set.Icc (0 : ℝ) 1) θ

/-- The L² class h is represented by the actual function f, modulo γ_n-null sets.
This is an equality of representatives, not an assumption of the analytic conclusions. -/
def IsL2Representative {n : ℕ} (f : Vec n → ℝ) (h : Lp ℝ 2 (gaussian n)) : Prop :=
  (fun g => h g) =ᵐ[gaussian n] f

end GaussProcSparsify.Optimal


