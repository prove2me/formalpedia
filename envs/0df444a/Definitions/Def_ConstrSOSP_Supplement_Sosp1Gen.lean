-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_Sosp1Gen
-- name    : ConstrSOSP_Supplement_Sosp1Gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:25:52.896362+00:00
-- url     : https://prove2.me/theorems/20a3775a-2600-4196-836c-e976c1a785c0
-- title:
--   Sosp1: the total white-box problem of Definition 4.6
-- statement:
--   **Sosp1.** Input: precision parameters $\epsilon_G,\epsilon_H>0$; $A\in\mathbb R^{m\times d}$, $B\in\mathbb R^m$ defining a bounded non-empty domain $\mathcal X=\{x\in\mathbb R^d: Ax\le B\}$; Turing machines for $f$, $\nabla f$, $\nabla^2 f$; Lipschitz constants $L,L_1,L_2>0$. Goal: find $x^*\in\mathcal X$ with
--
--   $$\|g_\pi(x^*)\|\le\epsilon_G,\qquad y^\top\nabla^2 f(x^*)\,y\ge-\epsilon_H\quad\forall y:\ A'(x^*)y=0,\ \|y\|=1,$$
--
--   where $g_\pi(x)=L_1\big(\pi_{\mathcal X}(x-\tfrac1{L_1}\nabla f(x))-x\big)$ is the proximal gradient and $A'(x^*)$ collects the active constraints; or else a regularity violation.
--
--   Every dimension $d$ and every bounded non-empty rational polytope is allowed.
--
--   **Formalization Note** The SOSP1 test is the base mission's `IsSOSP1`, with the instance's $L_1$. $K$ is the exponent of the machines' clock and is fixed by the problem.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.6, pp.19–20; Definition 4.4, p.19

import Mathlib
import Definitions.Def_ConstrSOSP_IsSOSP1
import Definitions.Def_ConstrSOSP_Supplement_GenProblem

namespace ConstrSOSP.Supplement

open ConstrSOSP

/-- **Sosp1** (Kontogiannis, Panageas & Pollatos, arXiv:2604.02285, 2 Nov 2026, Definition 4.6,
pp.19–20): "Input: precision parameters ϵG, ϵH > 0, A ∈ R^{m×d}, B ∈ R^m defining a bounded
non-empty domain X = {x ∈ R^d : Ax ≤ B}, Turing machine for f : R^d → R, ∇f : R^d → R^d and
∇²f : R^d → R^{d×d}, Lipschitz constants L, L1, L2 > 0. Goal: Find a point x* ∈ X such that:
‖gπ(x*)‖ ≤ ϵG, (7a) yᵀ∇²f(x*)y ≥ −ϵH, ∀ y s.t. A′(x*)y = 0 and ‖y‖ = 1 (7b). Alternatively, we
also accept one of the following violations as a solution: …".

The instances are those of `ValidGen K (fun _ => True)` (every dimension `d`, every bounded
non-empty rational polytope); an answer is a rational `(ϵG, ϵH)`-SOSP1 (`ConstrSOSP.IsSOSP1`:
proximal gradient with the instance's `L₁`, second-order test on Euclidean unit vectors in the null
space of the active rows) or a violation pair.

**Formalization Note** `K` is the exponent of the machines' clock `T · (|w| + 1)^K`, fixed by the
problem. -/
def Sosp1Gen (K : ℕ) : TetrisHard.Rows.SearchProblem :=
  GenProblem K (fun _ => True)
    (fun _ _ A B L1 ϵG ϵH x g H => IsSOSP1 A B L1 ϵG ϵH x g H)

end ConstrSOSP.Supplement


