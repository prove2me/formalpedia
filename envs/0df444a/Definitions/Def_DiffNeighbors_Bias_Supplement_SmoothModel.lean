-- Prove2me | Definitions.Def_DiffNeighbors_Bias_Supplement_SmoothModel
-- name    : DiffNeighbors_Bias_Supplement_SmoothModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:10:49.314405+00:00
-- url     : https://prove2.me/theorems/00d8a5b1-e1c5-4ad0-a536-f4cd7f41ecc7
-- title:
--   Assumption 2 and §2.2 — scaled outcome functions and smooth interference on the box
-- statement:
--   Let $G$ be an undirected, loopless graph on a finite unit set $I$, let $f_i$ be the potential outcomes, and write $f_i^a(z)=f_i(z^{z_i=a})$. For an interference scale $\delta$, put $B_\delta=[0,\delta]^I$. Smooth interference means
--   $$f_i^a(z)=g_i^a((\delta z_j)_{j\in I}),\qquad |D(Dg_i^a)(x)[e_k][e_j]|\le L\quad(x\in B_\delta,\ j,k\in\mathcal N_i,\ j\ne k).$$
--   Here $a$ is a binary treatment, $z$ a binary vector, and $e_j$ the coordinate basis vector. The predicate requires differentiability of $g_i^a$ and of its within-derivative map on the closed box, without continuity of second derivatives or regularity outside it. Theorems separately require $\delta>0$.
--
--   This is the continuous model behind the finite-difference bounds. The paper's neighbour-coordinate functions extend by projection to all coordinates. The domain follows Assumption 2 on p. 6 and the evaluations $g(\delta z)$, resolving the inconsistent $[0,1]^n$ domain on p. 5. Neither neighborhood interference nor nonnegativity of $L$ is bundled here; Theorem 3 states these separately.
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, pp. 5–6, §2.2, (1), Assumption 2

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

noncomputable section

namespace DiffNeighbors.Bias.Supplement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The box [0, δ]^ι from Assumption 2 (p. 6). Values of g outside this box
are never constrained or used. Theorems require δ > 0. -/
def interferenceBox (δ : ℝ) : Set (ι → ℝ) := Set.Icc 0 (fun _ => δ)

/-- The δ-parameterization of §2.2 (p. 5) and Assumption 2 (p. 6).
The paper's g on neighbour coordinates is extended by composing with the
projection onto the neighbours. No locality condition is imposed here.
Twice differentiability is within the closed box, with no global regularity
or continuity of second derivatives required. The bound is only for distinct
neighbours. L is not required to be nonnegative in this predicate; when there
are no such pairs its derivative-bound clause is vacuous. -/
def SmoothInterference (G : SimpleGraph ι) (f : ι → (ι → Bool) → ℝ)
    (g : ι → Bool → (ι → ℝ) → ℝ) (δ L : ℝ) : Prop :=
  (∀ i a z, condOutcome f i a z = g i a (fun j => δ * ind (z j))) ∧
  (∀ i a, DifferentiableOn ℝ (g i a) (interferenceBox δ)) ∧
  (∀ i a, DifferentiableOn ℝ (fderivWithin ℝ (g i a) (interferenceBox δ))
    (interferenceBox δ)) ∧
  (∀ i a x, x ∈ interferenceBox δ → ∀ j k, G.Adj i j → G.Adj i k → j ≠ k →
    |fderivWithin ℝ (fderivWithin ℝ (g i a) (interferenceBox δ))
      (interferenceBox δ) x (Pi.single k 1) (Pi.single j 1)| ≤ L)

end DiffNeighbors.Bias.Supplement

end


