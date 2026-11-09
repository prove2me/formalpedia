-- Prove2me | Definitions.Def_ProportionalTSP_Exact_Tours
-- name    : ProportionalTSP_Exact_Tours
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:42.997616+00:00
-- url     : https://prove2.me/theorems/3b640a3a-b5ab-4bec-a44b-dab1c6b03c77
-- title:
--   Simple graph tours and the exact exponential target
-- statement:
--   A tour is a spanning simple cycle in a finite simple undirected graph $G$, with cost equal to the sum of its unordered edge costs, each counted once. Real costs may be negative or tied, and edges may be missing. Tour edge sets identify both orientations and all choices of starting vertex. Correct answers either provide an optimal feasible tour or certify that no tour exists.
--
--   For real $\alpha,z$, define
--   $$f_\alpha(z)=2^{2\alpha-1}(2+z+z^2)^{1-\alpha}z^{-\alpha}.$$
--   The predicate $\operatorname{GammaValue}(\alpha,\gamma)$ asserts that $\gamma$ is an attained minimum of this expression over $z\ge1$. It does not assign a default infimum. The finite graph and independence interfaces are shared by the goal and structural milestones.
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), §1, equation (1.1), and §2 standing assumptions, PDF p. 2–3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Mathlib

noncomputable section

namespace ProportionalTSP.Exact

/-- Undirected edge sets identify rotations and reversals of a cycle. -/
def cycleEdges {V : Type} [DecidableEq V] (xs : List V) : Finset (Sym2 V) :=
  (xs.zip (xs.drop 1 ++ xs.take 1)).toFinset.image (fun e => s(e.1, e.2))

def IsTour {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : Finset (Sym2 V)) : Prop :=
  ∃ xs : List V, 3 ≤ xs.length ∧ xs.Nodup ∧ xs.toFinset = Finset.univ ∧
    H = cycleEdges xs ∧ ∀ e ∈ H, e ∈ G.edgeSet

def tourCost {V K : Type} [DecidableEq V] [AddCommMonoid K]
    (w : Sym2 V → K) (H : Finset (Sym2 V)) : K := ∑ e ∈ H, w e

def OptimalTour {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (H : Finset (Sym2 V)) : Prop :=
  IsTour G H ∧ ∀ H', IsTour G H' → tourCost w H ≤ tourCost w H'

def CorrectAnswer {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (ans : Option (Finset (Sym2 V))) : Prop :=
  match ans with
  | none => ¬ ∃ H, IsTour G H
  | some H => OptimalTour G w H

def Independent {V : Type} [DecidableEq V] (G : SimpleGraph V) (R : Finset V) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y

abbrev Vertex (m k : ℕ) := Fin m ⊕ Fin k

/-- The section's graph assumptions, without genericity. -/
def SectionGraph {m k : ℕ} (G : SimpleGraph (Vertex m k)) : Prop :=
  (∀ r s, ¬ G.Adj (.inr r) (.inr s)) ∧ ∀ l r, G.Adj (.inl l) (.inr r)

def cross {m k : ℕ} {K : Type} (w : Sym2 (Vertex m k) → K) (l : Fin m) (r : Fin k) : K :=
  w s(Sum.inl l, Sum.inr r)

/-- Equation (1.1), with the attained-minimum assertion left to the goal. -/
def gammaExpr (α z : ℝ) : ℝ :=
  Real.rpow 2 (2 * α - 1) * Real.rpow (2 + z + z ^ 2) (1 - α) * Real.rpow z (-α)

def GammaValue (α γ : ℝ) : Prop :=
  ∃ z : ℝ, 1 ≤ z ∧ γ = gammaExpr α z ∧ ∀ t : ℝ, 1 ≤ t → γ ≤ gammaExpr α t

end ProportionalTSP.Exact


