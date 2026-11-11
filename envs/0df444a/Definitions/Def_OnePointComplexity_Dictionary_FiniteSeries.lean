-- Prove2me | Definitions.Def_OnePointComplexity_Dictionary_FiniteSeries
-- name    : OnePointComplexity_Dictionary_FiniteSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:09.295191+00:00
-- url     : https://prove2.me/theorems/68cd1dab-3954-4f89-a411-6d1c13d46566
-- title:
--   Finite feasible-set cost series and directed tours
-- statement:
--   Let $E$ be a finite ground set, $c:E\to\mathbb N_{>0}$ its costs, and $\mathcal F\subseteq 2^E$ a family of distinct feasible subsets. Define
--
--   $$c(F)=\sum_{e\in F}c(e),\quad A_I(q)=\sum_{F\in\mathcal F}q^{c(F)},\quad
--   \Theta_I(z)=\sum_{F\in\mathcal F}e^{2\pi i c(F)z},\quad
--   \Theta_I(iy)=\sum_{F\in\mathcal F}e^{-2\pi y c(F)}.$$
--
--   The package defines the cost spectrum, minimum cost, total and optimal counts, the extraction height $|E|\ln2/(2\pi)$, evaluation height $(|E|+2)\ln2/\pi$, and accuracy-dependent height. An empty feasible subset is permitted. The minimum defaults to zero for an empty family; theorems invoking optimization require a nonempty family.
--
--   For a directed graph on $n$ vertices, tours are permutations with one orbit on all vertices, supported on the graph's arcs. Each directed Hamiltonian cycle contributes once, independently of a starting vertex. The tour value and threshold $\ln(2n!)/\pi$ are also defined. No completeness or cost-magnitude hypothesis is imposed.
--
--   These objects provide the shared mathematical model of both milestones. Equation (1)'s sum starts at degree zero here: $E=\{e\}$, $c(e)=1$, $\mathcal F=\{\varnothing\}$ has series $1$, contrary to its printed $k\ge1$ coefficient sum. This necessary correction is inherited by the theorem items.
-- source:
--   Varsha Gupta, STOC 2027 submission #1733 (October 2026), §1 equation (1), printed p. 1 (PDF p. 2); §2.1, printed pp. 3–4 (PDF pp. 4–5); §2.3, printed p. 4 (PDF p. 5)

import Mathlib

open scoped BigOperators
set_option autoImplicit false

namespace OnePointComplexity.Dictionary

/-- §2.1, PDF 4: an explicit finite ground set, positive integer costs, and distinct feasible
subsets. Empty feasible members are permitted. No computational operations are supplied. -/
structure Instance where
  n : ℕ
  cost : Fin n → ℕ
  cost_pos : ∀ e, 0 < cost e
  feasible : Finset (Finset (Fin n))

def setCost (I : Instance) (F : Finset (Fin I.n)) : ℕ := ∑ e ∈ F, I.cost e

def spectrum (I : Instance) : Finset ℕ := I.feasible.image (setCost I)

/-- The empty family's default is zero; every optimization theorem assumes a nonempty family. -/
noncomputable def optimum (I : Instance) : ℕ :=
  if h : (spectrum I).Nonempty then (spectrum I).min' h else 0

def feasibleCount (I : Instance) : ℕ := I.feasible.card

noncomputable def optimalCount (I : Instance) : ℕ :=
  (I.feasible.filter fun F => setCost I F = optimum I).card

/-- Equation (1), corrected to include degree zero: E={e}, c(e)=1, F={∅} has polynomial 1. -/
noncomputable def costPolynomial (I : Instance) : Polynomial ℕ :=
  ∑ F ∈ I.feasible, Polynomial.monomial (setCost I F) 1

noncomputable def theta (I : Instance) (z : ℂ) : ℂ :=
  ∑ F ∈ I.feasible, Complex.exp (2 * Real.pi * Complex.I * (setCost I F : ℂ) * z)

noncomputable def thetaImag (I : Instance) (y : ℝ) : ℝ :=
  ∑ F ∈ I.feasible, Real.exp (-2 * Real.pi * y * (setCost I F : ℝ))

noncomputable def extractionHeight (I : Instance) : ℝ := I.n * Real.log 2 / (2 * Real.pi)
noncomputable def evaluationHeight (I : Instance) : ℝ := (I.n + 2) * Real.log 2 / Real.pi
noncomputable def accuracyHeight (I : Instance) (ε : ℝ) : ℝ :=
  evaluationHeight I + Real.log (1 / ε) / (2 * Real.pi)

/-- Symmetric multiplicative approximation to a positive scalar; positivity is part of validity. -/
def Factor (r A B : ℝ) : Prop := 0 < A ∧ 0 < B ∧ A / r ≤ B ∧ B ≤ r * A

/-- §2.1, PDF 5: arbitrary directed graph, including missing arcs. -/
structure TourInstance (n : ℕ) where
  arc : Fin n → Fin n → Bool
  cost : Fin n → Fin n → ℕ
  cost_pos : ∀ a b, arc a b = true → 0 < cost a b

/-- A single orbit on all vertices. Nonemptiness excludes the empty permutation; the
one-vertex loop is retained, consistent with the Hamiltonian-cycle polynomial on PDF 5. -/
def IsTour {n : ℕ} (G : TourInstance n) (σ : Equiv.Perm (Fin n)) : Prop :=
  0 < n ∧ (∀ a b, ∃ k : ℕ, (σ ^ k) a = b) ∧ ∀ a, G.arc a (σ a) = true

noncomputable def tours {n : ℕ} (G : TourInstance n) : Finset (Equiv.Perm (Fin n)) :=
  by
    classical
    exact Finset.univ.filter (IsTour G)

def tourCost {n : ℕ} (G : TourInstance n) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ a, G.cost a (σ a)

/-- All rotations of a directed cycle are one permutation, hence one summand. -/
noncomputable def tourTheta {n : ℕ} (G : TourInstance n) (y : ℝ) : ℝ :=
  ∑ σ ∈ tours G, Real.exp (-2 * Real.pi * y * (tourCost G σ : ℝ))

def IsOptimalTour {n : ℕ} (G : TourInstance n) (σ : Equiv.Perm (Fin n)) : Prop :=
  IsTour G σ ∧ ∀ τ, IsTour G τ → tourCost G σ ≤ tourCost G τ

noncomputable def tourHeight (n : ℕ) : ℝ := Real.log (2 * (n.factorial : ℝ)) / Real.pi

end OnePointComplexity.Dictionary


