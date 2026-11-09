-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_graphModel
-- name    : MaoLowDegree_Counterexample_graphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:14.04034+00:00
-- url     : https://prove2.me/theorems/2f8a69b8-05dd-4056-b1e0-0d6a84023cef
-- title:
--   Graph laws, vertex relabeling, uniform resampling, and exact small marginals
-- statement:
--   Let $E_n$ be the unordered pairs of distinct vertices in $[n]$, and let $\Omega_n=\{0,1\}^{E_n}$. A graph law is a normalized probability mass function on this finite cube; $Q_n$ is its uniform law. Relabeling by $\tau$ pulls back an edge along $\tau^{-1}$. For a rate $\varepsilon\in[0,1]$, the resampling operator independently keeps each edge with probability $1-\varepsilon$ and otherwise replaces it by an independent fair bit.
--
--   Exact $d$-wise uniformity means that, for every $S\subseteq E_n$ with $|S|\le d$ and pattern $z\in\{0,1\}^S$,
--   $$\Pr_{X\sim P}[X|_S=z]=2^{-|S|}.$$
--
--   These definitions separate vertex symmetry from the stronger symmetry under arbitrary edge-coordinate permutations. Empty coordinate sets have their unique pattern with probability one. The implementation uses increasing endpoint pairs with zero-based labels and includes the empty graph cube at $n=0$. Independent resampling is a fold of normalized one-coordinate kernels, so the probability of changing a given bit is $\varepsilon/2$.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), §1, pp.3–4; §1.3, p.7; Proposition 2.6, p.10

import Mathlib

open Classical
open scoped ENNReal NNReal
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Unordered edges, stored by increasing endpoints (labels are zero based). -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Graph (n : ℕ) := Edge n → Bool
abbrev GraphLaw (n : ℕ) := PMF (Graph n)
abbrev GraphFamily := (n : ℕ) → GraphLaw n

/-- The uniform law on the full graph cube, including the singleton empty cube. -/
def nullLaw (n : ℕ) : GraphLaw n := PMF.uniformOfFintype (Graph n)

/-- Event probability on a finite probability space. -/
def probE {α : Type} [Fintype α] (p : PMF α) (E : α → Prop) : ℝ≥0∞ :=
  ∑ x : α, if E x then p x else 0

def prob {α : Type} [Fintype α] (p : PMF α) (E : α → Prop) : ℝ :=
  (probE p E).toReal

def expect {α : Type} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ x : α, (p x).toReal * f x

/-- Return the unique stored edge joining distinct endpoints. -/
def orderedEdge {n : ℕ} (i j : Fin n) (h : i ≠ j) : Edge n :=
  if hij : i < j then ⟨(i,j), hij⟩ else ⟨(j,i), lt_of_le_of_ne (le_of_not_gt hij) h.symm⟩

/-- Pull back coordinates along the inverse vertex permutation. -/
def relabel {n : ℕ} (τ : Equiv.Perm (Fin n)) (x : Graph n) : Graph n := fun e =>
  x (orderedEdge (τ.symm e.val.1) (τ.symm e.val.2)
    (fun h => (ne_of_lt e.property) (τ.symm.injective h)))

def PermutationInvariant {n : ℕ} (P : GraphLaw n) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), P.map (relabel τ) = P

/-- Rates are genuine probabilities; no clamping or division by a vanishing parameter. -/
abbrev Rate := Set.Icc (0 : ℝ) 1

/-- Resample one coordinate with probability ε, using an independent fair bit. -/
def resampleEdge {n : ℕ} (ε : Rate) (e : Edge n) (P : GraphLaw n) : GraphLaw n :=
  P.bind fun x =>
    (PMF.bernoulli (⟨ε.val, ε.property.1⟩ : ℝ≥0) ε.property.2).bind fun replace =>
      (PMF.uniformOfFintype Bool).map fun bit =>
        if replace then Function.update x e bit else x

/-- Each distinct unordered edge is processed once, with fresh independent choices. -/
def noise {n : ℕ} (ε : Rate) (P : GraphLaw n) : GraphLaw n :=
  (Finset.univ : Finset (Edge n)).toList.foldl (fun Q e => resampleEdge ε e Q) P

/-- Every pattern on every set of at most d coordinates has its exact fair-cube mass. -/
def MarginalUniform {n : ℕ} (P : GraphLaw n) (d : ℕ) : Prop :=
  ∀ S : Finset (Edge n), S.card ≤ d → ∀ z : S → Bool,
    prob P (fun x => ∀ e : S, x e.val = z e) = (2 : ℝ) ^ (-(S.card : ℤ))

end MaoLowDegree.Counterexample


