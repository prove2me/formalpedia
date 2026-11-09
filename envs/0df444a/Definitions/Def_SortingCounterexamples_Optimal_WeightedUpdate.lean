-- Prove2me | Definitions.Def_SortingCounterexamples_Optimal_WeightedUpdate
-- name    : SortingCounterexamples_Optimal_WeightedUpdate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:54.469223+00:00
-- url     : https://prove2.me/theorems/7d9c7218-2fe2-44cd-ab1c-a12aafc6e1aa
-- title:
--   §4.1 — cube, ranking cells, uniform cell law, barycenter, surrogate loss and the weighted update (1)
-- statement:
--   This file fixes the geometric objects of the upper bound (§4.1, pp. 15–17).
--
--   1. **Cube and cells.** $B=[0,1]^n\subset\mathbb R^n$. For a ranking $\pi$ (listing items by position), the cell is
--   $$C_\pi=\{x\in(0,1)^n:\ x_{\pi(1)}<x_{\pi(2)}<\dots<x_{\pi(n)}\}.$$
--   The **uniform law on $C_\pi$** is Lebesgue measure restricted to $C_\pi$ and divided by $\mathrm{vol}(C_\pi)$.
--   2. **Mass and barycenter.** For a weight $w:\mathbb R^n\to\mathbb R$, $W=\int_{[0,1]^n}w(x)\,dx$ and the barycenter of the density $p=w/W$ on the cube is $c=W^{-1}\int_{[0,1]^n}x\,w(x)\,dx$.
--   3. **Sorting.** A ranking $\pi$ *sorts* $c$ when $c_{\pi(1)}\le c_{\pi(2)}\le\dots\le c_{\pi(n)}$ (the ranking obtained by sorting the coordinates of $c$, ties broken arbitrarily).
--   4. **Surrogate loss.** For a query $\pi$ and a returned pair $\{i,j\}$, oriented so that $\pi$ places $i$ before $j$, put $z(x)=x_j-x_i$ and
--   $$\ell(x)=\bigl(1+\gamma n\,z(x)\bigr)_+,\qquad (a)_+=\max\{a,0\}.$$
--   5. **Weighted update (1).** Starting from $w_0(x)=1$, each round with query $\pi_t$ and returned pair $s_t$ sets $w_{t+1}(x)=w_t(x)\,e^{-\ell_t(x)}$; $w_t$ denotes the weight after a transcript of $t$ rounds.
--   6. **The learner.** The weighted learner queries a ranking sorting the barycenter $c_t$ of $w_t$; the file fixes the label tie-break (via `Tuple.sort`) for a concrete deterministic learner. It uses only the transcript, never the lie budget.
--
--   These are the objects of Lemmas 4.2–4.4.
--
--   **Formalization Note** The weight is defined on all of $\mathbb R^n$, and every integral is restricted to the cube, as in the source. The mass is positive and the barycenter integrand integrable for every transcript (the weight is continuous, positive and at most $1$), so the Bochner integrals and the division are never at a junk value. The milestones quantify over every ranking that sorts the barycenter, so no tie rule is imposed on them.
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed pp. 15–16 / PDF pp. 16–17, §4.1: cells C_π, Grünbaum preamble, 'The weighted update' (w_0 = 1, W_t, p_t, c_t, z_t, ℓ_t, update (1)); printed p. 17 / PDF p. 18: target cell C⋆ and the uniform distribution Q on C⋆

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol

open MeasureTheory

namespace SortingCounterexamples.Optimal

/-- The unit cube `[0,1]^n`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.Icc 0 1

/-- The open cell `C_π = {x ∈ (0,1)^n : x_{π(1)} < ⋯ < x_{π(n)}}` of the ranking `π`. -/
def cell {n : ℕ} (π : Ranking n) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i ∧ x i < 1) ∧ ∀ a b : Fin n, a < b → x (π a) < x (π b)}

/-- The uniform probability law on the cell `C_π`: Lebesgue measure restricted to `C_π`
and normalized by `vol(C_π)`. -/
noncomputable def cellUniform {n : ℕ} (π : Ranking n) : Measure (Fin n → ℝ) :=
  ProbabilityTheory.cond volume (cell π)

/-- The total mass `W = ∫_{[0,1]^n} w(x) dx` of a weight function. -/
noncomputable def mass {n : ℕ} (w : (Fin n → ℝ) → ℝ) : ℝ := ∫ x in cube n, w x

/-- The barycenter `E_{X∼p}[X]` of the normalized density `p = w / W` on `[0,1]^n`. -/
noncomputable def barycenter {n : ℕ} (w : (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  (mass w)⁻¹ • ∫ x in cube n, w x • x

/-- The ranking `π` lists the items in nondecreasing order of the coordinates of `c`:
`π` is a ranking "obtained by sorting the coordinates of `c`, breaking ties arbitrarily". -/
def SortsCoords {n : ℕ} (c : Fin n → ℝ) (π : Ranking n) : Prop :=
  Monotone (c ∘ π)

/-- `z(x) = x_j - x_i` for the returned pair `s = {i, j}`, oriented so that the query `π`
places `i` before `j`. -/
def gap {n : ℕ} (π : Ranking n) (s : ItemPair n) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ s.1, ∑ j ∈ s.1, if π.Before i j then x j - x i else 0

/-- The surrogate loss `ℓ(x) = (1 + γ n z(x))_+` of the query `π` and returned pair `s`. -/
noncomputable def loss {n : ℕ} (γ : ℝ) (π : Ranking n) (s : ItemPair n) (x : Fin n → ℝ) : ℝ :=
  max (1 + γ * n * gap π s x) 0

/-- The weight `w_t` after the transcript `h` (chronological list of queries and returned
pairs), starting from `w_0 = 1` and applying the update (1),
`w_{t+1}(x) = w_t(x) e^{-ℓ_t(x)}`, once per round. -/
noncomputable def weightAfter {n : ℕ} (γ : ℝ) (h : Transcript n) : (Fin n → ℝ) → ℝ :=
  h.foldl (fun w e => fun x => w x * Real.exp (-loss γ e.1 e.2 x)) (fun _ => 1)

/-- The deterministic weighted learner of §4.1, with ties broken by item label: it queries
the sorted barycenter of the current weight. It uses only the transcript, not `k`. -/
noncomputable def mwLearner {n : ℕ} (γ : ℝ) : DetLearner n :=
  fun h => Tuple.sort (barycenter (weightAfter γ h))

end SortingCounterexamples.Optimal


