-- Prove2me | Definitions.Def_PagingDelay_PMD_Path
-- name    : PagingDelay_PMD_Path
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:36.479869+00:00
-- url     : https://prove2.me/theorems/3bc593b5-9ec4-402a-948f-ecb024a0a776
-- title:
--   PMD closed path, potential, bands and rounding map
-- statement:
--   Set $\delta=1/(2k+1)$ and $L=\log(2k+1)$. For antimass $x$ of total mass $n-k$ and a page $p$, define
--
--   $$\lambda(s)_i=\min\{1,x_i e^{s/w_i}\}\quad(i\ne p),\qquad
--   \lambda(s)_p=n-k-\sum_{i\ne p}\lambda(s)_i.$$
--
--   The path length is the first nonnegative parameter where $\lambda(s)_p=\delta$, and the level-$W$ band length is $\max\{0,\min\{2WL,|\lambda|\}-WL\}$. On the valid domain this hitting set is nonempty and bounded below, and continuity makes its infimum a minimum. If the hitting set is empty, the definition returns zero; this branch is unused on the valid domain. Weighted eviction is the integral of the positive coordinate derivatives multiplied by weights. The finitely many kinks do not affect this integral.
--
--   The potential is $D(O\Vert x)=\sum_{i\notin O}w_i(x_i-1-\log x_i)+\sum_{i\in O}w_ix_i$. A miss service contributes the sum of band lengths over dyadic $W$ with $w_p\le W<w_{\min}(O)$. Relevant levels end at the largest page weight. The scalar rounding map is $z(u)=\max\{0,2(1-u)/(1-\delta)-1\}$.
--
--   These are explicit formulas, with no bounds, optimality or service guarantees assumed. Empty-cache minimum weight is assigned zero only outside the domain used by the statements.
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), §3, pp. 7–10, (4); (8), p. 11; §5, p. 16; Definition 16, p. 17; Lemma 34, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Model

noncomputable section

namespace PagingDelay.PMD
open scoped BigOperators Classical

def delta (k : ℕ) : ℝ := 1 / (2 * (k : ℝ) + 1)
def logFactor (k : ℕ) : ℝ := Real.log (2 * (k : ℝ) + 1)
def level (j : ℕ) : ℝ := 2 ^ j

def DyadicWeights {n : ℕ} (w : Fin n → ℝ) : Prop := ∀ i, ∃ m : ℕ, w i = 2 ^ m

def PMDWeights {n : ℕ} (w : Fin n → ℝ) : Prop :=
  DyadicWeights w ∧ ∃ i, w i = 1

def StateValid {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ i, delta k ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = (n : ℝ) - k

/-- The explicit closed path of §3, p.8. The formula extends to all real parameters;
only nonnegative parameters through the first hit are used. -/
def path {n : ℕ} (k : ℕ) (w x : Fin n → ℝ) (p : Fin n) (s : ℝ) (i : Fin n) : ℝ :=
  if i = p then (n : ℝ) - k - ∑ q ∈ Finset.univ.erase p, min 1 (x q * Real.exp (s / w q))
  else min 1 (x i * Real.exp (s / w i))

/-- A guarded infimum. The invalid-input fallback is zero; on StateValid, k≥1,
positive weights, the set is nonempty, bounded below, and its infimum is a minimum. -/
def pathLength {n : ℕ} (k : ℕ) (w x : Fin n → ℝ) (p : Fin n) : ℝ :=
  if ∃ s : ℝ, 0 ≤ s ∧ path k w x p s p = delta k then
    sInf {s : ℝ | 0 ≤ s ∧ path k w x p s p = delta k}
  else 0

def pathEnd {n : ℕ} (k : ℕ) (w x : Fin n → ℝ) (p : Fin n) :=
  path k w x p (pathLength k w x p)

def bandLength (k : ℕ) (len W : ℝ) : ℝ :=
  max 0 (min (2 * W * logFactor k) len - W * logFactor k)

def pathFetch {n : ℕ} (k : ℕ) (w x : Fin n → ℝ) (p : Fin n) : ℝ :=
  w p * (x p - delta k)

/-- Derivatives at the finitely many kinks are zero in Lean; this does not change EV. -/
def weightedEviction {n : ℕ} (k : ℕ) (w x : Fin n → ℝ) (p : Fin n) : ℝ :=
  ∫ s in (0 : ℝ)..pathLength k w x p, ∑ i, w i * max 0 (deriv (fun t => path k w x p t i) s)

def potential {n : ℕ} (w : Fin n → ℝ) (O : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ O, w i * (x i - 1 - Real.log (x i))) + ∑ i ∈ O, w i * x i

/-- Empty-cache fallback zero is unused: every comparator cache has card k≥1. -/
def minWeight {n : ℕ} (w : Fin n → ℝ) (O : Finset (Fin n)) : ℝ :=
  ((O.toList.map w).foldr (fun a z => some (match z with
    | none => a | some b => min a b)) none).getD 0

/-- Finite set of relevant levels, including max weight for an exact power-of-two input. -/
def levels {n : ℕ} (w : Fin n → ℝ) : List ℕ :=
  List.range (1 + Finset.univ.sup (fun i => ⌊Real.log (max 1 (w i)) / Real.log 2⌋₊))

def serviceExcess {n : ℕ} (k : ℕ) (w x : Fin n → ℝ) (p : Fin n)
    (O : Finset (Fin n)) : ℝ :=
  (((levels w).filter (fun j => w p ≤ level j ∧ level j < minWeight w O)).map
    (fun j => bandLength k (pathLength k w x p) (level j))).sum

/-- Lemma 34's scalar map, on the source interval [δ,1]. -/
def roundingMap (k : ℕ) (u : ℝ) : ℝ := max 0 (2 * ((1 - u) / (1 - delta k)) - 1)

end PagingDelay.PMD


