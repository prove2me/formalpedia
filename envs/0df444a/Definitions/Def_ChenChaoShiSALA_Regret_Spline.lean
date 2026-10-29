-- Prove2me | Definitions.Def_ChenChaoShiSALA_Regret_Spline
-- name    : ChenChaoShiSALA_Regret_Spline
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:16:43.704263+00:00
-- url     : https://prove2.me/theorems/3b9320ad-e3e7-4d34-ae7a-97cad96ab5fb
-- title:
--   Algorithm 0 — divided differences and explicit spline construction
-- statement:
--   For a list of $n$ distinct real nodes $x_0,\ldots,x_{n-1}$, the divided difference of $g$ is $\sum_j g(x_j)/\prod_{i\ne j}(x_j-x_i)$. A spline specification contains real endpoints $p^l,p^h$ and integers $m,l$. On the intended domain $p^l<p^h$, $m\ge2$, $l\ge1$, set $\delta=(p^h-p^l)/(l+1)$, $w_i=p^l+\delta(i-m)$ and $\tau_{ij}=w_i+(w_{i+m}-w_i)(j-1)/(m-1)$. Knots and nodes use one-based indices. Define $\phi_i(x)=\prod_{r=1}^{m-1}(x-w_{i+r})$ and $\psi_{ij}(x)=\prod_{r=1}^{j-1}(x-\tau_{ir})$. The coefficients $\alpha_{ij}$ are exactly the derivative sum (5), including its signs and factorial. The basis is $N_i^m(p)=(-1)^m(w_{i+m}-w_i)D[w_i,\ldots,w_{i+m}](w\mapsto\max(0,p-w)^{m-1})$. Define $\gamma_i^g=\sum_{j=1}^m\alpha_{ij}D[\tau_{i1},\ldots,\tau_{ij}]g$ and $Lg=\sum_{i=1}^{m+l}\gamma_i^gN_i^m$. These are total formulas; hypotheses at use sites exclude repeated nodes and zero denominators. No approximation accuracy is assumed.
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, pp. 10–11, Algorithm 0, (4)–(6)

import Mathlib

open scoped BigOperators
noncomputable section

namespace ChenChaoShiSALA.Regret

/-- Divided differences on an indexed list of distinct real nodes. -/
def dividedDifference (n : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, g (x j) /
    ∏ i ∈ (Finset.range n).erase j, (x j - x i)

/-- Algorithm 0 parameters; mathematical validity requires low < high, m ≥ 2, l ≥ 1. -/
structure Spline where
  low : ℝ
  high : ℝ
  m : ℕ
  l : ℕ

def Spline.delta (s : Spline) : ℝ := (s.high - s.low) / (s.l + 1 : ℕ)

/-- Knots and sampling nodes retain the source's one-based indices. -/
def Spline.knot (s : Spline) (i : ℕ) : ℝ :=
  s.low + s.delta * ((i : ℝ) - s.m)

def Spline.node (s : Spline) (i j : ℕ) : ℝ :=
  s.knot i + (s.knot (i + s.m) - s.knot i) * ((j : ℝ) - 1) / ((s.m : ℝ) - 1)

def Spline.phi (s : Spline) (i : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.range (s.m - 1), (x - s.knot (i + r + 1))

def Spline.psi (s : Spline) (i j : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.range (j - 1), (x - s.node i (r + 1))

def Spline.alpha (s : Spline) (i j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range j, (-1 : ℝ) ^ r *
    iteratedDeriv (s.m - (r + 1)) (s.phi i) 0 *
    iteratedDeriv r (s.psi i j) 0 / (Nat.factorial (s.m - 1) : ℝ)

def Spline.basis (s : Spline) (i : ℕ) (p : ℝ) : ℝ :=
  (-1 : ℝ) ^ s.m * (s.knot (i + s.m) - s.knot i) *
    dividedDifference (s.m + 1) (fun r => s.knot (i + r))
      (fun w => (max 0 (p - w)) ^ (s.m - 1))

def Spline.coefficient (s : Spline) (g : ℝ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s.m, s.alpha i (j + 1) *
    dividedDifference (j + 1) (fun r => s.node i (r + 1)) g

def Spline.approximation (s : Spline) (g : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (s.m + s.l), s.coefficient g (i + 1) * s.basis (i + 1) p

end ChenChaoShiSALA.Regret


