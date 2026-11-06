-- Prove2me | Definitions.Def_NearLinIsing_HardCore
-- name    : NearLinIsing_HardCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:10.537542+00:00
-- url     : https://prove2.me/theorems/6f9656ab-a25f-4d63-bd3e-4d62be3b29c7
-- title:
--   Finite hard-core laws, pinning, covariance order, heat-bath dynamics, Dirichlet form and entropy
-- statement:
--   A finite hard-core model on $M$ coordinates is a conflict graph (the off-diagonal conflict matrix $A^\circ$, without self-conflicts) with activities $\lambda_i$. Its law on a coordinate set $S$ gives an independent subset $X\subseteq S$ probability proportional to $\prod_{i\in X}\lambda_i$, and $X_i=\mathbf 1\{i\in X\}$.
--
--   A **positive pinning** by an independent set $\tau$ leaves the hard-core law on the coordinates outside $\tau$ that conflict with no member of $\tau$. The module defines the occupied marginals $\mathbb E X_i$, the covariance $\mathrm{Cov}(X)$, and the positive-semidefinite statement $\mathrm{Cov}(X)\preceq\mathrm{Diag}(d)$ tested on vectors supported on a given set.
--
--   **Uniform-coordinate heat-bath dynamics** $P_{HB}$ picks a uniform coordinate $i$. If a neighbour of $i$ is occupied nothing changes; otherwise $i$ is occupied with probability $\lambda_i/(1+\lambda_i)$ and empty with probability $1/(1+\lambda_i)$. Finally
--
--   $$\mathcal E_P(f,f)=\tfrac12\sum_{x,y}\pi(x)P(x,y)(f(x)-f(y))^2,\qquad \mathrm{Ent}_\pi(h)=\mathbb E_\pi[h\log h]-\mathbb E_\pi[h]\log\mathbb E_\pi[h],$$
--
--   with $0\log0=0$. These are the finite objects of the log–Sobolev input and of the covariance bound.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §2.2, p. 8; §2.5, p. 9; Lemma 3.4, p. 11; Lemma 3.5, p. 14

import Mathlib

namespace NearLinIsing

noncomputable section

open Classical

/-!
Finite hard-core models on `M` coordinates (§2.2, p. 8; §2.5, p. 9; Lemmas 3.4 and 3.5).

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §2.2 (p. 8), §2.5 (p. 9), Lemma 3.4 (p. 11), Lemma 3.5 (p. 14).

A finite hard-core model is a conflict graph `Gc` on `Fin M` (the off-diagonal conflict matrix
`A°`, no self-conflicts) with activities `lam`. A configuration is a finite set `X` of occupied
coordinates; `X_i = 1{i ∈ X}`.
-/

variable {M : ℕ}

/-- `X` is independent (feasible) in the conflict graph `Gc`. -/
def IsIndep (Gc : SimpleGraph (Fin M)) (X : Finset (Fin M)) : Prop :=
  ∀ i ∈ X, ∀ j ∈ X, ¬ Gc.Adj i j

/-- The hard-core weight `1{X ⊆ S, X independent} ∏_{i ∈ X} λ_i` of the model restricted to the
coordinate set `S`. -/
def hcWeight (Gc : SimpleGraph (Fin M)) (lam : Fin M → ℝ) (S : Finset (Fin M))
    (X : Finset (Fin M)) : ℝ :=
  if X ⊆ S ∧ IsIndep Gc X then ∏ i ∈ X, lam i else 0

/-- The **hard-core law** on the coordinates `S` with activities `lam`, as point masses on
`Finset (Fin M)` (supported on independent subsets of `S`). -/
def hcLaw (Gc : SimpleGraph (Fin M)) (lam : Fin M → ℝ) (S : Finset (Fin M))
    (X : Finset (Fin M)) : ℝ :=
  hcWeight Gc lam S X / ∑ Y : Finset (Fin M), hcWeight Gc lam S Y

/-- The coordinates that stay feasible after the **positive pinning** of the independent set `τ`
(§2.5): not in `τ` and not in conflict with `τ`. The residual law is the hard-core law on this set. -/
def resSet (Gc : SimpleGraph (Fin M)) (τ : Finset (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter fun i => i ∉ τ ∧ ∀ j ∈ τ, ¬ Gc.Adj i j

/-- The occupied marginal `E X_i = P(i ∈ X)` under a law `π` on `Finset (Fin M)`. -/
def mean (π : Finset (Fin M) → ℝ) (i : Fin M) : ℝ :=
  ∑ X : Finset (Fin M), π X * (if i ∈ X then 1 else 0)

/-- The covariance `Cov(X_i, X_j)` under `π`. -/
def cov (π : Finset (Fin M) → ℝ) (i j : Fin M) : ℝ :=
  (∑ X : Finset (Fin M), π X * ((if i ∈ X then 1 else 0) * (if j ∈ X then 1 else 0)))
    - mean π i * mean π j

/-- `Cov(X) ⪯ Diag(d)` in the positive-semidefinite order, tested on vectors supported on `U`:
`xᵀ Cov(X) x ≤ ∑_i d_i x_i²` for every `x` vanishing outside `U`. -/
def CovLeDiag (π : Finset (Fin M) → ℝ) (d : Fin M → ℝ) (U : Finset (Fin M)) : Prop :=
  ∀ x : Fin M → ℝ, (∀ i, i ∉ U → x i = 0) →
    ∑ i, ∑ j, x i * cov π i j * x j ≤ ∑ i, d i * x i ^ 2

/-- One heat-bath update at coordinate `i`: if a neighbour of `i` is occupied, `X` stays; otherwise
`i` is resampled, occupied with probability `λ_i/(1+λ_i)` and empty with probability `1/(1+λ_i)`. -/
def hbAt (Gc : SimpleGraph (Fin M)) (lam : Fin M → ℝ) (i : Fin M) (X Y : Finset (Fin M)) : ℝ :=
  if ∃ j ∈ X, Gc.Adj i j then (if Y = X then 1 else 0)
  else (if Y = insert i X then lam i / (1 + lam i) else 0)
    + (if Y = X.erase i then 1 / (1 + lam i) else 0)

/-- The **uniform-coordinate heat-bath kernel** `P_HB(X, Y)`: choose `i` uniformly from the `M`
coordinates and apply `hbAt i` (Lemma 3.4). -/
def hbKernel (Gc : SimpleGraph (Fin M)) (lam : Fin M → ℝ) (X Y : Finset (Fin M)) : ℝ :=
  ∑ i, hbAt Gc lam i X Y / M

/-- The **Dirichlet form** `E_P(f,f) = ½ ∑_{x,y} π(x) P(x,y) (f(x) − f(y))²` (§2.2, p. 8) of the
heat-bath kernel, with `π` the hard-core law on all coordinates. -/
def hbDirichlet (Gc : SimpleGraph (Fin M)) (lam : Fin M → ℝ) (f : Finset (Fin M) → ℝ) : ℝ :=
  (1 / 2) * ∑ X : Finset (Fin M), ∑ Y : Finset (Fin M),
    hcLaw Gc lam Finset.univ X * hbKernel Gc lam X Y * (f X - f Y) ^ 2

/-- The **entropy** `Ent_π(h) = E_π[h log h] − E_π[h] log E_π[h]`, with `0 log 0 = 0` (§2.2,
p. 8).

**Formalization Note.** `Real.log 0 = 0`, so `0 · log 0 = 0` holds as written. -/
def ent (π : Finset (Fin M) → ℝ) (h : Finset (Fin M) → ℝ) : ℝ :=
  (∑ X : Finset (Fin M), π X * (h X * Real.log (h X)))
    - (∑ X : Finset (Fin M), π X * h X) * Real.log (∑ X : Finset (Fin M), π X * h X)

end

end NearLinIsing


