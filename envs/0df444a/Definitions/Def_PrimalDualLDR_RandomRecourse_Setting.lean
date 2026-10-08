-- Prove2me | Definitions.Def_PrimalDualLDR_RandomRecourse_Setting
-- name    : PrimalDualLDR_RandomRecourse_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:10.425766+00:00
-- url     : https://prove2.me/theorems/b50af3c1-3cdc-4446-8df9-726e0ec0ab76
-- title:
--   One-stage stochastic program with random recourse and quadratically constrained support (3.11): data, standing assumptions, M, strict feasibility (pp. 3–4, 9–10)
-- statement:
--   This module fixes the data and the standing assumptions of §3 of Kuhn, Wiesemann and Georghiou.
--
--   **Data.** Dimensions $k\ge1$, $n$, $m$, $l$; a probability measure $\mathbb P$ on $(\mathbb R^k,\mathfrak B(\mathbb R^k))$; matrices $C\in\mathbb R^{n\times k}$ and $B\in\mathbb R^{m\times k}$ giving the cost $c(\xi)=C\xi$ and the right-hand side $b(\xi)=B\xi$ (the $\mu$th row of $B$ is $b_\mu^\top$); matrices $A_1,\dots,A_m\in\mathbb R^{k\times n}$ giving the random recourse matrix $A(\xi)$, whose $\mu$th row is $\xi^\top A_\mu$; and matrices $W_1,\dots,W_l\in\mathbb R^{k\times k}$. Write $e_1$ for the first standard basis vector of $\mathbb R^k$.
--
--   **Support (3.11).**
--   $$
--   \Xi=\big\{\xi\in\mathbb R^k:\ e_1^\top\xi=1,\ \ \xi^\top W_\ell\,\xi\ge0,\ \ \ell=1,\dots,l\big\}.
--   $$
--
--   **Standing assumptions (§3, p. 10).**
--   1. $\mathbb P$ is a probability measure;
--   2. every $W_\ell$ is symmetric ($W_\ell\in\mathbb S$, the symmetric $k\times k$ matrices);
--   3. $\Xi$ is the support of $\mathbb P$;
--   4. $\Xi$ is nonempty and bounded;
--   5. the linear hull of $\Xi$ is $\mathbb R^k$.
--
--   **Second-order moment matrix (p. 4).** $M:=\mathbb E(\xi\xi^\top)$, i.e. $M_{ij}=\int\xi_i\xi_j\,d\mathbb P$.
--
--   **Strict feasibility of $\mathcal{SP}$.** The stochastic program $\mathcal{SP}$ minimizes $\mathbb E(c(\xi)^\top x(\xi))$ over $x\in\mathcal L^2_{k,n}$ subject to $A(\xi)x(\xi)\le b(\xi)$ $\mathbb P$-a.s. It is *strictly feasible* if there are $\varepsilon>0$, $\bar x\in\mathcal L^2_{k,n}$ and $\bar s\in\mathcal L^2_{k,m}$ with
--   $$
--   A(\xi)\bar x(\xi)+\bar s(\xi)=b(\xi)\quad\text{and}\quad \bar s(\xi)\ge\varepsilon e\qquad\mathbb P\text{-a.s.},
--   $$
--   where $e$ is the all-ones vector of $\mathbb R^m$; the $\mu$th row of $A(\xi)\bar x(\xi)$ is $\xi^\top A_\mu\bar x(\xi)$.
--
--   These are the objects on which the primal linear decision rule approximation $\mathcal{SP}^u$ and its semidefinite reformulation (3.14) are built.
--
--   **Formalization Note** Indices are 0-based: the paper's $\mu=1,\dots,m$, $\ell=1,\dots,l$ and the coordinate $\xi_1$ are `Fin m`, `Fin l` and index `0`; the field `hk : 0 < k` makes $e_1$ available. The standing assumptions are the predicate `Standing`, assumed by every theorem of the mission. Strict feasibility is the paper's condition (2.9) of §2 (p. 9) with $A\bar x(\xi)$ replaced by $A(\xi)\bar x(\xi)$: Theorem 2 uses the phrase "$\mathcal{SP}$ is strictly feasible" in §3 without restating it, and this transfer is ours. Under the standing assumptions $\xi$ is bounded $\mathbb P$-a.s., so the integrals defining $M$ are finite.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, pp. 3–4 (SP, M), p. 9 (2.9), p. 10 (§3, (3.11))

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic

namespace PrimalDualLDR.RandomRecourse

open MeasureTheory Matrix

/-- **Kuhn, Wiesemann, Georghiou (preprint 2009), §2 p. 3 and §3 p. 10.** The data of the
one-stage stochastic program `𝒮𝒫` with random recourse and quadratically constrained support.

* `k, n, m, l` are the dimensions of the outcome `ξ ∈ ℝ^k`, of the decision `x ∈ ℝ^n`, the number
  of constraints and the number of quadratic constraints describing the support; `hk : 0 < k`
  makes the first coordinate `ξ₁` (index `0`) available.
* `P` is the probability measure on `(ℝ^k, 𝔅(ℝ^k))`.
* `C ∈ ℝ^{n×k}`: cost coefficients `c(ξ) = Cξ`.
* `B ∈ ℝ^{m×k}`: right-hand side `b(ξ) = Bξ`; its row `B μ` is the paper's `b_μᵀ`.
* `A μ ∈ ℝ^{k×n}`: the `μ`th row of the recourse matrix `A(ξ)` is `ξᵀ A_μ`.
* `W ℓ ∈ ℝ^{k×k}`: the matrices `W_ℓ` of the support (3.11).

Indices are 0-based: the paper's `μ = 1, …, m`, `ℓ = 1, …, l` and coordinate `ξ_1` are
`Fin m`, `Fin l` and index `0`. -/
structure Setting where
  k : ℕ
  n : ℕ
  m : ℕ
  l : ℕ
  hk : 0 < k
  P : Measure (Fin k → ℝ)
  C : Matrix (Fin n) (Fin k) ℝ
  B : Matrix (Fin m) (Fin k) ℝ
  A : Fin m → Matrix (Fin k) (Fin n) ℝ
  W : Fin l → Matrix (Fin k) (Fin k) ℝ

namespace Setting

variable (σ : Setting)

/-- The basis vector `e_1 ∈ ℝ^k` (first coordinate `1`, all others `0`). -/
def e1 : Fin σ.k → ℝ := Pi.single ⟨0, σ.hk⟩ 1

/-- **(3.11), p. 10.** `Ξ = {ξ ∈ ℝ^k : e_1ᵀξ = 1, ξᵀW_ℓξ ≥ 0, ℓ = 1, …, l}`. -/
def Xi : Set (Fin σ.k → ℝ) :=
  {ξ | σ.e1 ⬝ᵥ ξ = 1 ∧ ∀ ℓ : Fin σ.l, 0 ≤ ξ ⬝ᵥ (σ.W ℓ *ᵥ ξ)}

/-- **Standing assumptions of §3 (p. 10, with Notation p. 3).** `P` is a probability measure;
every `W_ℓ` is symmetric (`W_ℓ ∈ 𝕊`); the set `Ξ` of (3.11) is the support of `P`; `Ξ` is nonempty
and bounded; and the linear hull of `Ξ` is `ℝ^k`. -/
def Standing : Prop :=
  IsProbabilityMeasure σ.P ∧ (∀ ℓ, (σ.W ℓ).IsSymm) ∧ PrimalDualLDR.FixedRecourse.IsSupport σ.P σ.Xi ∧
    σ.Xi.Nonempty ∧ Bornology.IsBounded σ.Xi ∧ Submodule.span ℝ σ.Xi = ⊤

/-- **p. 4.** The second-order moment matrix `M := E(ξξᵀ)`, entrywise `M_{ij} = ∫ ξ_i ξ_j dP`. -/
noncomputable def M : Matrix (Fin σ.k) (Fin σ.k) ℝ :=
  Matrix.of fun i j => ∫ ξ, ξ i * ξ j ∂σ.P

/-- The `μ`th entry of `A(ξ) x`: the row `ξᵀA_μ` applied to `x`, i.e. `ξᵀ A_μ x`. -/
def Arow (μ : Fin σ.m) (ξ : Fin σ.k → ℝ) (x : Fin σ.n → ℝ) : ℝ :=
  ξ ⬝ᵥ (σ.A μ *ᵥ x)

/-- **Strict feasibility of `𝒮𝒫`, (2.9) p. 9 transferred to random recourse.** There are a
tolerance `ε > 0` and decision rules `x̄ ∈ 𝓛²_{k,n}`, `s̄ ∈ 𝓛²_{k,m}` with
`A(ξ) x̄(ξ) + s̄(ξ) = b(ξ)` and `s̄(ξ) ≥ ε e`, `P`-almost surely. -/
def StrictlyFeasible : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ xbar : (Fin σ.k → ℝ) → (Fin σ.n → ℝ), ∃ sbar : (Fin σ.k → ℝ) → (Fin σ.m → ℝ),
    PrimalDualLDR.FixedRecourse.IsL2Rule σ.P xbar ∧ PrimalDualLDR.FixedRecourse.IsL2Rule σ.P sbar ∧
    ∀ᵐ ξ ∂σ.P, ∀ μ : Fin σ.m, σ.Arow μ ξ (xbar ξ) + sbar ξ μ = σ.B μ ⬝ᵥ ξ ∧ ε ≤ sbar ξ μ

end Setting

end PrimalDualLDR.RandomRecourse


