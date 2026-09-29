-- Prove2me | Definitions.Def_DistInterpRO_Equivalence_Model
-- name    : DistInterpRO_Equivalence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:43:49.980098+00:00
-- url     : https://prove2.me/theorems/b3cf0909-5f35-446d-bb51-8409d8fb28bc
-- title:
--   The distribution set $\mathcal P_n$, the extended expectation, dual feasibility and the nested dual solution of Theorem 2.1
-- statement:
--   Throughout, $\mathbb R^m$ carries its Borel $\sigma$-algebra, and $[1:n]=\{1,\dots,n\}$. This file defines the four objects in terms of which Theorem 2.1 of Xu, Caramanis and Mannor (2012) and its proof are stated.
--
--   1. **The distribution set $\mathcal P_n$.** Given weights $c_1,\dots,c_n\in\mathbb R$ and sets $\mathcal Z_1,\dots,\mathcal Z_n\subseteq\mathbb R^m$,
--   $$\mathcal P_n=\Big\{\mu \text{ a Borel probability measure on } \mathbb R^m \ \Big|\ \forall S\subseteq[1:n]:\ \mu\Big(\bigcup_{i\in S}\mathcal Z_i\Big)\ge\sum_{i\in S}c_i\Big\}.$$
--   The constraint is imposed for every subset $S$, including $S=\emptyset$ and $S=[1:n]$.
--   2. **The extended expectation.** For a Borel probability measure $\mu$ (or any measure) and a real function $f$,
--   $$\mathbb E_\mu[f]=\int f^+\,d\mu-\int f^-\,d\mu\ \in[-\infty,+\infty],$$
--   where $f^+=\max(f,0)$, $f^-=\max(-f,0)$ and both integrals are Lebesgue integrals of nonnegative functions with values in $[0,+\infty]$. When both are $+\infty$ the difference is taken to be $-\infty$ (the extended-real convention $\infty-\infty=-\infty$).
--   3. **Dual feasibility.** Write $\mathcal Z_S=\bigcup_{i\in S}\mathcal Z_i$ and $N=[1:n]$. A vector $\alpha=(\alpha_S)_{S\subseteq N}\in\mathbb R^{2^n}$ is *dual feasible* for $f$ if
--   $$\sum_{S\subseteq N}\alpha_S\,\mathbf 1(x\in\mathcal Z_S)\le f(x)\quad\forall x\in\mathcal Z_N,\qquad \alpha_S\ge0\quad\forall S\ne N.$$
--   The coordinate $\alpha_N$ is unrestricted in sign.
--   4. **The nested dual solution.** Given numbers $f_1,\dots,f_n$, the vector $\alpha$ with $\alpha_S=0$ for all $S$ except the $n$ nested sets $\{1,\dots,i\}$, where
--   $$\alpha_{\{1,\dots,i\}}=f_i-f_{i+1}\ (1\le i<n),\qquad \alpha_N=f_n.$$
--
--   Item 1 is the distributional set of Theorem 2.1; item 2 is the meaning of $\int f\,d\mu$ in Eq. (4); items 3 and 4 are the semi-infinite dual linear program and the explicit dual solution used in the proof of Theorem 2.1.
--
--   **Formalization Note** $\mathbb R^m$ is `Fin m → ℝ` (no norm is used). Distributions are `Measure (Fin m → ℝ)` with `IsProbabilityMeasure` built into membership of $\mathcal P_n$. Indices $1,\dots,n$ become `Fin n` $=\{0,\dots,n-1\}$ and subsets are `Finset (Fin n)`; the set $\{1,\dots,i\}$ is `Finset.Iic i`. The bound $\sum_{i\in S}c_i$ is compared with the measure as `ENNReal.ofReal (∑ i ∈ S, c i)`. The expectation is computed in `EReal` from two lower Lebesgue integrals, never with the Bochner integral, so an infinite expectation is represented as $\pm\infty$ rather than as $0$. In the nested dual solution the last index has no successor, and its coefficient is $f_n$ itself.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 96, Theorem 2.1 (the set 𝒫ₙ); p. 97, proof of Theorem 2.1 (the dual problem and the nested dual solution)

import Mathlib

open MeasureTheory

namespace DistInterpRO.Equivalence

/-- The distribution set `𝒫ₙ` of Theorem 2.1 (Xu–Caramanis–Mannor 2012, p. 96):
the Borel probability measures `μ` on `ℝᵐ` such that, for **every** index set
`S ⊆ [1 : n]` (`S = ∅` and `S = [1 : n]` included), `μ(⋃_{i ∈ S} 𝒵ᵢ) ≥ ∑_{i ∈ S} cᵢ`.
Indices are `Fin n = {0, …, n-1}`. -/
def distSet {m n : ℕ} (c : Fin n → ℝ) (Z : Fin n → Set (Fin m → ℝ)) :
    Set (Measure (Fin m → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧
    ∀ S : Finset (Fin n), ENNReal.ofReal (∑ i ∈ S, c i) ≤ μ (⋃ i ∈ S, Z i)}

/-- The extended-real expectation `∫ f dμ = ∫ f⁺ dμ − ∫ f⁻ dμ ∈ [−∞, +∞]`, computed with
lower Lebesgue integrals of the positive and negative parts (no Bochner integral).
By the `EReal` convention `⊤ - ⊤ = ⊥`, it is `⊥` when both parts are infinite. -/
noncomputable def expect {m : ℕ} (μ : Measure (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal)

open Classical in
/-- Dual feasibility for the semi-infinite dual LP in the proof of Theorem 2.1 (p. 97):
`α ∈ ℝ^{2ⁿ}` (indexed by subsets `S ⊆ N = [1 : n]`) is dual feasible if
`∑_S α_S 𝟏(x ∈ 𝒵_S) ≤ f(x)` for all `x ∈ 𝒵_N` and `α_S ≥ 0` for all `S ≠ N`,
where `𝒵_S = ⋃_{i ∈ S} 𝒵ᵢ`. The coordinate `α_N` is unsigned. -/
def IsDualFeasible {m n : ℕ} (Z : Fin n → Set (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ)
    (α : Finset (Fin n) → ℝ) : Prop :=
  (∀ x ∈ ⋃ i, Z i,
      ∑ S : Finset (Fin n), α S * (if x ∈ ⋃ i ∈ S, Z i then (1 : ℝ) else 0) ≤ f x) ∧
    ∀ S : Finset (Fin n), S ≠ Finset.univ → 0 ≤ α S

/-- The nested dual solution of the proof of Theorem 2.1 (p. 97), built from the values
`fᵢ` (`fi i`): `α_S = 0` except on the `n` nested sets `{1, …, i}` (here `Finset.Iic i`,
0-based), where `α_{{1,…,i}} = fᵢ − fᵢ₊₁` for `i < n` and `α_N = fₙ`
(0-based: the last index `n-1` has no successor, and its term is `f_{n-1} − 0`). -/
noncomputable def nestedDual {n : ℕ} (fi : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i : Fin n,
    if S = Finset.Iic i then
      fi i - (if h : i.val + 1 < n then fi ⟨i.val + 1, h⟩ else 0)
    else 0

end DistInterpRO.Equivalence


