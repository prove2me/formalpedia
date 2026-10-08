-- Prove2me | Definitions.Def_GoldieRenewal_Kesten_Perpetuity
-- name    : GoldieRenewal_Kesten_Perpetuity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:13.685503+00:00
-- url     : https://prove2.me/theorems/c0556be5-7bce-4305-be2d-7ec01df3ee51
-- title:
--   Partial products Π_j, Π_{j,n}, partial sums R_n, R_{j,n} of Proposition 4.2, medians, and the paper's ‖X‖_p
-- statement:
--   Let $(Q_k,M_k)$, $k=1,2,\dots$, be a sequence of pairs of real random variables. Following Proposition 4.2 of the paper, define for $0\le j\le n$
--
--   $$
--   \Pi_j := \prod_{k=1}^{j} M_k,\qquad R_n := \sum_{k=1}^{n}\Pi_{k-1}Q_k,\qquad
--   \Pi_{j,n} := \prod_{k=j+1}^{n} M_k,\qquad R_{j,n} := \sum_{k=j+1}^{n}\Pi_{j,k-1}Q_k ,
--   $$
--
--   with empty products equal to $1$ and empty sums equal to $0$, so that $R_n = R_j + \Pi_jR_{j,n}$. The partial sums $R_n$ are the partial sums of the perpetuity $\sum_{k\ge1}\Pi_{k-1}Q_k$, which solves the random difference equation $R\overset{\mathcal L}{=}Q+MR$.
--
--   A real number $a$ is a **median** of a law $\nu$ on $\mathbb R$ if $\nu[a,\infty)\ge\tfrac12$ and $\nu(-\infty,a]\ge\tfrac12$; medians need not be unique.
--
--   For a random variable $X$ with law $\nu$ and $p>0$, the paper's (§1)
--
--   $$
--   \|X\|_p := \begin{cases}\mathbf E|X|^p, & 0<p\le 1,\\ (\mathbf E|X|^p)^{1/p}, & 1\le p<\infty,\end{cases}
--   $$
--
--   which satisfies the triangle inequality for every $p>0$.
--
--   **Formalization Note** The sequence is stored 0-based: the Lean functions `Q i`, `M i` for $i=0,1,\dots$ are the paper's $Q_{i+1}$, $M_{i+1}$, so $\Pi_j = \prod_{i<j} M_i$ in Lean indexing. $\|X\|_p$ is a function of the law of $X$ and uses the Bochner integral; every statement that uses it asserts or assumes the integrability of $|X|^p$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 127 (§1, ‖X‖_p); p. 136, Proposition 4.2 (Π_j, R_n, Π_{j,n}, R_{j,n}, med)

import Mathlib

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! The partial products and partial sums of Proposition 4.2 (Goldie 1991, p. 136).

The sequence `(Q_k, M_k)`, `k = 1, 2, …`, of the paper is stored 0-based: `Q i`, `M i` for
`i = 0, 1, …` stand for the paper's `Q_{i+1}`, `M_{i+1}`. Empty products are `1`, empty sums `0`. -/

/-- `Π_j := M₁ ⋯ M_j` (paper, p. 136; also `Π_n` of §4, p. 135). With 0-based storage this is
`∏_{i < j} M i`; `Π₀ = 1`. -/
def piProd {Ω : Type*} (M : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range j, M i ω

/-- `R_n := Σ_{k=1}^n Π_{k−1} Q_k` (paper, p. 136). With 0-based storage this is
`Σ_{i < n} Π_i Q i`; `R₀ = 0`. -/
def partialSum {Ω : Type*} (Q M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, piProd M i ω * Q i ω

/-- `Π_{j,n} := Π_{k=j+1}^n M_k` (paper, p. 136). With 0-based storage this is
`∏_{j ≤ i < n} M i`; it is `1` when `n ≤ j`. -/
def piProdFrom {Ω : Type*} (M : ℕ → Ω → ℝ) (j n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.Ico j n, M i ω

/-- `R_{j,n} := Σ_{k=j+1}^n Π_{j,k−1} Q_k` (paper, p. 136). With 0-based storage this is
`Σ_{j ≤ i < n} Π_{j,i} Q i`; it is `0` when `n ≤ j`. -/
def partialSumFrom {Ω : Type*} (Q M : ℕ → Ω → ℝ) (j n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Ico j n, piProdFrom M j i ω * Q i ω

/-- **Median** of a law (Goldie 1991, p. 136, "med denotes median"): `a` is a median of the law
`ν` on `ℝ` when `ν[a, ∞) ≥ 1/2` and `ν(−∞, a] ≥ 1/2`. Medians need not be unique. -/
def IsMedian (ν : Measure ℝ) (a : ℝ) : Prop :=
  (2 : ℝ≥0∞)⁻¹ ≤ ν (Set.Ici a) ∧ (2 : ℝ≥0∞)⁻¹ ≤ ν (Set.Iic a)

/-- **The paper's `‖X‖_p`** (Goldie 1991, §1, p. 127) for `X` with law `ν`:
`‖X‖_p := E|X|^p` if `0 < p ≤ 1`, and `(E|X|^p)^{1/p}` if `1 ≤ p < ∞` (the two agree at `p = 1`).

**Formalization Note** `E|X|^p` is the Bochner integral `∫ |x|^p dν`; every statement using this
quantity also asserts or assumes that `|x|^p` is `ν`-integrable, so the value is never a junk `0`. -/
noncomputable def goldieNorm (p : ℝ) (ν : Measure ℝ) : ℝ :=
  if p ≤ 1 then ∫ x, |x| ^ p ∂ν else (∫ x, |x| ^ p ∂ν) ^ (1 / p)

end GoldieRenewal.Kesten


