-- Prove2me | Definitions.Def_ExitSpirals_WellBehaved
-- name    : ExitSpirals_WellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:22.91912+00:00
-- url     : https://prove2.me/theorems/943d72c3-2662-4df0-96ee-001092b64281
-- title:
--   Well-behaved degree-sequence tuples (Assumptions A.1, A.2) and independent labels
-- statement:
--   A **degree tuple** gives, for every population size $n$, an out-degree $d^+_{i,n}$ and an in-degree $d^-_{i,n}$ for each agent $i\in\{1,\dots,n\}$. Its empirical law is $p_{jk,n}=\#\{i: d^-_{i,n}=j,\ d^+_{i,n}=k\}/n$, its maximum degree is $\Delta_n=\max_i\max(d^-_{i,n},d^+_{i,n})$, and
--   $$\psi_n=\max\Big(\sum_{j,k}\frac{j^2k\,p_{jk,n}}{\lambda_n},\ \sum_{j,k}\frac{k^2j\,p_{jk,n}}{\lambda_n}\Big),\qquad \lambda_n=\sum_{j,k}j\,p_{jk,n}.$$
--   The tuple is **well-behaved** for a joint law $p$ if
--
--   1. $\sum_i d^+_{i,n}=\sum_i d^-_{i,n}$ for every $n$;
--   2. $p_{jk,n}\to p_{jk}$ for all $j,k$ (A.1(1));
--   3. $\sum_i (d^+_{i,n})^2+(d^-_{i,n})^2=O(n)$ (A.1(3));
--   4. if $\Delta_n\to\infty$ then $\psi_n=o(\Delta_n)$ (A.2(1));
--   5. $\Delta_n\le n^{1/12}/\log n$ for all large $n$ (A.2(2)).
--
--   Two tuples $d_R,d_C$ have **independent labels** for $p_R,p_C$ if for all $j,k,j',k'$
--   $$\frac1n\#\{i:\ d^-_{i,R}=j,\ d^+_{i,R}=k,\ d^-_{i,C}=j',\ d^+_{i,C}=k'\}\ \longrightarrow\ p_{jk,R}\,p_{j'k',C},$$
--   so that an agent's degrees in one market carry asymptotically no information about its degrees in the other.
--
--   These are the conditions (from Cooper and Frieze) under which uniform random digraphs with the given degrees are well approximated by branching processes.
--
--   **Formalization Note** $j$ is the in-degree in $p_{jk,n}$ (A.3 prints the opposite order). A.2(2) is required only eventually: at $n=1$ it is false for any nonzero degree. The paper calls the tuples random variables and its independence sentence is garbled; independence is encoded as convergence of the joint empirical law to the product, for deterministic tuples. $\psi_n$ is written as a ratio of sums over agents (the factors $1/n$ cancel).
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Appendix A.3, pp.47–48: empirical law p_jk,n (p.47), Assumption A.1, Assumption A.2, well-behaved tuples, independence of the two markets' degrees (p.48)

import Mathlib

namespace ExitSpirals

open Filter Asymptotics

/-- **An infinite tuple of degree sequences** `((d⁺_n, d⁻_n))_{n}` for one market.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Appendix A.3,
p.47: "For each n, let d⁺_n = (d⁺_{i,n})_{i=1}^n and d⁻_n = (d⁻_{i,n})_{i=1}^n be sequences of
non-negative integers representing the out-degrees and in-degrees, respectively".

**Formalization Note.** For each `n` the agents are `Fin n`; `dOut n i = d⁺_{i,n}` and
`dIn n i = d⁻_{i,n}`. -/
structure DegreeTuple where
  /-- Out-degrees `d⁺_{i,n}`. -/
  dOut : (n : ℕ) → Fin n → ℕ
  /-- In-degrees `d⁻_{i,n}`. -/
  dIn : (n : ℕ) → Fin n → ℕ

/-- Empirical joint degree distribution `p_{jk,n} = #{i : d⁻_{i,n} = j, d⁺_{i,n} = k} / n`
(p.47), with `j` the **in**-degree, as in the limit law (pp.16, 25). -/
noncomputable def empDist (d : DegreeTuple) (n j k : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin n => d.dIn n i = j ∧ d.dOut n i = k).card : ℝ) / n

/-- Maximum degree `Δ_n` (Assumption A.2, p.48), over in- and out-degrees. -/
def maxDeg (d : DegreeTuple) (n : ℕ) : ℕ :=
  Finset.univ.sup fun i : Fin n => max (d.dIn n i) (d.dOut n i)

/-- `ψ_n = max(Σ_{j,k} j²k p_{jk,n}/λ_n, Σ_{j,k} k²j p_{jk,n}/λ_n)` (Assumption A.2(1), p.48), with
`λ_n = Σ_{j,k} j p_{jk,n}` the empirical mean degree. Written over agents: the factor `1/n` of
`p_{jk,n}` cancels between numerator and `λ_n`. -/
noncomputable def psi (d : DegreeTuple) (n : ℕ) : ℝ :=
  max ((∑ i : Fin n, ((d.dIn n i : ℝ) ^ 2 * d.dOut n i)) / ∑ i : Fin n, (d.dIn n i : ℝ))
      ((∑ i : Fin n, ((d.dOut n i : ℝ) ^ 2 * d.dIn n i)) / ∑ i : Fin n, (d.dIn n i : ℝ))

/-- **Well-behaved tuple** (Assumptions A.1 and A.2, p.48), consistent with the joint law `p`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, p.48:
"For each n, d⁺_n and d⁻_n are sequences of non-negative integers such that Σ_i d⁺_{i,n} =
Σ_i d⁻_{i,n} and, for some joint distribution (p_{jk})_{j,k≥0}, over in- and out-degrees
1. p_{jk,n} → p_{jk} for every j, k ≥ 0 as n → ∞, 2. λ := … ∈ (0, ∞), 3. Σ_{i=1}^n (d⁺_{i,n})² +
(d⁻_{i,n})² = O(n)." Assumption A.2: "1. … If Δ_n → ∞ with n then ψ_n = o(Δ_n). 2. Δ_n ≤
n^{1/12} / log n. We call an infinite tuple that satisfies Assumptions A.1 and A.2 well-behaved."

The four fields are: equal total degrees for every `n`; A.1(1); A.1(3); A.2(1); A.2(2).
A.1(2) is a property of `p` alone and is part of `IsDegreeDist`.

**Formalization Note.** `j` is the in-degree in `p_{jk,n}` (pp.16, 25; A.3 prints the opposite
order, which is not followed). A.2(2) is required only for all sufficiently large `n`: at `n = 1`
`log n = 0`, and for any degree `≥ 1` the inequality fails until `n` is astronomically large, so a
literal "for all n" would make the class empty; Cooper–Frieze's conditions are asymptotic and §4.3.1
studies "n sufficiently large". -/
def WellBehaved (d : DegreeTuple) (p : ℕ → ℕ → ℝ) : Prop :=
  (∀ n, ∑ i : Fin n, d.dOut n i = ∑ i : Fin n, d.dIn n i) ∧
  (∀ j k, Tendsto (fun n => empDist d n j k) atTop (nhds (p j k))) ∧
  (fun n : ℕ => ∑ i : Fin n, ((d.dOut n i : ℝ) ^ 2 + (d.dIn n i : ℝ) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ)) ∧
  (Tendsto (fun n => maxDeg d n) atTop atTop →
      (fun n => psi d n) =o[atTop] (fun n => (maxDeg d n : ℝ))) ∧
  (∀ᶠ n : ℕ in atTop, (maxDeg d n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 12) / Real.log n)

/-- **Asymptotically independent labels** of the two markets' degree sequences.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Appendix A.3,
p.48: "our assumption that the two networks G_R and G_C are drawn independently (Assumption 3.1)
implies … In other words, the in (out) degree of an intermediary in the repo market gives no
information about its in- (out-) degree in the collateral market."

The joint empirical law of `(d⁻_{i,R}, d⁺_{i,R}, d⁻_{i,C}, d⁺_{i,C})` over agents `i` converges to
`p_R ⊗ p_C`.

**Formalization Note.** The page's sentence is garbled (no predicate) and calls the tuples random
variables; the statement is made for every deterministic pair of tuples whose joint empirical law
is asymptotically the product, which covers every typical realization of independent draws. -/
def IndependentLabels (dR dC : DegreeTuple) (pR pC : ℕ → ℕ → ℝ) : Prop :=
  ∀ j k j' k', Tendsto
    (fun n => ((Finset.univ.filter fun i : Fin n =>
        dR.dIn n i = j ∧ dR.dOut n i = k ∧ dC.dIn n i = j' ∧ dC.dOut n i = k').card : ℝ) / n)
    atTop (nhds (pR j k * pC j' k'))

end ExitSpirals


