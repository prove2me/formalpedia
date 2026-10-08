-- Prove2me | Definitions.Def_MonteCarloBound_LowerBound_Setting
-- name    : MonteCarloBound_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:35.179286+00:00
-- url     : https://prove2.me/theorems/e36c79c6-c630-43a3-91e5-a2a10cdeb848
-- title:
--   Proof of Theorem 2, p. 50 — leave-one-out reindexing of the sample, and the law of the sample path
-- statement:
--   This file fixes the three auxiliary objects of Mak, Morton and Wood's proof that the expected sample-average optimal value increases with the sample size. The stochastic program, its sample-average approximation and the i.i.d. sample are those of the imported module `SolutionQuality.SRP.Setting`: for a decision $x\in X\subseteq\mathbb R^d$ and a sample path $s=(s_0,s_1,\dots)$ of realizations of $\tilde\xi$,
--   $$
--   \bar f_n(x)=\frac1n\sum_{i=1}^n f(x,\tilde\xi^i),\qquad z_n^*=\inf_{x\in X}\bar f_n(x),
--   $$
--   where the paper's $\tilde\xi^i$ is the term $s_{i-1}$ of the path.
--
--   1. **Leave-one-out reindexing.** For indices $i,j\in\mathbb N$,
--   $$
--   \mathrm{skip}_i(j)=\begin{cases} j, & j<i,\\ j+1, & j\ge i.\end{cases}
--   $$
--   For $i\le n$ the values $\mathrm{skip}_i(0),\dots,\mathrm{skip}_i(n-1)$ list $\{0,\dots,n\}\setminus\{i\}$ in increasing order. In the paper's one-based notation they are the indices $j=1,\dots,n+1$, $j\ne i$.
--
--   2. **Leave-one-out optimal value.** For a sample path $s$, a sample size $n$ and an index $i$,
--   $$
--   z_{n,(i)}^*(s)=\inf_{x\in X}\ \frac1n\sum_{\substack{j=1\\ j\ne i}}^{n+1} f(x,\tilde\xi^j),
--   $$
--   that is, the sample-average optimal value $z_n^*$ computed on the path $j\mapsto s_{\mathrm{skip}_i(j)}$ from which the $i$-th draw has been deleted. These are the $n+1$ problems that appear in the proof of Theorem 2.
--
--   3. **Law of the sample path.** For random elements $\xi_0,\xi_1,\dots:\Omega\to\Xi$ on a probability space $(\Omega,P)$, the law of $\omega\mapsto(\xi_0(\omega),\xi_1(\omega),\dots)$ on the path space $\Xi^{\mathbb N}$ with its product $\sigma$-algebra. Statements of the form "with probability one, every $\mathrm{SP}_m$ has an optimal solution" are made almost surely with respect to this law.
--
--   **Formalization Note.** Indices are 0-based throughout: the paper's $\tilde\xi^i$ is `ξ (i-1)`, and the paper's leave-one-out index $i\in\{1,\dots,n+1\}$ is the Lean `i - 1 ∈ {0, …, n}`. The infimum is the conditionally complete `sInf` of the imported `saaValue`; it equals the paper's minimum whenever the minimum is attained.
-- source:
--   Mak, Morton & Wood, Oper. Res. Lett. 24 (1999), pp. 47–50, SP, SP_n, proof of Theorem 2

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace MonteCarloBound.LowerBound

open MeasureTheory ProbabilityTheory SolutionQuality.SRP

variable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- Leave-one-out reindexing (proof of Theorem 2, p. 50). For `i ≤ n` the values
`skipIndex i 0, …, skipIndex i (n - 1)` enumerate `{0, …, n} \ {i}` in increasing order: the
paper's indices `j = 1, …, n + 1`, `j ≠ i`, shifted to start at `0`. -/
def skipIndex (i j : ℕ) : ℕ := if j < i then j else j + 1

/-- The leave-one-out optimal value
`min_{x ∈ X} (1/n) Σ_{j = 1, j ≠ i}^{n+1} f(x, ξ̃ʲ)` of the proof of Theorem 2 (p. 50), on the
sample path `s`: the SAA optimal value `z*_n` computed on the path with its `i`-th term
(0-based) removed. -/
noncomputable def looValue (f : E d → Ξ → ℝ) (X : Set (E d)) (s : ℕ → Ξ) (n i : ℕ) : ℝ :=
  saaValue f X (fun j => s (skipIndex i j)) n

/-- The law of the sample path `ω ↦ (ξ̃¹(ω), ξ̃²(ω), …)` on `ℕ → Ξ` (the Lean `ξ 0, ξ 1, …`). -/
noncomputable def pathLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℕ → Ω → Ξ) :
    Measure (ℕ → Ξ) :=
  P.map (fun ω i => ξ i ω)

end MonteCarloBound.LowerBound


