-- Prove2me | Definitions.Def_SemiStreamReach_Main_PositiveOracle
-- name    : SemiStreamReach_Main_PositiveOracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:51:28.206142+00:00
-- url     : https://prove2.me/theorems/dab43d02-e277-4258-8994-0320a1477342
-- title:
--   PositiveOracle (Algorithm 6, lines 8-11): $\theta=\lceil 3n_A/\varepsilon\rceil$, $A^+$ and the returned estimates
-- statement:
--   PositiveOracle$(A,s_A,\varepsilon)$ answers a request for $(1+\varepsilon)$-approximate distances from $s_A$ in a graph $A$ with $n_A$ vertices and nonnegative integer weights $w_A$. It sets $\theta=\lceil 3n_A/\varepsilon\rceil$, forms $A^+$, which is $A$ with weights $\theta w_A+1$, obtains $(1+\varepsilon/3)$-approximate distances $\hat d^+$ from $s_A$ in $A^+$ from an approximate algorithm, and returns
--   $$\hat d(v)=\begin{cases}0,&\hat d^+(v)<\theta,\\ \hat d^+(v)/\theta,&\text{otherwise.}\end{cases}$$
--
--   **Formalization Note.** `oracleTheta nA ε` is $\theta$, `plusWeights θ wA` the weights of $A^+$, `oracleAnswer θ d̂⁺` the returned vector, with values in `ℝ≥0∞` ($\infty/\theta=\infty$).
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 56 (PDF 58), Algorithm 6 lines 8-11

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances

open scoped ENNReal

namespace SemiStreamReach.Main

/-! # PositiveOracle (Algorithm 6, lines 8–11)

Hoppenworth, Li, Mahabadi, Tarnawski, arXiv:2611.05061 (PDF sha256 c1b64474…), Appendix A, p. 56
(PDF 58): "PositiveOracle answers an oracle call that asks for (1 + ε)-approximate distances from a
source s_A in a graph A with n_A vertices and nonnegative integer weights w_A.
procedure PositiveOracle(A, s_A, ε): θ ← ⌈3n_A/ε⌉, and A+ ← A with weights θw_A + 1;
d̂+ ← (1 + ε/3)-approximate distances from s_A in A+; return d̂(v) = 0 if d̂+(v) < θ, and
d̂(v) = d̂+(v)/θ otherwise."

**Formalization Note.** `A` has vertex set `Fin nA`, edge set `E` and natural weights `wA`
(`ofEdges`). The approximate algorithm is abstract: `d̂+` is any vector of estimates, in `ℝ≥0∞`
(`⊤ = ∞`). -/

/-- `θ = ⌈3 n_A / ε⌉`. -/
noncomputable def oracleTheta (nA : ℕ) (ε : ℝ) : ℕ := ⌈3 * (nA : ℝ) / ε⌉₊

/-- The weights `θ · w_A + 1` of `A+`. -/
def plusWeights {nA : ℕ} (θ : ℕ) (wA : Fin nA × Fin nA → ℕ) : Fin nA × Fin nA → ℕ :=
  fun e => θ * wA e + 1

/-- The answer of PositiveOracle: `d̂(v) = 0` if `d̂+(v) < θ`, and `d̂(v) = d̂+(v)/θ` otherwise. -/
noncomputable def oracleAnswer {nA : ℕ} (θ : ℕ) (dplus : Fin nA → ℝ≥0∞) : Fin nA → ℝ≥0∞ :=
  fun v => if dplus v < (θ : ℝ≥0∞) then 0 else dplus v / (θ : ℝ≥0∞)

end SemiStreamReach.Main


