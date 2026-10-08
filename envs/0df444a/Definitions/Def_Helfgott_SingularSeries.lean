-- Prove2me | Definitions.Def_Helfgott_SingularSeries
-- name    : Helfgott_SingularSeries
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-05T01:26:49.029308+00:00
-- url     : https://prove2.me/theorems/b05142a8-3aaf-4662-ad5d-8add1471ee44
-- title:
--   Euler factors and constant for the actual ternary Goldbach singular series
-- statement:
--   For a nonnegative integer $N$, let
--
--   $$F_p(N)=\begin{cases}
--   1-(p-1)^{-2},&p\text{ prime and }p\mid N,\\
--   1+(p-1)^{-3},&p\text{ prime and }p\nmid N,\\
--   1,&p\text{ not prime}.
--   \end{cases}$$
--
--   The ternary singular-series Euler constant is
--
--   $$C_0(N)=\prod_{p\text{ prime}}F_p(N).$$
--
--   For odd $N$, the local factor at $p=2$ is $2$. These are the arithmetic factors appearing in the main term of Helfgott's ternary Goldbach circle method. The definitions assert no convergence, equality with a Ramanujan series, or numerical lower bound; those are separate proof obligations.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §7.2, equation (7.9), and the main term in §3. The local formula agrees with the existing Vino.threePrimeFactor for natural arguments; this definition adds the actual real Euler product used in the coordinated Helfgott analysis. Written by Codex.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs

open scoped BigOperators

namespace Helfgott

/-- Prime local factors of the ternary Goldbach singular series, extended by one
at nonprimes. The sign is determined by whether the prime divides N. -/
noncomputable def singularEulerFactor (N p : ℕ) : ℝ :=
  if Nat.Prime p then
    if p ∣ N then 1-1/((p:ℝ)-1)^2 else 1+1/((p:ℝ)-1)^3
  else 1

/-- The actual ternary singular-series Euler constant. Convergence and numerical
bounds are separate theorem obligations, not assertions of this definition. -/
noncomputable def singularConstant (N : ℕ) : ℝ :=
  ∏' p : ℕ, singularEulerFactor N p

end Helfgott


