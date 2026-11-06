-- Prove2me | Definitions.Def_MethodFulfillment_alg2Prob
-- name    : MethodFulfillment_alg2Prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:08.777879+00:00
-- url     : https://prove2.me/theorems/e2d03f25-6d64-4413-a0b1-183ddf8ea61d
-- title:
--   Availability probability of magician $(i,k)$ in Algorithm 2
-- statement:
--   In period $t$ of a run, magician $(i,k)$ with $S_{ik}>0$ makes its inventory available with probability $a^{tW}_{ik}$, where $W=W^t_{ik}$ is its usage so far and $a^{tl}_{ik}$ is the threshold rule of Appendix D for the level $\gamma_{ik}=1-1/\sqrt{S_{ik}+3}$ and the magician's inputs $\nu_{ik}$. In Algorithm 2 the inputs are the consumption probabilities $\mu^t_{ik}$ of (12); Appendix D also considers inputs that are only upper bounds on them, so the inputs are a parameter. A pair with $S_{ik}=0$ has no magician and is never made available.
--
--   **Formalization Note** The inputs $\nu_{ik}(t)$ are indexed from $0$ (the paper's period $t+1$).
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Algorithm 2, p.15; Appendix D, p.58

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Run
import Definitions.Def_MethodFulfillment_usage
import Definitions.Def_MethodFulfillment_gammaS
import Definitions.Def_MethodFulfillment_magF

namespace MethodFulfillment

/-- The probability that magician `(i, k)` of Algorithm 2 makes its inventory available at Lean
time `t` on the run `r` (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Algorithm 2,
p.15, Appendix D, p.58). The magician is given the consumption probabilities `ν i k`, the level
`γ_{ik} = 1 − 1/√(S_{ik} + 3)` (p.16) and its usage `W = usage r t i k`; it is available with
probability `a^{tW}`, the threshold rule of Appendix D for the recursion `magF (ν i k) γ_{ik}`.

**Formalization Note.** Algorithm 2 feeds the magicians the probabilities `μ^t_{ik}` of (12),
i.e. `ν = mu' P y`; that is how Theorem 1 uses this definition. Appendix D also considers inputs
that are only upper bounds on the consumption probabilities, so `ν` is a parameter. `ν i k t` is
the input at Lean time `t` (the paper's `t + 1`). Algorithm 2 has magicians only for `S_{ik} > 0`;
a pair with `S_{ik} = 0` is never made available (probability `0`). -/
noncomputable def alg2Prob {I K Q : Type} [DecidableEq I] [DecidableEq K] {T : ℕ}
    (P : Instance I K Q T) (ν : I → K → ℕ → ℝ) (t : Fin T) (r : Run I K Q T)
    (i : I) (k : K) : ℝ :=
  if 0 < P.S i k then
    aCoef (magF (ν i k) (gammaS (P.S i k)) t) (gammaS (P.S i k)) (usage r t i k)
  else 0

end MethodFulfillment


