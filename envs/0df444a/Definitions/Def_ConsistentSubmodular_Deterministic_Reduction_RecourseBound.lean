-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound
-- name    : ConsistentSubmodular_Deterministic_Reduction_RecourseBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:15:54.561484+00:00
-- url     : https://prove2.me/theorems/6eeccd01-563e-4096-88e1-2b7c84edfb8c
-- title:
--   Recourse constant, accuracy choice, and rate constants $A_C$, $K_C$ of the reduction (Theorem 5)
-- statement:
--   - `reductionRecourse` $N\,S$: the recourse constant for accuracy $1/N$ when compressed windows have at most $S$ segments,
--   $$2\,T(N,H_S)+4N(4N+1)\bigl(3\Lambda_S+1\bigr)+2,$$
--   where $T=$ `transferThreshold`, $H_S=$ `familyHeavy` $N\,S$ and $\Lambda_S=$ `familyLength` $S$.
--   - `accuracy` $\varepsilon$: the accuracy parameter $N=\lfloor 20/\varepsilon\rfloor+200$ for slack $\varepsilon$. This is an integer with $N\ge 200$, $20/N<\varepsilon$ and $N\le 220/\varepsilon$ (for $\varepsilon\le 1$).
--   - `rateConstant` $C$: the real number $A_C=256\ln\bigl(1200(C+1)\bigr)+1034+31220\,(C+1)$, the constant in the bound $N^3\,(A_C+800\ln N)$.
--   - `reductionConstant` $C$: $K_C=220^3\,\bigl(4A_C+20000\bigr)$, the constant of Theorem 5.
--
--   Here $C$ is a natural number, $N,S$ are natural numbers and $\varepsilon>0$.
--
--   These definitions fix the explicit constants in the final quantitative statement of the deterministic reduction (Theorem 5, Appendix B.2): for slack $\varepsilon$ one takes $N=$ `accuracy` $\varepsilon$ and bounds the recourse by `reductionRecourse` $N\,S$, then expresses it as $K_C$ times a power of $1/\varepsilon$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RecourseBound.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformRoundedFamilies

noncomputable section

namespace ConsistentSubmodular

/-- The recourse constant for accuracy `1/N` when compressed windows have at
most `S` segments. -/
def reductionRecourse (N S : ℕ) : ℕ :=
  2 * transferThreshold N (familyHeavy N S) +
    4 * N * (4 * N + 1) * (3 * familyLength S + 1) + 2

/-- The accuracy parameter for slack `ε`: an integer `N ≥ 200` with `20/N < ε`
and `N ≤ 220/ε`. -/
def accuracy (ε : ℝ) : ℕ := ⌊20 / ε⌋₊ + 200

/-- The constant `A_C` of the bound `N³ (A_C + 800 log N)`. -/
def rateConstant (C : ℕ) : ℝ :=
  256 * Real.log (1200 * ((C : ℝ) + 1)) + 1034 + 31220 * ((C : ℝ) + 1)

/-- The constant `K_C` of Theorem 5. -/
def reductionConstant (C : ℕ) : ℝ := 220 ^ 3 * (4 * rateConstant C + 20000)

end ConsistentSubmodular

end


