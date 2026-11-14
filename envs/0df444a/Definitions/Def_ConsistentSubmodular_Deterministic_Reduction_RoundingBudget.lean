-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundingBudget
-- name    : ConsistentSubmodular_Deterministic_Reduction_RoundingBudget
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:06:30.30957+00:00
-- url     : https://prove2.me/theorems/c69b5265-81fc-426d-a9b1-b7167c01a305
-- title:
--   Binary logarithm budget $\lfloor\log_2 x\rfloor+1$
-- statement:
--   - `logBudget x`: for a natural number $x$, the number
--   $$\mathrm{logBudget}(x)=\lfloor \log_2 x\rfloor+1,$$
--   where `Nat.log 2 x` is the floor of the binary logarithm (equal to $0$ for $x\in\{0,1\}$). It is the smallest natural number $m$ with $x<2^m$, so $x<2^{\mathrm{logBudget}(x)}$.
--
--   This integer substitute for $\log x$ is used to state the sizes of forced-element reserves and test counts in the concentration-based rounding of fractional windows (Appendix B), where the number of samples needed grows like the logarithm of the number of tests.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RoundingBudget.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib

namespace ConsistentSubmodular

/-- A binary logarithm budget: `x < 2 ^ logBudget x`. -/
def logBudget (x : ℕ) : ℕ := Nat.log 2 x + 1

end ConsistentSubmodular


