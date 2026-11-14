-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowCounts
-- name    : ConsistentSubmodular_Deterministic_Reduction_WindowCounts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:10.141206+00:00
-- url     : https://prove2.me/theorems/a6d6aaef-3c23-4a36-8426-3c858842714e
-- title:
--   Bounds on tests, forced elements and path length for a window
-- statement:
--   For natural numbers $N$ (grid parameter) and $S$ (number of segments), with $\mathrm{logBudget}(x)=\lfloor\log_2 x\rfloor+1$:
--
--   - `windowTestBound N S`: the number of tests used for a window,
--   $$M(N,S)=100\,(N+1)^2\,(S+1).$$
--   - `windowHeavyBound N S`: the forced-element reserve,
--   $$64\,N^{2}\cdot\mathrm{logBudget}\bigl(4\,M(N,S)\bigr),$$
--   that is, the inverse of a threshold $\theta$ of order $N^{-2}/\log M$ for $M$ tests, as for $\theta=\eta^2/(4\log(8M))$ in Appendix B.2.3.
--   - `windowLengthBound S`: the bound $100\,S+10$ on the length of a rounded window, in units of the core budget $\kappa$.
--
--   These explicit constants parametrize the concentration-based rounding of fractional windows in the deterministic reduction (Appendix B.2): they fix how many sampled tests, forced elements and physical operations a rounded window may use.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/WindowCounts.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundingBudget

namespace ConsistentSubmodular

def windowTestBound (N S : ℕ) : ℕ := 100 * (N + 1) ^ 2 * (S + 1)

/-- The forced-element reserve: `θ⁻¹` with `θ` of order `N⁻² / log M` for
`M` tests, as for `θ = η² / (4 log(8M))` in Appendix B.2.3. -/
def windowHeavyBound (N S : ℕ) : ℕ := 64 * N ^ 2 * logBudget (4 * windowTestBound N S)

def windowLengthBound (S : ℕ) : ℕ := 100 * S + 10

end ConsistentSubmodular


