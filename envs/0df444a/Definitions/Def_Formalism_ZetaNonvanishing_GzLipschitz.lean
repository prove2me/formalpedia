-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
-- name    : Formalism_ZetaNonvanishing_GzLipschitz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:19.865905+00:00
-- url     : https://prove2.me/theorems/cc9db7b3-3ed1-45f2-b6d2-046426ee33f9
-- title:
--   Gz Lipschitz
-- statement:
--   Definitions and structural lemmas for Gz Lipschitz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean

import Definitions.Def_Formalism_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
namespace Formalism
namespace LogFactorialMertensBounds
def A (k : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 k, Λ n / n
def P (k : ℕ) (x : ℝ) : ℝ :=
  x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x
def K0 : ℝ := Real.log 4 + 7
end LogFactorialMertensBounds
end Formalism


