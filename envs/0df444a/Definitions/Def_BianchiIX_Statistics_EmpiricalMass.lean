-- Prove2me | Definitions.Def_BianchiIX_Statistics_EmpiricalMass
-- name    : BianchiIX_Statistics_EmpiricalMass
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T19:06:43.192348+00:00
-- url     : https://prove2.me/theorems/28c0b688-be51-4256-a63a-772e9db3491b
-- title:
--   Empirical masses of a finite label sequence
-- statement:
--   For a sequence of labels $\ell:\mathbb N\to I$ and
--   $N\geq0$, define the empirical probability mass
--   $$p_N(i)=\frac1{N+1}\sum_{j=0}^N\mathbf1_{\{\ell_j=i\}}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EmpiricalMass.lean

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite empirical distributions with a strictly positive sample size. -/

open Filter
open scoped Topology

namespace BianchiIX

noncomputable section
open scoped Classical

/-- The distribution of the first `N + 1` labels. -/
def empiricalMass {ι : Type*} (label : ℕ → ι) (N : ℕ) (i : ι) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), if i = label j then 1 else 0







end
end BianchiIX


