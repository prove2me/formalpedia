-- Prove2me | Definitions.Def_HodgeComputerCycleQ2GradedLinear
-- name    : HodgeComputerCycleQ2GradedLinear
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-23T23:55:25.776409+00:00
-- url     : https://prove2.me/theorems/845c2557-3261-45b2-9656-300bc1d64429
-- title:
--   Graded linear form of the chart-divergence equation
-- statement:
--   Fix a denominator $S$, numerator components $W_j$, and a quotient $Q$. Write $\Delta$ for the two-monomial source and $\mathrm{chartDivergence}(S,W)$ for the sum of the five numerator terms. The graded linear operator and its inhomogeneous term are
--
--   $$\mathrm{gradedLinear}(S,W,Q) = \mathrm{chartDivergence}(S,W) - F^2 Q,$$
--
--   $$\mathrm{gradedInhomogeneous}(S) = -S^2\Delta.$$
--
--   The equation $\mathrm{gradedLinear}(S,W,Q) = \mathrm{gradedInhomogeneous}(S)$ is the divergence-carrier equation rewritten as a linear system in $(W,Q)$ for fixed $S$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_homogeneous_quotient_membership, https://prove2.me/theorems/e1b484fe-a669-4584-8d96-580dd070803a. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- The `(W, Q)`-linear left-hand side of the graded residue equation. -/
def HodgeComputer.CycleQ2.gradedLinear (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n)
    (Q : AmbientPoly n) : AmbientPoly n :=
  let div : AmbientPoly 5 := chartDivergence S W
  let Q5 : AmbientPoly 5 := Q
  let F5 : AmbientPoly 5 := F
  div - F5 ^ 2 * Q5

/-- The inhomogeneous term `-(S ^ 2 * sparseSource)`. -/
def HodgeComputer.CycleQ2.gradedInhomogeneous (S : AmbientPoly n) : AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let src : AmbientPoly 5 := sparseSource
  (-1 : AmbientPoly 5) * (S5 ^ 2 * src)


