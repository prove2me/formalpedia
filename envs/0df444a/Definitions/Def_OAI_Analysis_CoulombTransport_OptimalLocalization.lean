-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
-- name    : OAI_Analysis_CoulombTransport_OptimalLocalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:38:01.710645+00:00
-- url     : https://prove2.me/theorems/1f177377-3b75-4c31-9451-0956c66a28a8
-- title:
--   Shifted dual certificates for the Coulomb problem
-- statement:
--   Work in $\mathbb{R}^3$. The three-body Coulomb cost of a triple $(x,y,z)$ is $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$, with $0^{-1}=\infty$. A three-coupling of a probability measure $\mu$ is a probability measure on triples whose three coordinate marginals all equal $\mu$. A shifted Coulomb certificate for $\mu$ with value $V$ consists of a potential $\Phi\ge0$ on triples and a finite shift $s$ such that, for every three-coupling $\pi$ of $\mu$,
--   $$
--   \Phi\le c+s\quad\pi\text{-a.e.},\qquad\int\Phi\,d\pi=V+s .
--   $$
--
--   Then every coupling has cost at least $V$. The shift allows bounded signed potentials to be used inside nonnegative integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/OptimalLocalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/OptimalLocalization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A nonnegative dual certificate after adding a finite constant to the cost.
The shift permits a signed bounded real-valued supporting potential. -/
structure ShiftedCoulombCertificate (mu : Measure E3) (value : ℝ≥0∞) where
  potential : Triple → ℝ≥0∞
  shift : ℝ≥0∞
  shift_ne_top : shift ≠ ⊤
  lower_bound : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
    ∀ᵐ t ∂pi, potential t ≤ coulombCost t + shift
  integral_eq : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
    (∫⁻ t, potential t ∂pi) = value + shift

namespace ShiftedCoulombCertificate

variable {mu : Measure E3} {value : ℝ≥0∞}

end ShiftedCoulombCertificate

end Problem356

end

end OAI


