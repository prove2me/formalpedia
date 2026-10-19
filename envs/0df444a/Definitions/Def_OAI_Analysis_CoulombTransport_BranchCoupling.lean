-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
-- name    : OAI_Analysis_CoulombTransport_BranchCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:30:35.389905+00:00
-- url     : https://prove2.me/theorems/96c120cd-5922-4e3f-a7fe-c5bb59136689
-- title:
--   Symmetrized couplings supported on two branch graphs
-- statement:
--   Work in $\mathbb{R}^3$. The three-body Coulomb cost of a triple $(x,y,z)$ is $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$, with $0^{-1}=\infty$. A three-coupling of a probability measure $\mu$ is a probability measure on triples whose three coordinate marginals all equal $\mu$. For maps $f,g,h$ of $\mathbb{R}^3$ let $\Gamma_{f,g,h}(x)=(f(x),g(x),h(x))$. For a measure $\nu$ and maps $H_1,\dots,H_4$:
--
--   1. the branch marginal is
--   $$
--   \frac13\nu+\frac16\bigl(H_{1\#}\nu+H_{2\#}\nu+H_{3\#}\nu+H_{4\#}\nu\bigr);
--   $$
--   2. the branch coupling is $\frac16$ times the sum of the pushforwards of $\nu$ under $\Gamma_{\mathrm{id},H_1,H_2}$, $\Gamma_{H_1,H_2,\mathrm{id}}$, $\Gamma_{H_2,\mathrm{id},H_1}$, $\Gamma_{\mathrm{id},H_3,H_4}$, $\Gamma_{H_3,H_4,\mathrm{id}}$, $\Gamma_{H_4,\mathrm{id},H_3}$.
--
--   Each of the two branches is averaged over its three cyclic orderings. This makes all three marginals equal to the branch marginal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchCoupling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A graph with all three coordinates explicitly specified. -/
def branchGraph (f g h : E3 → E3) : E3 → Triple := fun x => (f x, (g x, h x))

/-- The marginal used by the two-branch construction. -/
def branchMarginal (nu : Measure E3) (H1 H2 H3 H4 : E3 → E3) : Measure E3 :=
  (1 / 3 : ℝ≥0∞) • nu +
    (1 / 6 : ℝ≥0∞) • (Measure.map H1 nu + Measure.map H2 nu +
      Measure.map H3 nu + Measure.map H4 nu)

/-- Each branch is averaged over its three cyclic coordinate orderings. -/
def branchCoupling (nu : Measure E3) (H1 H2 H3 H4 : E3 → E3) : Measure Triple :=
  (1 / 6 : ℝ≥0∞) •
    (Measure.map (branchGraph id H1 H2) nu +
      Measure.map (branchGraph H1 H2 id) nu +
      Measure.map (branchGraph H2 id H1) nu +
      Measure.map (branchGraph id H3 H4) nu +
      Measure.map (branchGraph H3 H4 id) nu +
      Measure.map (branchGraph H4 id H3) nu)

end Problem356

end

end OAI


