-- Prove2me | Definitions.Def_Zeta23_FromPNTPlus_Mertens
-- name    : Zeta23_FromPNTPlus_Mertens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:04:40.286029+00:00
-- url     : https://prove2.me/theorems/a9e6891c-5094-4165-bb0e-181e86a0242e
-- title:
--   Mertens remainder $E_{1\Lambda}$ in von Mangoldt form
-- statement:
--   This bundle (ported from the PrimeNumberTheoremAnd project, file `Mertens.lean`; the Euler–Maclaurin section lives in the separate `EulerMaclaurin` bundle) defines the **remainder term in Mertens' first theorem**, in von Mangoldt form:
--   $$E_{1\Lambda}(x) := \sum_{0 < d \le \lfloor x\rfloor} \frac{\Lambda(d)}{d} - \log x,$$
--   where $\Lambda$ is the von Mangoldt function (`ArithmeticFunction.vonMangoldt`) and the sum runs over `Finset.Ioc 0 ⌊x⌋₊`. Mertens' first theorem is the statement that $E_{1\Lambda}$ is bounded, which the surrounding module proves (`E₁Λ.bounded'`, with explicit two-sided estimates `E₁Λ.ge`, `E₁Λ.le`), following Goldmakher's quick proof via Euler–Maclaurin and Stirling-type factorial estimates.
--
--   In the project this supplies Chebyshev–Mertens-type input for the H-cheb hypothesis (`Zeta23/Chebyshev.lean`), one of the classical analytic inputs consumed by the prime-side trace computations behind Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/Mertens.lean

import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mertens.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Original authors per that project's blueprint (Euler–Maclaurin and Mertens
sections drawn from Leo Goldmakher, "A quick proof of Mertens' theorem",
https://web.williams.edu/Mathematics/lg5/mertens.pdf).

Declarations ported (source lines 1–371):
  Mertens.sum_Ioc_one_eq_sum_Ioc_zero, Mertens.sum_log_eq, Mertens.sum_log_le,
  Mertens.integral_log_le, Mertens.sum_log_ge, Mertens.sum_log_eq_log_factorial,
  Mertens.sum_log_eq_sum_mangoldt, Mertens.E₁Λ, Mertens.sum_mangoldt_div_eq,
  Mertens.E₁Λ.ge, Mertens.E₁Λ.le, Mertens.sum_mangoldt_div_eq_log,
  Mertens.E₁Λ.bounded'.

Local modifications:
  * the source's `section EulerMaclaurin` (B1 ... sum_eq_integral_add_integral_deriv)
    now lives in Zeta23/FromPNTPlus/EulerMaclaurin.lean (re-ported from upstream
    v4.32.2, where that section was split out of Mertens.lean into its own file),
    imported here;
  * dropped `import Architect` and all `@[blueprint ...]` attributes and
    `blueprint_comment` blocks (blueprint tooling we do not vendor); statement
    text retained as plain docstrings on the main theorems;
  * dropped three root-level helpers unused by the ported region (each is
    referenced only past our truncation point): Filter.EventuallyEq.iff_eventually,
    Real.inv_log_eq_o_one, Real.one_eq_o_log_log — nothing is injected into the
    Real or Filter namespaces by this file;
  * dropped a stray `#check ArithmeticFunction.vonMangoldt_sum`;
  * truncated after E₁Λ.bounded' (everything later — the sorry'd E₁Λ.bounded,
    the prime-form/second/third theorems — is not ported; no sorry enters);
  * added the closing `end Mertens`.
Modified 2026 by Anthropic PBC.
-/




namespace Mertens


open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log










/-- The remainder term in Mertens' first theorem (von Mangoldt form): `E₁Λ x = ∑ d ≤ x, Λ(d)/d - log x`. -/
noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x







end Mertens


