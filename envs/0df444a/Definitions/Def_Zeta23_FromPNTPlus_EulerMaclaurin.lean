-- Prove2me | Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
-- name    : Zeta23_FromPNTPlus_EulerMaclaurin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:03:33.958535+00:00
-- url     : https://prove2.me/theorems/e61bbf74-9e4f-4778-9819-e2bc0f854389
-- title:
--   First Bernoulli function $B_1(x) = x - \lfloor x\rfloor - 1/2$
-- statement:
--   This bundle (ported verbatim from the PrimeNumberTheoremAnd project, file `EulerMaclaurin.lean`) defines the **first Bernoulli function**
--   $$B_1(x) := x - \lfloor x\rfloor_{\mathbb{N}} - \tfrac12,$$
--   the sawtooth kernel of the first-order Euler–Maclaurin formula. The surrounding module proves that formula — expressing a sum $\sum_{a < n \le b} f(n)$ as an integral plus a correction integral against $B_1$ — by specialising Abel summation.
--
--   In the project this feeds `Zeta23.FromPNTPlus.Mertens` (the Mertens-type estimates behind the Chebyshev–Mertens hypothesis H-cheb) and the `ZetaBounds` port, whose Euler–Maclaurin representation of $\zeta$ underlies the unconditional zeta bounds used in the zero-counting inputs.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/EulerMaclaurin.lean

import Mathlib.NumberTheory.AbelSummation

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/


/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

@[expose] public section

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2


