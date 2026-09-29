-- Prove2me | Definitions.Def_Zeta23_FromPNTPlus_Fourier
-- name    : Zeta23_FromPNTPlus_Fourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:04:19.080549+00:00
-- url     : https://prove2.me/theorems/91e06d05-4d53-48df-82c0-208383ad42d2
-- title:
--   Fourier lemmas port: real-to-complex coercion instance
-- statement:
--   This bundle (ported from the PrimeNumberTheoremAnd project, file `Fourier.lean`) contributes a single local coercion instance: for any type $E$, a function $f : E \to \mathbb{R}$ is coerced to $E \to \mathbb{C}$ pointwise ($x \mapsto (f(x) : \mathbb{C})$). This is notation-level infrastructure — it lets the Fourier-analytic lemmas of the port state results about real test functions inside complex-valued Fourier theory without explicit casts.
--
--   The surrounding module carries the Fourier-transform lemmas of the PNT+ port (built on the `Sobolev` bundle's classes $C_c^n$ and $W^{1,n}$), which serve the Fourier-analytic infrastructure of the project's `FromPNTPlus` chain, including the `ZetaBounds` port.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/Fourier.lean

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Fourier.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: redirected the intra-project import to Zeta23.FromPNTPlus.Sobolev.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Adjusted for Lean v4.33.0-rc2 / Mathlib 51e6992efd06: `Circle.norm_coe` supplied explicitly to two `simp` calls.
Modified 2026 by Anthropic PBC.
-/

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas











end lemmas


