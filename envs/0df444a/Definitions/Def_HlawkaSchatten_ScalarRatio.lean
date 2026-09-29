-- Prove2me | Definitions.Def_HlawkaSchatten_ScalarRatio
-- name    : HlawkaSchatten_ScalarRatio
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:28:05.519174+00:00
-- url     : https://prove2.me/theorems/df73a47b-4352-43cf-883e-abe1d0d58384
-- title:
--   The scalar Bregman-to-Mazur ratio, regularized and compactified
-- statement:
--   For real $p,t$, using the scalar Bregman divergence $\beta_p$ and scalar Mazur map $\psi_p$ from the `ScalarBregman` bundle:
--
--   - `scalarRatio p t` $:= \beta_p(t,1)\big/(\psi_p(t)-1)^2$ — the Bregman-to-Mazur ratio, with its second scalar argument normalized to $1$.
--   - `regularizedScalarRatio p t` $:=$ if $t=1$ then $2(p-1)/p^2$ else `scalarRatio p t` — the same ratio with its removable singularity at $t=1$ (where the denominator $(\psi_p(t)-1)^2$ vanishes) patched by the value $2(p-1)/p^2$, which is the limit of `scalarRatio p` at $t=1$ for $p>1$ (`tendsto_scalarRatio_one`, a separate page).
--   - `compactifiedScalarRatio p` (a function `OnePoint ℝ → ℝ`) — extends `regularizedScalarRatio p` to the one-point compactification of $\mathbb{R}$, assigning the point at infinity the value $1/p$, which is the limit of the ratio as $t\to\pm\infty$ for $p>1$ (`tendsto_scalarRatio_atTop`/`atBot` in the source module). At $p=1$ the ratio is identically $0$ for $t>0$, so this assigned value does not match a limit at every $p$.
--
--   These three definitions build, in stages, a function on a *compact* domain, which is what lets a compactness argument (elsewhere) produce a uniform two-sided bound $m_p\le\text{ratio}\le M_p$ on the compactified real line — the "scalar comparison" step of the construction.
--
--   One embedded algebraic fact is included: `scalarMazur_sq`, that for $p>0$, $\psi_p(a)^2=|a|^p$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarRatio.lean#L23-L556

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The scalar Bregman--Mazur ratio

This file starts the compact scalar-reduction layer of the Schatten Hlawka
argument.  The raw quotient has a removable singularity at `t = 1`; the
regularized version installs its second-order limiting value.
-/

namespace HlawkaSchatten

open Filter Set
open scoped OnePoint Topology

/-- The Bregman-to-Mazur ratio after normalizing the second scalar to one. -/
noncomputable def scalarRatio (p t : ℝ) : ℝ :=
  scalarBregman p t 1 / (scalarMazur p t - 1) ^ 2

/-- The scalar ratio with its removable value installed at `t = 1`. -/
noncomputable def regularizedScalarRatio (p t : ℝ) : ℝ :=
  if t = 1 then 2 * (p - 1) / p ^ 2 else scalarRatio p t









































































/-- The scalar ratio on the one-point compactification of the real line. -/
noncomputable def compactifiedScalarRatio (p : ℝ) : OnePoint ℝ → ℝ :=
  fun x ↦ x.elim (1 / p) (regularizedScalarRatio p)











/-- Squaring the scalar Mazur map recovers the degree-`p` absolute power. -/
theorem scalarMazur_sq {p : ℝ} (hp : 0 < p) (a : ℝ) :
    (scalarMazur p a) ^ 2 = |a| ^ p := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow hp.ne']
  · have habs : 0 < |a| := abs_pos.mpr ha
    have hpow : (|a| ^ (p / 2)) ^ 2 = |a| ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul habs.le]
      congr 1
      ring
    rcases lt_or_gt_of_ne ha with haneg | hapos
    · simp [scalarMazur, signedPower, sign_neg haneg, hpow]
    · simp [scalarMazur, signedPower, sign_pos hapos, hpow]







end HlawkaSchatten


