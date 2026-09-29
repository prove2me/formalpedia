-- Prove2me | Definitions.Def_HlawkaSchatten_Final
-- name    : HlawkaSchatten_Final
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:41:44.784242+00:00
-- url     : https://prove2.me/theorems/1b9523b0-ac73-4b72-a47a-5753ecee591d
-- title:
--   Normalizing an operator to the Schatten power sphere, and its radial Mazur map
-- statement:
--   Fix finite-dimensional complex inner product spaces $E,F$, a real $p$, and $T:E\to F$.
--
--   - `schattenNormalized p T` $:= (\|T\|_p)^{-1}\bullet T$ — rescales $T$ to lie on the Schatten-$p$ unit-norm sphere. The definition is total: at $T=0$ it returns $0$ (using $0^{-1}=0$). The bundle proves that for $p>0$ and $T\neq0$, $\|\mathrm{schattenNormalized}\,p\,T\|_p=1$, equivalently `singularValuePowerSum p (schattenNormalized p T) = 1` — so the rescaled operator genuinely lands on the power sphere.
--   - `radialRectangularMazurMap p T` $:= \|T\|_p\bullet\mathrm{rectangularMazurMap}\,p\,(\mathrm{schattenNormalized}\,p\,T)$ — the "radial" variant of `rectangularMazurMap` (`HermitianDilation` bundle): the Mazur image of the *normalized direction* of $T$, rescaled back by $T$'s own Schatten norm rather than by any power of it.
--   - `radialMazurHilbertMap p T` $:=$ the Hilbert–Schmidt coordinates (`HilbertSchmidt` bundle), in $E$'s standard orthonormal basis, of `radialRectangularMazurMap p T` — a map into the Hilbert space $\mathrm{PiLp}\,2\,\bigl(\mathrm{Fin}(\dim_{\mathbb{C}}E)\to F\bigr)$. Per the source's doc comment and the separate page `norm_radialMazurHilbertMap` (proved for $p>0$), this rescaling is exactly what makes $\|\mathrm{radialMazurHilbertMap}\,p\,T\|=\|T\|_p$: the construction carries the Schatten-$p$ norm of $T$ to the ordinary Hilbert norm of its coordinatized image, not the same norm $\|\cdot\|_p$ preserved on both sides — `rectangularMazurMap` on its own instead carries the power *sum* $\sum_k\sigma_k^p$ of $T$ to $\sum_k\sigma_k(\cdot)^2$ of its image.
--   - `schattenPowerDirection hp T hT`, for $0<p$ and $T\neq0$, packages `schattenNormalized p T` together with the proof — via `singularValuePowerSum_normalized` — that it lies on the Schatten-$p$ power sphere, producing a genuine element of the subtype `schattenPowerSphere p`.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Final.lean#L24-L103

import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HilbertSchmidt
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Dimension-independent Hlawka constants for Schatten norms

This file removes the unit-sphere normalization from the variational
comparison and performs the final Hilbert-space Hlawka transfer.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Normalize a nonzero operator to the Schatten-`p` unit sphere.  The
definition is total; at zero it returns zero. -/
noncomputable def schattenNormalized (p : ℝ) (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F :=
  (((schattenPNorm p T)⁻¹ : ℝ) : ℂ) • T

theorem schattenPNorm_normalized {p : ℝ} (hp : 0 < p)
    {T : E →ₗ[ℂ] F} (hT : T ≠ 0) :
    schattenPNorm p (schattenNormalized p T) = 1 := by
  unfold schattenNormalized
  have hr : 0 < schattenPNorm p T := schattenPNorm_pos p hT
  rw [schattenPNorm_real_smul hp (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

theorem singularValuePowerSum_normalized {p : ℝ} (hp : 0 < p)
    {T : E →ₗ[ℂ] F} (hT : T ≠ 0) :
    singularValuePowerSum p (schattenNormalized p T) = 1 :=
  (schattenPNorm_eq_one_iff hp _).mp (schattenPNorm_normalized hp hT)



/-- The homogeneous rectangular Mazur map.  Unlike `rectangularMazurMap`,
this radial version preserves the Schatten norm rather than its power. -/
noncomputable def radialRectangularMazurMap
    (p : ℝ) (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F :=
  ((schattenPNorm p T : ℝ) : ℂ) •
    rectangularMazurMap p (schattenNormalized p T)

/-- Hilbert coordinates of the radial Mazur map. -/
noncomputable def radialMazurHilbertMap
    (p : ℝ) (T : E →ₗ[ℂ] F) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ E) => F) :=
  hilbertSchmidtCoordinates (stdOrthonormalBasis ℂ E)
    (radialRectangularMazurMap p T)







/-- A nonzero operator, normalized as an element of the Schatten power
sphere. -/
noncomputable def schattenPowerDirection {p : ℝ} (hp : 0 < p)
    (T : E →ₗ[ℂ] F) (hT : T ≠ 0) :
    schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p :=
  ⟨schattenNormalized p T, singularValuePowerSum_normalized hp hT⟩















end HlawkaSchatten


