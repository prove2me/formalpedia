-- Prove2me | Definitions.Def_HlawkaSchatten_Variational
-- name    : HlawkaSchatten_Variational
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:42:55.901652+00:00
-- url     : https://prove2.me/theorems/261c7d76-7090-4dc2-899f-297b5533d60b
-- title:
--   Attained global minima, and weighted Hilbert/Bregman objectives on the Schatten power sphere
-- statement:
--   - `IsGlobalMinimumValue f value` (a `Prop`, for $f:A\to\mathbb{R}$ on any type $A$) $:= \bigl(\forall x,\ \mathrm{value}\le f(x)\bigr) \wedge \bigl(\exists x,\ f(x)=\mathrm{value}\bigr)$ — "$\mathrm{value}$ is an attained global minimum of $f$."
--
--   For a finite index type $\iota$, a scalar field $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$, and an inner product space $H$ over $\mathbb{K}$, with real weights $a:\iota\to\mathbb{R}$ and a family $u:\iota\to H$:
--   - `weightedHilbertSum a u` $:=\sum_i a_i\,u_i\in H$.
--   - `weightedHilbertObjective a u v` $:=\sum_i a_i\,\|u_i-v\|^2$ — the weighted sum-of-squared-distances objective, as a function of the "center" $v\in H$.
--
--   For finite-dimensional complex inner product spaces $E,F$, a finite index type $\kappa$, and $p\in\mathbb{R}$, working with elements of the Schatten-$p$ power sphere (`schattenPowerSphere p`, `SchattenNorm` bundle) of $E\to F$ operators:
--   - `rectangularMazurHilbertSphereEquiv e hp`, for an orthonormal basis $e$ of $E$ and $0<p$, composes the rectangular-Mazur power-sphere equivalence (`HermitianDilation` bundle) with the Hilbert-coordinate equivalence (`HilbertSchmidt` bundle) to identify the Schatten-$p$ power sphere directly with an ordinary Hilbert unit sphere.
--   - `rectangularMazurDistanceObjective p a u v` $:=\sum_i a_i\cdot\bigl(\text{Schatten-2 power sum of } \mathrm{rectangularMazurMap}\,p\,u_i-\mathrm{rectangularMazurMap}\,p\,v\bigr)$ — the weighted squared Hilbert–Schmidt distance between rectangular-Mazur images of a family $u:\iota\to(\text{power sphere})$, against a fixed $v$ on the same sphere.
--   - `rectangularMazurBarycenter p a u` $:=\sum_i a_i\cdot\mathrm{rectangularMazurMap}\,p\,(u_i)\in E\to F$ — the $\mathbb{C}$-weighted barycenter of the *rectangular-Mazur images* of the family's underlying operators.
--   - `rectangularBregmanObjective p a u v` $:=\sum_i a_i\cdot\bigl(\mathrm{dilatedBregmanTrace}\,p\,u_i\,v\bigr)/2$ — the weighted rectangular Bregman objective (`HermitianDilation` bundle), with the $1/2$ removing the two-copy normalization coming from Hermitian dilation.
--   - `rectangularWeightedSum a u` $:=\sum_i a_i\cdot u_i\in E\to F$ — the plain $\mathbb{C}$-weighted sum of the family's own, already power-sphere-normalized, underlying operators, with **no** Mazur map applied.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L23-L212

import Definitions.Def_HlawkaSchatten_Basic
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
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace ComplexConjugate

/-- `value` is an attained global minimum of `f`. -/
def IsGlobalMinimumValue {A : Type*} (f : A → ℝ) (value : ℝ) : Prop :=
  (∀ x, value ≤ f x) ∧ ∃ x, f x = value





variable {𝕜 H ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Real-weighted sum of a finite family in a real or complex inner-product
space. -/
noncomputable def weightedHilbertSum (a : ι → ℝ) (u : ι → H) : H :=
  ∑ i, (a i : 𝕜) • u i

/-- Weighted squared-distance objective used in the Hilbert variational
identity. -/
noncomputable def weightedHilbertObjective
    (a : ι → ℝ) (u : ι → H) (v : H) : ℝ :=
  ∑ i, a i * ‖u i - v‖ ^ 2







section RectangularMazur

variable {E F κ : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The rectangular Mazur equivalence followed by Hilbert--Schmidt column
coordinates identifies the Schatten-`p` power sphere with an ordinary
Hilbert unit sphere. -/
noncomputable def rectangularMazurHilbertSphereEquiv
    (e : OrthonormalBasis κ ℂ E) {p : ℝ} (hp : 0 < p) :
    schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p ≃
      unitSphere (PiLp 2 (fun _ : κ => F)) :=
  (rectangularMazurPowerSphereEquiv hp).trans
    (schattenTwoPowerSphereEquivUnitSphere e)

/-- Weighted squared Schatten-2 distance between rectangular Mazur images,
parametrized on the original Schatten-`p` power sphere. -/
noncomputable def rectangularMazurDistanceObjective
    (p : ℝ) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) : ℝ :=
  ∑ i, a i * singularValuePowerSum 2
    (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)

/-- Weighted barycenter of the rectangular Mazur images. -/
noncomputable def rectangularMazurBarycenter
    (p : ℝ) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    E →ₗ[ℂ] F :=
  ∑ i, (a i : ℂ) • rectangularMazurMap p (u i).1

/-- Weighted rectangular Bregman objective, normalized by the two copies in
the Hermitian dilation. -/
noncomputable def rectangularBregmanObjective
    (p : ℝ) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) : ℝ :=
  ∑ i, a i * (dilatedBregmanTrace p (u i).1 v.1 / 2)

/-- Weighted sum of the original Schatten-`p` unit operators. -/
noncomputable def rectangularWeightedSum
    {p : ℝ} (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    E →ₗ[ℂ] F :=
  ∑ i, (a i : ℂ) • (u i).1





















end RectangularMazur

end HlawkaSchatten


