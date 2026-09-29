-- Prove2me | Definitions.Def_HlawkaSchatten_HilbertSchmidt
-- name    : HlawkaSchatten_HilbertSchmidt
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:40:42.974038+00:00
-- url     : https://prove2.me/theorems/b6d34891-2deb-447a-87f1-4bb83405b484
-- title:
--   Hilbert–Schmidt coordinates, and the Schatten-2 quantity as a Hilbert norm
-- statement:
--   Fix $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$, a finite index type $\iota$, and finite-dimensional inner product spaces $E,F$ over $\mathbb{K}$. Fix an orthonormal basis $e=(e_i)_{i\in\iota}$ of $E$.
--
--   - `hilbertSchmidtCoordinates e T` $:= (T e_i)_{i\in\iota}$, packaged as a single element of the $\ell^2$-sum Hilbert space $\mathrm{PiLp}\,2\,(\iota\to F)$ — the tuple of "columns" of a linear map $T:E\to F$ read off in the basis $e$.
--   - `hilbertSchmidtLinearEquiv e` — the $\mathbb{K}$-linear equivalence between $E\to F$ and that same Hilbert space of column-tuples, with `hilbertSchmidtCoordinates e` as its forward map and basis-extension (Mathlib's `Basis.constr`) as its inverse.
--   - `schattenTwoPowerSphereEquivUnitSphere e` — the restriction of that equivalence identifying the Schatten-2 power sphere $\{T:\mathrm{singularValuePowerSum}\,2\,T=1\}$ (from the `SchattenNorm` bundle) with the ordinary unit sphere $\mathrm{unitSphere}\bigl(\mathrm{PiLp}\,2\,(\iota\to F)\bigr)$ (from the `Basic` bundle).
--
--   Together these definitions realize $\|T\|_2$ as an honest Hilbert-space norm: the bundle also proves that `hilbertSchmidtCoordinates` is additive, and that $\mathrm{singularValuePowerSum}\,2\,T$ equals both $\sum_i\|Te_i\|^2$ and $\|\mathrm{hilbertSchmidtCoordinates}\,e\,T\|^2$. This is what lets the classical Hlawka inequality for Hilbert-space norms be carried over to the Schatten-2 quantity.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HilbertSchmidt.lean#L27-L107

import Definitions.Def_HlawkaSchatten_Basic
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The Schatten-2 quantity as a Hilbert norm

This file realizes a finite-dimensional linear map by its values on an
orthonormal basis.  At exponent two, this coordinate map is an isometry for
the Schatten quantity defined from singular values.  Consequently the
Schatten-2 quantity satisfies Hlawka's inequality with constant one.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Hilbert--Schmidt coordinates of a linear map, obtained by evaluating it
on an orthonormal basis of its domain. -/
noncomputable def hilbertSchmidtCoordinates
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    PiLp 2 (fun _ : ι => F) :=
  WithLp.toLp 2 (fun i => T (e i))

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem hilbertSchmidtCoordinates_add
    (e : OrthonormalBasis ι 𝕜 E) (S T : E →ₗ[𝕜] F) :
    hilbertSchmidtCoordinates e (S + T) =
      hilbertSchmidtCoordinates e S + hilbertSchmidtCoordinates e T := by
  rfl

/-- Evaluation on an orthonormal basis is a linear equivalence from linear
maps to their finite family of columns. -/
noncomputable def hilbertSchmidtLinearEquiv
    (e : OrthonormalBasis ι 𝕜 E) :
    (E →ₗ[𝕜] F) ≃ₗ[𝕜] PiLp 2 (fun _ : ι => F) where
  toFun := hilbertSchmidtCoordinates e
  invFun x := e.toBasis.constr 𝕜 (WithLp.ofLp x)
  left_inv T := by
    apply e.toBasis.ext
    intro i
    change (e.toBasis.constr 𝕜 (fun j => T (e j))) (e i) = T (e i)
    exact e.toBasis.constr_basis 𝕜 _ i
  right_inv x := by
    apply WithLp.ofLp_injective 2
    funext i
    change (e.toBasis.constr 𝕜 (WithLp.ofLp x)) (e i) = WithLp.ofLp x i
    exact e.toBasis.constr_basis 𝕜 _ i
  map_add' := hilbertSchmidtCoordinates_add e
  map_smul' _ _ := rfl

/-- The exponent-two singular-value power sum is the sum of the squared
norms of the columns in any orthonormal basis. -/
theorem singularValuePowerSum_two_eq_sum_norm_sq
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 2 T = ∑ i, ‖T (e i)‖ ^ 2 := by
  rw [singularValuePowerSum_two_eq_re_trace,
    LinearMap.trace_eq_sum_inner (T.adjoint.comp T) e, map_sum]
  apply Fintype.sum_congr
  intro i
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := 𝕜) (T (e i))).symm



/-- The exponent-two power sum is the square of the Hilbert coordinate
norm. -/
theorem singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 2 T = ‖hilbertSchmidtCoordinates e T‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact singularValuePowerSum_two_eq_sum_norm_sq e T

/-- The Schatten-2 power sphere is exactly the ordinary unit sphere of the
Hilbert column-coordinate space. -/
noncomputable def schattenTwoPowerSphereEquivUnitSphere
    (e : OrthonormalBasis ι 𝕜 E) :
    schattenPowerSphere (𝕜 := 𝕜) (E := E) (F := F) 2 ≃
      unitSphere (PiLp 2 (fun _ : ι => F)) where
  toFun T := ⟨hilbertSchmidtCoordinates e T.1, by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e,
      T.property, one_pow]⟩
  invFun x := ⟨(hilbertSchmidtLinearEquiv e).symm x.1, by
    rw [singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e,
      show hilbertSchmidtCoordinates e ((hilbertSchmidtLinearEquiv e).symm x.1) =
          x.1 from (hilbertSchmidtLinearEquiv e).apply_symm_apply x.1,
      x.property, one_pow]⟩
  left_inv T := Subtype.ext ((hilbertSchmidtLinearEquiv e).symm_apply_apply T.1)
  right_inv x := Subtype.ext ((hilbertSchmidtLinearEquiv e).apply_symm_apply x.1)



end HlawkaSchatten


