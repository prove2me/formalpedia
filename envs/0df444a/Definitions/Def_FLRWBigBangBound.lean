-- Prove2me | Definitions.Def_FLRWBigBangBound
-- name    : FLRWBigBangBound
-- status  : Definition
-- author  : @LG
-- created : 2026-11-25T01:58:56.704798+00:00
-- url     : https://prove2.me/theorems/e19da5b8-3da0-4eb8-8391-6c47d25edffe
-- title:
--   Real-time FLRW model for the Big-Bang bound
-- statement:
--   A spatial geometry is spherical with a real parameter k<0, flat with no parameter, or saddle with a real parameter k>0. An FLRWModel consists of a set I of real times that is open and order-connected, a function a:ℝ→ℝ, positivity a(t)>0 for every t∈I, differentiability of a on I, differentiability of its derivative on I, and one of the three spatial-geometry values. The function is specified on all real numbers, but these positivity and differentiability conditions apply only on I; no nonemptiness or boundedness of I is required. The definition uses real time as a Mathlib-only representation of the upstream model data.
-- source:
--   Joseph Tooby-Smith and Luis Gabriel C. Bariuan, Physlib, “The Friedmann–Lemaître–Robertson–Walker metric,” Physlib/Cosmology/FLRW/Basic.lean, commit 85bb8f5df598f6701be57a70f06e08069e30589c; https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/Cosmology/FLRW/Basic.lean; model definition at lines 32–144.

import Mathlib

/-!
A Mathlib-only representation of the model data used in the Big-Bang bound from
`Physlib/Cosmology/FLRW/Basic.lean`. Cosmic time is represented directly by `ℝ`;
this is equivalent to Physlib's `Time` coordinate for the real-valued scale factor.
-/
namespace CosmologyFLRW

/-- The three spatial-curvature cases used by the FLRW model. -/
inductive SpatialGeometry : Type where
  | Spherical (k : ℝ) (h : k < 0)
  | Flat
  | Saddle (k : ℝ) (h : k > 0)

/-- An FLRW model on an open interval of real cosmic time. The scale factor is
positive and twice differentiable on the interval, and the model includes its
spatial geometry. -/
structure FLRWModel where
  I : Set ℝ
  isOpen_I : IsOpen I
  ordConnected_I : I.OrdConnected
  a : ℝ → ℝ
  a_pos : ∀ t ∈ I, 0 < a t
  differentiableOn_a : DifferentiableOn ℝ a I
  differentiableOn_deriv_a : DifferentiableOn ℝ (deriv a) I
  geometry : SpatialGeometry

end CosmologyFLRW


