-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:26.768895+00:00
-- url     : https://prove2.me/theorems/fdc3e733-c5ca-42f6-9128-3f5fc929735b
-- title:
--   Plane Gen
-- statement:
--   Definitions and structural lemmas for Plane Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
def bf (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ fun i => c (v i)
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
structure PlaneOK (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x y : Fin n → R) (ι : Matrix (Fin n) (Fin k) R) : Prop where
  cc : ∀ a, c (c a) = a
  ee : ε * ε = 1
  ce : c ε = ε
  herm : ∀ i j, c (J j i) = ε * J i j
  xx : bf c J x x = 0
  yy : bf c J y y = 0
  xy : bf c J x y = 1
  ix : ∀ z, bf c J (ι *ᵥ z) x = 0
  iy : ∀ z, bf c J (ι *ᵥ z) y = 0
  span : ∀ v, ∃ (s t : R) (z : Fin k → R), v = s • x + ι *ᵥ z + t • y
  nd : ∀ v, (∀ w, bf c J v w = 0) → v = 0
namespace PlaneOK
variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h
omit h in

def lev (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) + ((s - 1) * ε) • vecMulVec y (J *ᵥ fun i => c (x i))
end PlaneOK
end PositivityTheory.Mix


