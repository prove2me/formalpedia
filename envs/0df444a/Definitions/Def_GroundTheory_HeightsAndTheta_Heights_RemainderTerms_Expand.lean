-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:03.928226+00:00
-- url     : https://prove2.me/theorems/15e49256-05bf-4210-a378-83c7aae358c1
-- title:
--   Expand
-- statement:
--   Definitions and structural lemmas for Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
namespace Top
open MvPolynomial Finset
noncomputable section
def blockEmb (f N : ℕ) (σ : Fin f) : RootRing 1 N →ₐ[ℚ] RootRing f N :=
  rename (fun p : Fin 1 × Fin N => (σ, p.2))
def HasDD (f N : ℕ) (H P : RootRing f N) : Prop :=
  antisymmetrize f N H = blockVandermonde f N * P
def fib1 (r a : ℕ) (c : SmallBlock) : RootRing 1 (r + a) :=
  vandermondeOf (yRoot 1 r a c 0) * vandermondeOf (zRoot 1 r a c 0)
def yEval (r a : ℕ) (c : SmallBlock) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] RootRing 1 (r + a) :=
  aeval (yRoot 1 r a c 0)
def xSign (r a : ℕ) (c : SmallBlock) : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] RootRing 1 (r + a) :=
  aeval (fun i : Fin (r + a) => C c.sign * X ((0 : Fin 1), i))
def pushOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (lam : Fin r → ℕ) : RootRing 1 (r + a) :=
  if ∀ i, a ≤ lam i then C κ * xSign r a c (schur (Fin (r + a)) (fun i => lam i - a)) else 0
def extraFactor (r q : ℕ) : MvPolynomial (Fin r) ℚ := if q = 0 then 1 else psum (Fin r) ℚ q
def blockCoeff {r : ℕ} (q m : ℕ) (lam : Fin r → ℕ) : ℚ :=
  if q = 0 then (if m = 0 then 1 else symmetricGroupCharacter lam (List.replicate m 1))
  else symmetricGroupCharacter lam (q :: List.replicate m 1)
def blockOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) : RootRing 1 (r + a) :=
  ∑ lam ∈ partitionsOf r (q + m), blockCoeff q m lam • pushOut r a c κ lam
end
end Top
end RestTerms
end GroundTheory.Heights₂.Heights


