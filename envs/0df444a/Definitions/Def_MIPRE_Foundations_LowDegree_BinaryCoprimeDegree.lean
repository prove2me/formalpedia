-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
-- name    : MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:38.939892+00:00
-- url     : https://prove2.me/theorems/2e4b8f82-3e4d-4abd-b459-62bf12dcff11
-- title:
--   Definitions of BinaryCoprimeDegree: Exact degrees of sums with coprime binary field degrees
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryCoprimeDegree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact degrees of sums with coprime binary field degrees
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `frobenius_comm`, `iterate_add_delta`, `nsmul_delta_eq_zero`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryCoprimeDegree` (`MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Extension

/-! # Exact degrees of sums with coprime binary field degrees -/

noncomputable section

namespace MIPRE.LowDegree.BinaryFiniteField

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

theorem frobenius_comm (a b : ℕ) (x : R) :
    iterateFrobenius R 2 a (iterateFrobenius R 2 b x) =
      iterateFrobenius R 2 b (iterateFrobenius R 2 a x) := by
  rw [← iterateFrobenius_add_apply, Nat.add_comm a b, iterateFrobenius_add_apply]

omit [CharP R 2] in
theorem iterate_add_delta (F : R →+ R) (x d : R)
    (hx : F x = x + d) (hd : F d = d) (n : ℕ) : F^[n] x = x + n • d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hx, hd, succ_nsmul]
    abel

omit [CharP R 2] in
theorem nsmul_delta_eq_zero (F : R →+ R) (x : R) (n : ℕ)
    (hd : F (F x - x) = F x - x) (hx : F^[n] x = x) : n • (F x - x) = 0 := by
  have h := iterate_add_delta F x (F x - x) (by abel) hd n
  rw [hx] at h
  exact (add_left_cancel (show x + n • (F x - x) = x + 0 by simpa using h.symm))

variable {L : Type*} [Field L] [Algebra (ZMod 2) L]

end MIPRE.LowDegree.BinaryFiniteField

end


