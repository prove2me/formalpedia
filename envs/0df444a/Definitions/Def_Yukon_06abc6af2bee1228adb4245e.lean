-- Prove2me | Definitions.Def_Yukon_06abc6af2bee1228adb4245e
-- name    : Yukon_06abc6af2bee1228adb4245e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:37:00.02061+00:00
-- url     : https://prove2.me/theorems/68a7b0bb-409f-41bd-a718-4b637fd0f84b
-- title:
--   YukonModule.ArkLib.ToCompPoly.Univariate.Lagrange.part0
-- statement:
--   Source module ArkLib.ToCompPoly.Univariate.Lagrange.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToCompPoly/Univariate/Lagrange.lean
--
--   yukon-proof-operation:7ba938ac5b5468e0ac0df3ce22c0a9dc96e41c45546c9825ff5939b95b4666a8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODM0NmZjZGIzMmJjYzI1OTBhMGY5M2QzMTY0ZGYxMmZkYTM2YjAyNTg1ODg2ZDlmYzU3ZDJmY2Q0NTBjNDVkZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjdiYTkzOGFjNWI1NDY4ZTBhYzBkZjNjZTIyYzBhOWRjOTZlNDFjNDU1NDZjOTgyNWZmNTkzOWI5NWI0NjY2YTgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wNmFiYzZhZjJiZWUxMjI4YWRiNDI0NWUiLCJ2IjoyfQ]

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Definitions.Def_Yukon_5b023a2e28d9b62160ff10b5



import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Lagrange
set_option backward.isDefEq.respectTransparency.types false
/-!
  # Additions to `CompPoly.Univariate.Lagrange` not yet upstreamed to CompPoly.
-/

namespace CompPoly.CPolynomial.CLagrange

variable {R ι : Type*} [BEq R] [Field R] [LawfulBEq R] [DecidableEq ι]

lemma interpolation_of_constants (s : Finset ι) (x y : ι → R) (c : R)
    (hy : ∀ i ∈ s, y i = c) (hx : Set.InjOn x s) (hs : s.Nonempty) :
    interpolate s x y = CPolynomial.C c := by
  suffices h : (interpolate s x y).toPoly = (CPolynomial.C c).toPoly from
    CPolynomial.ringEquiv.injective h
  rw [cinterpolate_eq_interpolate, CPolynomial.C_toPoly]
  symm
  exact Lagrange.eq_interpolate_of_eval_eq y hx
    (lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Finset.card_pos.mpr hs))
    (fun i hi => by simp [hy i hi])

end CompPoly.CPolynomial.CLagrange


