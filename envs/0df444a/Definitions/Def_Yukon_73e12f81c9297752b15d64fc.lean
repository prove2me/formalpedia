-- Prove2me | Definitions.Def_Yukon_73e12f81c9297752b15d64fc
-- name    : Yukon_73e12f81c9297752b15d64fc
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:47:08.610335+00:00
-- url     : https://prove2.me/theorems/8a5547e2-56f3-4101-a8fa-d063312da0c7
-- title:
--   YukonModule.CompPoly.Data.MvPolynomial.Notation.part0
-- statement:
--   Source module CompPoly.Data.MvPolynomial.Notation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Data/MvPolynomial/Notation.lean
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Data/MvPolynomial/Notation.lean
--
--   yukon-proof-operation:c0cdabd80766600b8959b7c65e4db4bf7d3fa7b31db776f6199190cee4a6c285
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YzBjZGFiZDgwNzY2NjAwYjg5NTliN2M2NWU0ZGI0YmY3ZDNmYTdiMzFkYjc3NmY2MTk5MTkwY2VlNGE2YzI4NSIsImhhc2giOiJkMGJjZmI0MjYyMTc5MTA3ZDhmYzBkNmM4Y2E2OWNlNjRlY2UxNzI0ODkxNGU3YzExOTcwZjE0NDczNGUzMmE2Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl83M2UxMmY4MWM5Mjk3NzUyYjE1ZDY0ZmMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Definitions.Def_Yukon_4ea09ef2c24092bc5b066c4c



public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Data.Finsupp.Fin
public import Init
public import Mathlib.Algebra.MvPolynomial.Equiv
meta import Definitions.Def_Yukon_4ea09ef2c24092bc5b066c4c
set_option backward.isDefEq.respectTransparency.types false
/-!
  # Useful Notation
    We define notation `R[X σ]` to be `MvPolynomial σ R`.

    For a Finset `s` and a natural number `n`, we also define `s ^ᶠ n` to be
    `Fintype.piFinset (fun (_ : Fin n) => s)`. This matches the intuition that `s ^ᶠ n`
    is the set of all tuples of length `n` with elements in `s`.
-/

@[expose] public section

noncomputable section

-- TODO: Upstream these to `Mathlib.Algebra.MvPolynomial.Equiv`
namespace MvPolynomial

section Equiv

variable (R : Type*) [CommSemiring R] {n : ℕ}

/-- Equivalence between `MvPolynomial (Fin 1) R` and `Polynomial R` -/
def finOneEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  (finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv R (Fin 0)))

end Equiv

end MvPolynomial

end

open MvPolynomial

@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃< " d "⦄[X]" => Polynomial.degreeLT R d
@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃≤ " d "⦄[X]" => Polynomial.degreeLE R d

@[inherit_doc] scoped[MvPolynomial] notation:9000 R "[X " σ "]"  => MvPolynomial σ R
@[inherit_doc] scoped[MvPolynomial] notation:9000
  R "⦃≤ " d "⦄[X " σ "]"  => MvPolynomial.restrictDegree σ R d

-- `𝔽⦃≤ 1⦄[X Fin n]` is the set of multilinear polynomials in `n` variables over `𝔽`.

notation:70 s:70 " ^^ " t:71 => Fintype.piFinset fun (i : t) ↦ s i
notation:70 s:70 " ^ᶠ " t:71 => Fintype.piFinset fun (i : Fin t) ↦ s


