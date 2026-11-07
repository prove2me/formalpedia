-- Prove2me | Definitions.Def_CompNonlocal_IsEffect
-- name    : CompNonlocal_IsEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:45.411198+00:00
-- url     : https://prove2.me/theorems/405f6d3c-1030-4019-9318-8d9f38a38c38
-- title:
--   Effects $0\le E\le I$
-- statement:
--   An **effect** on a finite-dimensional Hilbert space is a Hermitian operator $E$ with
--   $$0\preceq E\preceq I .$$
--   It describes a binary test accepting the state $\omega$ with probability $\operatorname{Tr}(E\omega)$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19

import Mathlib

set_option autoImplicit false

open scoped ComplexOrder

namespace CompNonlocal

/-- Effects. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19: "An effect on a Hilbert space H is a Hermitian operator
E : H → H satisfying 0 ≤ E ≤ I". -/
def IsEffect {ι : Type} [Fintype ι] [DecidableEq ι] (E : Matrix ι ι ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

end CompNonlocal


