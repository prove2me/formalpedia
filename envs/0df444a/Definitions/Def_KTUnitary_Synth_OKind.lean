-- Prove2me | Definitions.Def_KTUnitary_Synth_OKind
-- name    : KTUnitary_Synth_OKind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:22.743352+00:00
-- url     : https://prove2.me/theorems/b5e04795-9531-496a-bf7c-b59d251ed1a2
-- title:
--   The four oracle homomorphisms
-- statement:
--   An $\mathcal O$-oracle unitary circuit may use the oracle gates $O_n,\ O_n^*,\ O_n^\dagger,\ O_n^T$ and their controlled versions. `OKind` names the four homomorphisms (identity, entrywise complex conjugate, adjoint, transpose); `OKind.act` applies one to a matrix and `OKind.code` is its two-bit label in circuit descriptions.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.5, p. 17

import Mathlib

namespace KTUnitary.Synth

/-- **The four oracle homomorphisms** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.5, p. 17): an `𝒪`-oracle unitary
circuit may contain oracle gates from `{O_n, O_n^*, O_n^†, O_n^T, cO_n, cO_n^*, cO_n^†, cO_n^T}`.
`OKind` is the choice among `O_n`, `O_n^*` (entrywise complex conjugate), `O_n^†` (adjoint) and
`O_n^T` (transpose); a controlled gate is a separate gate constructor. -/
inductive OKind
  | plain
  | conj
  | adj
  | transp
  deriving DecidableEq

/-- The matrix of the oracle homomorphism `κ` applied to `A`: `A`, `A^*`, `A^†` or `A^T`. -/
def OKind.act {ι : Type} (κ : OKind) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  match κ with
  | .plain => A
  | .conj => A.map star
  | .adj => A.conjTranspose
  | .transp => A.transpose

/-- The two-bit code of `κ`, used in gate descriptions. -/
def OKind.code : OKind → List Bool
  | .plain => [false, false]
  | .conj => [false, true]
  | .adj => [true, false]
  | .transp => [true, true]

end KTUnitary.Synth


