-- Prove2me | Definitions.Def_LindbladStructLearn_letterPhase
-- name    : LindbladStructLearn_letterPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:54.871144+00:00
-- url     : https://prove2.me/theorems/1a357276-f055-49a7-bbe3-14a4719d3cea
-- title:
--   Phase of a product of single-qubit Pauli letters
-- statement:
--   For single-qubit Pauli letters $a, b \in \{I,X,Y,Z\}$, `letterPhase a b` is the scalar $c(\sigma_a\sigma_b) \in \{\pm1, \pm i\}$ with $\sigma_a\sigma_b = c(\sigma_a\sigma_b)\,\mathcal P(\sigma_a\sigma_b)$; e.g. $XY = iZ$, $YZ = iX$, $ZX = iY$, and the phase is $1$ when the letters commute.
--
--   The $n$-qubit phase $c(PQ)$ is the product of these over the sites.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Phase of a product of single-qubit Pauli letters (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13): `c(σ_a σ_b)`,
so that `σ_a σ_b = letterPhase a b • σ_(letterMul a b)` (`XY = iZ`, `YZ = iX`, `ZX = iY`).

**Formalization Note** Letters `0 = I, 1 = X, 2 = Y, 3 = Z`. -/
def letterPhase : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, Complex.I, -Complex.I], ![1, -Complex.I, 1, Complex.I],
    ![1, Complex.I, -Complex.I, 1]]

end LindbladStructLearn


