-- Prove2me | Definitions.Def_LindbladStructLearn_oneEigenProj
-- name    : LindbladStructLearn_oneEigenProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:47.267006+00:00
-- url     : https://prove2.me/theorems/541136bb-68d0-4716-883e-ac984f1425f1
-- title:
--   Single-qubit Pauli eigenstate projector $|P,b\rangle\langle P,b|$
-- statement:
--   For $P \in \{X,Y,Z\}$ and $b \in \{\pm1\}$, $|P,b\rangle\langle P,b| = (I + bP)/2$ is the projector onto the eigenvector of $P$ with eigenvalue $b$; for $P = I$ the paper sets $|I,+1\rangle = |0\rangle$ and $|I,-1\rangle = |1\rangle$, the $Z$ projectors.
--
--   **Formalization Note** $b$ is a Boolean: `false` is $+1$, `true` is $-1$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.2, p.16

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Single-qubit Pauli eigenstate projector (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.2, p.16): `|P,b⟩⟨P,b| = (I + bP)/2` for
`P ∈ {X,Y,Z}`, and `|I,+1⟩ = |0⟩`, `|I,−1⟩ = |1⟩` (the `Z` projectors).

**Formalization Note** The eigenvalue `b ∈ {±1}` is a `Bool`: `false = +1`, `true = −1`
(so for `I`, `false` is `|0⟩`). -/
def oneEigenProj (a : Fin 4) (b : Bool) : Op Bool :=
  (1 / 2 : ℂ) • (1 + (if b then (-1 : ℂ) else 1) • onePauli (if a = 0 then 3 else a))

end LindbladStructLearn


