-- Prove2me | Definitions.Def_CompNonlocal_singlet
-- name    : CompNonlocal_singlet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:33.07348+00:00
-- url     : https://prove2.me/theorems/ecd149ad-e5a0-4b60-813d-726259aa4a86
-- title:
--   The singlet projector $|\psi^-\rangle\langle\psi^-|$
-- statement:
--   The rank-one projector $|\psi^-\rangle\langle\psi^-|$ onto the singlet, a $4\times4$ matrix on $\mathbb C^2\otimes\mathbb C^2$ with Alice's qubit as the first factor.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19 and Definition 1, p.19

import Mathlib
import Definitions.Def_CompNonlocal_singletAmp

set_option autoImplicit false

namespace CompNonlocal

/-- The singlet projector `|ψ⁻⟩⟨ψ⁻|` on `C² ⊗ C²`. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19 (singlet state) and
Definition 1, p.19, Eq. (4).

**Formalization Note** Entry `(p, p')` is `ψ⁻(p) · conj(ψ⁻(p'))`; Alice's qubit is the first factor. -/
noncomputable def singlet : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p p' => singletAmp p * star (singletAmp p')

end CompNonlocal


