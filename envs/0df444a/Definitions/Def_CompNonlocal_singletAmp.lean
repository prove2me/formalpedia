-- Prove2me | Definitions.Def_CompNonlocal_singletAmp
-- name    : CompNonlocal_singletAmp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:44.323385+00:00
-- url     : https://prove2.me/theorems/611d9e3d-9ac7-4b00-8196-584568b73d17
-- title:
--   Amplitudes of the singlet $|\psi^-\rangle$
-- statement:
--   The singlet state
--   $$|\psi^-\rangle=\frac{|01\rangle-|10\rangle}{\sqrt2}$$
--   as an amplitude vector on two qubits, Alice's qubit first: amplitude $1/\sqrt2$ at $|01\rangle$, $-1/\sqrt2$ at $|10\rangle$, $0$ elsewhere.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19

import Mathlib

set_option autoImplicit false

namespace CompNonlocal

/-- The amplitudes of the singlet state. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19: "The following state is called the
singlet state ψ⁻ = (|01⟩ − |10⟩)/√2".

**Formalization Note** The two-qubit basis is `Bool × Bool`, Alice's qubit first, `false = |0⟩`;
so `ψ⁻(false, true) = 1/√2`, `ψ⁻(true, false) = −1/√2` and the other amplitudes vanish. -/
noncomputable def singletAmp (p : Bool × Bool) : ℂ :=
  if p = (false, true) then ((Real.sqrt 2)⁻¹ : ℝ)
  else if p = (true, false) then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

end CompNonlocal


