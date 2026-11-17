-- Prove2me | Definitions.Def_DesignTest_Supplement_weylSet
-- name    : DesignTest_Supplement_weylSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:07:08.021681+00:00
-- url     : https://prove2.me/theorems/8fea6eb6-1e87-4581-b41c-fb71e2ae4fe2
-- title:
--   Weyl matrices $X^aZ^b$ up to phase
-- statement:
--   On $\mathbb C^d$ with basis $|0\rangle,\dots,|d-1\rangle$ let $X|k\rangle=|k+1\bmod d\rangle$ and $Z|k\rangle=e^{2\pi ik/d}|k\rangle$. The **Weyl operators** are $W_d=\{X^aZ^b: a,b\in\{0,\dots,d-1\}\}$. The set used here contains every unitary equal to some $X^aZ^b$ up to a global phase.
--
--   It is the known support of Theorem 5.12.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §5.3, p.59; Theorem 5.12, p.65

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open RandomGateDesign.MasterBound

/-- The **shift** `X|k⟩ = |k + 1 mod d⟩` on `ℂ^d` (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and
Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), §5.3, p.59; Theorem 5.12, p.65): entry
`(i, j)` is `1` iff `i = j + 1 mod d`. Basis labels are `Fin d = {0, …, d − 1}`. -/
def weylX (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = ((j : ℕ) + 1) % d then 1 else 0

/-- The **clock** `Z|k⟩ = e^{2πik/d}|k⟩` on `ℂ^d` (STOC 2027 submission (sha256 e2f0a429…), §5.3, p.59). -/
noncomputable def weylZ (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun k : Fin d =>
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (d : ℂ))

/-- The unitaries that are, **up to global phase, one of the Weyl matrices** `X^a Z^b`,
`a, b ∈ {0, …, d − 1}` (STOC 2027 submission (sha256 e2f0a429…), §5.3, p.59: `W_d`; Theorem 5.12,
p.65). -/
def weylUpToPhase (d : ℕ) : Set (U d) :=
  {V | ∃ a b : Fin d, PhaseEq (V : Matrix (Fin d) (Fin d) ℂ) (weylX d ^ (a : ℕ) * weylZ d ^ (b : ℕ))}

end DesignTest.Supplement


