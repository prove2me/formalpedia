-- Prove2me | Definitions.Def_QSampVerif_updateCZ
-- name    : QSampVerif_updateCZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:17.721106+00:00
-- url     : https://prove2.me/theorems/a4b800a9-1b71-4479-969b-8566cc703592
-- title:
--   The key-update map $\mathrm{updateCZ}$ (Definition 4.1) and the one-time pad $X^xT^t$
-- statement:
--   With $X$-exponents modulo 2 and $T$-exponents modulo 8,
--
--   $$\mathrm{updateCZ}(x_1,t_1,x_2,t_2)=(x_1,\ t_1+4x_2,\ x_2,\ t_2+4x_1).\qquad(43)$$
--
--   The one-time pad with keys $(x,t)$ is the one-qubit operator $X^xT^t$, $T=\mathrm{diag}(1,e^{i\pi/4})$.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Definition 4.1, (43), p.25 (PDF 26)

import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Definition 4.1, (43), p.25 (PDF 26):
`updateCZ(x₁, t₁, x₂, t₂) = (x₁, t₁ + 4x₂, x₂, t₂ + 4x₁)`. "All X-exponents are interpreted
modulo 2, and all T-exponents modulo 8" (p.25), so `x ∈ ZMod 2` and `t ∈ ZMod 8`. -/
def updateCZ (x₁ : ZMod 2) (t₁ : ZMod 8) (x₂ : ZMod 2) (t₂ : ZMod 8) :
    ZMod 2 × ZMod 8 × ZMod 2 × ZMod 8 :=
  (x₁, t₁ + 4 * ((x₂.val : ℕ) : ZMod 8), x₂, t₂ + 4 * ((x₁.val : ℕ) : ZMod 8))

/-- The one-time pad `X^x T^t` on one qubit (p.25), with the published `pauliX` and `gateT`;
the exponents are the representatives `x.val ∈ {0, 1}` and `t.val ∈ {0, …, 7}`. -/
noncomputable def padXT (x : ZMod 2) (t : ZMod 8) : Matrix Bool Bool ℂ :=
  pauliX ^ x.val * gateT ^ t.val

end QSampVerif


