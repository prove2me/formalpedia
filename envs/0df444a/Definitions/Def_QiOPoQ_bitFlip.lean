-- Prove2me | Definitions.Def_QiOPoQ_bitFlip
-- name    : QiOPoQ_bitFlip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:11.470322+00:00
-- url     : https://prove2.me/theorems/b88a8e1d-a390-4cf8-9917-bf30f316d5e7
-- title:
--   The bit-flip channel $X^b(\cdot)$
-- statement:
--   The one-qubit channel $X^b(\cdot):\rho\mapsto X^b\rho X^b$ for a bit $b$, where $X^0=I$ and $X^1=X$. For $b=0$ this is the identity channel $I(\cdot)$ and for $b=1$ it is $X(\cdot)$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13 and Lemma 4.4, p.18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms

/-- The one-qubit matrix `X^b` (`X^0 = I`, `X^1 = X`). -/
def xPow (b : Bool) : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ :=
  Matrix.of fun y y' => if y 0 = (y' 0 ^^ b) then 1 else 0

/-- The channel `X^b(·) : ρ ↦ X^b ρ X^b` on one qubit (p.13, the class C_BQP; p.18, "the channels
I(·) and X(·)"). -/
def bitFlip (b : Bool) : Superop (Fin 1 → Bool) (Fin 1 → Bool) :=
  fun ρ => xPow b * ρ * (xPow b).conjTranspose

end QiOPoQ


