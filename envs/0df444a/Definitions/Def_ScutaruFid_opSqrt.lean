-- Prove2me | Definitions.Def_ScutaruFid_opSqrt
-- name    : ScutaruFid_opSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:07.223117+00:00
-- url     : https://prove2.me/theorems/0bb361e6-7305-40fc-8707-cf6dd253280b
-- title:
--   Positive square root $\sqrt T$ of an operator
-- statement:
--   For a bounded operator $T$ on a complex Hilbert space $H$, $\sqrt T$ denotes the square root given by the continuous functional calculus. When $T$ is positive, $\sqrt T$ is the unique positive operator with
--
--   $$
--   \sqrt T\,\sqrt T=T .
--   $$
--
--   This is the square root in Uhlmann's fidelity (1) and the operator $\sqrt\rho$ of the paper's rule R2 (eqs. (6)–(9)).
--
--   **Formalization Note** Mathlib's `CFC.sqrt` on the C*-algebra `H →L[ℂ] H`, declared once for a general complex Hilbert space $H$ (on $L^2(\mathbb R)$ Mathlib's separate real-module structure of `Lp` would otherwise block instance search). On a non-positive operator the value is a junk value; the mission applies it only to positive operators.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (1), p.1, and p.2 before (6) ("We shall define the operator √ρ")

import Mathlib

namespace ScutaruFid

/-- **Positive square root of a bounded operator.** Scutaru, arXiv:quant-ph/9708013v1, eq. (1),
p.1 (the factors `√ρ1` in "F(ρ1, ρ2) = [trace(√ρ1 ρ2 √ρ1)^{1/2}]²") and p.2, before (6): "We
shall define the operator √ρ".

For a bounded operator `T` on a complex Hilbert space `H`, `opSqrt T` is the square root of `T`
given by the continuous functional calculus; when `T` is positive it is the unique positive
operator whose square is `T`.

**Formalization Note** This is Mathlib's `CFC.sqrt` on the C*-algebra `H →L[ℂ] H`, declared for a
general complex Hilbert space `H`. Writing it once for a general `H` makes the functional calculus
use the real structure induced by the complex one; on `L²(ℝ)` Mathlib's separate real-module
instance of `Lp` would otherwise block instance search. On a non-positive operator the value is
Mathlib's junk value; the mission only applies it to positive operators. -/
noncomputable def opSqrt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt T

end ScutaruFid


