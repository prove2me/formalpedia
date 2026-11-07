-- Prove2me | Definitions.Def_SigmoidWire_bitR
-- name    : SigmoidWire_bitR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:14.230307+00:00
-- url     : https://prove2.me/theorems/d1ed7af6-f2cf-491e-aaa8-eee9344aacf7
-- title:
--   Boolean bits as the reals $0$ and $1$, and the cube point of $x\in\{0,1\}^n$
-- statement:
--   A bit $b\in\{0,1\}$, represented in Lean as a Boolean value, is read as the real number $0$ or $1$. A point $x\in\{0,1\}^n$ is correspondingly read as the real vector with these coordinates.
--
--   These two conversions are what let a weight multiply an input bit and a real polynomial be evaluated at a point of the cube.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), §3 Notation, p.14

import Mathlib

namespace SigmoidWire

/-- **Boolean bits as reals**: `true ↦ 1`, `false ↦ 0`.

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), §3 Notation, p.14 (PDF p.16):
inputs `x ∈ {0,1}^n`.

**Formalization Note.** A point of `{0,1}^n` is a function `Fin n → Bool`; it is read as the real
vector with entries `0` and `1` wherever a weight multiplies it or a polynomial is evaluated at it. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- **The point of `ℝ^n` underlying `x ∈ {0,1}^n`** (coordinates `0` and `1`), §3, p.14 (Li,
Reichman, Williams, Wu, STOC 2027 submission). -/
def cubePt {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ := fun i => bitR (x i)

end SigmoidWire


