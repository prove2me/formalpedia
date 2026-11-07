-- Prove2me | Definitions.Def_FixpReciprocal_toBasicData
-- name    : FixpReciprocal_toBasicData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:47.375211+00:00
-- url     : https://prove2.me/theorems/2c6fabc7-daf6-4da8-97f4-42bfc735e20f
-- title:
--   The basic FIXP data $([0,1]^N,F_{\mathcal C})$
-- statement:
--   This is the data of the basic FIXP instance of the membership proof: the cube $[0,1]^N$, written by the $2N$ rows $x_i\le1$ and $-x_i\le0$, and an algebraic circuit for $F_{\mathcal C}$. A clipped affine gate compiles to the $11$ operations computing $\min\{1,\max\{ax_j+bx_k+c,0\}\}$, and a reciprocal gate to the $5$ operations computing $1/(1+\tau x_j)$. Wires are numbered consecutively after the $N$ inputs.
--
--   **Formalization Note** The compilation is explicit so that "a polynomial-size algebraic circuit" can be stated about it. That the result is an instance of Definition 3.1 is a clause of the milestone `FixpReciprocal.circuitMap_spec`, not of this definition, because it needs $\tau>0$.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_basicFIXP
import Definitions.Def_FixpReciprocal_RGate

namespace FixpReciprocal

/-- The row with entry `s` at position `i` and zeros elsewhere, of length `N`. -/
def unitRow (N i : ℕ) (s : ℚ) : List ℚ := (List.range N).map fun k => if k = i then s else 0

/-- The rows of the cube: `x_i ≤ 1` and `−x_i ≤ 0`. -/
def cubeRows (N : ℕ) : List (List ℚ × ℚ) :=
  (List.range N).flatMap fun i => [(unitRow N i 1, 1), (unitRow N i (-1), 0)]

/-- The operations computing a gate, with `base` the first new wire. For `aff`: `⟦a x_j + b x_k + c⟧ =
min{1, max{a x_j + b x_k + c, 0}}`, output at `base + 10`. For `recip`: `1 / (1 + τ x_j)`, output at `base + 4`. -/
def gateOps (τ : ℚ) (base : ℕ) : RGate → List AlgOp
  | .aff a b c j k =>
    [.const a, .mul base j, .const b, .mul (base + 2) k, .add (base + 1) (base + 3), .const c,
     .add (base + 4) (base + 5), .const 0, .max (base + 6) (base + 7), .const 1,
     .min (base + 9) (base + 8)]
  | .recip j =>
    [.const 1, .const τ, .mul (base + 1) j, .add base (base + 2), .div base (base + 3)]

/-- The operations and output wires of a list of gates. -/
def compileGates (τ : ℚ) : ℕ → List RGate → List AlgOp × List ℕ
  | _, [] => ([], [])
  | base, g :: gs =>
    let n := (gateOps τ base g).length
    let r := compileGates τ (base + n) gs
    (gateOps τ base g ++ r.1, (base + n - 1) :: r.2)

/-- **The basic FIXP data `([0, 1]^N, F_C)` of the proof of Theorem 4.2.**

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12: "`F_C` is a continuous self-map represented by a polynomial-size
algebraic circuit." -/
def toBasicData (τ : ℚ) (C : List RGate) : BasicData where
  rows := cubeRows C.length
  circ :=
    { n := C.length
      ops := (compileGates τ C.length C).1
      out := (compileGates τ C.length C).2 }

end FixpReciprocal


