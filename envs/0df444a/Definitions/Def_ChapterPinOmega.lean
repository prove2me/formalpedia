-- Prove2me | Definitions.Def_ChapterPinOmega
-- name    : ChapterPinOmega
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:28:34.167982+00:00
-- url     : https://prove2.me/theorems/7ced3839-f3a4-4a24-8dbf-19edbf58dcdd
-- title:
--   Chapter PinOmega
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPinOmega.lean`): generated def bundle for ChapterPinOmega. See BookProof/ChapterPinOmega.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPinOmega.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"On the Lorentz, SL(2,C) and Pin(3,1) groups", Definition 49 — the discrete Pin
subgroup `Ω` is the quaternion group `Q₈`

`book.tex` (Definition 49, line ~5510) introduces the discrete `Pin(3,1)` subgroup

```
Ω = { ±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵ }
```

and asserts (via the two-to-one cover `Λ`) that it is a group of order `8` — the
double cover of the Klein-four discrete Lorentz subgroup `Δ`.  This file pins
down the algebraic heart of that assertion using the concrete `4×4` real
Majorana / Dirac matrix model of `BookProof.ChapterA3`:

* the three "imaginary units" are
  `qi = iγ⁰ = ` (Majorana matrix `iγ⁰`), `qj = γ⁰γ⁵`, `qk = iγ⁵`;
* they satisfy the **quaternion relations** `qi² = qj² = qk² = -1`,
  `qi·qj = qk`, `qj·qk = qi`, `qk·qi = qj` (and the anti-commuted forms), and
  `qi·qj·qk = -1` — i.e. `Ω ≅ Q₈`, the quaternion group of order 8;
* the eight-element set `Ω` is **closed under multiplication**, contains `1` and
  the inverses of all its elements, and is **nonabelian** — so it is a group of
  order `8`.

Everything is carried out first over `ℤ` (where the identities are decidable) and
then transported to the complex model `mgamma`/`mgamma5`.  The identification of
`qj` with `γ⁰γ⁵` in the book's normalization (`γ^μ = -i·(iγ^μ)`) is recorded in
`qjC_eq_dirac`.

The surrounding claim that `Λ` maps `Ω` onto `Δ` (so `Ω` is the double cover of
`Δ`) is the continuous-cover statement of the note and is left as prose; here we
discharge the finite group-theoretic core.

As requested this stays **off the gravity line** and **off the Hankel-transform
line** (it uses only the concrete Majorana/Dirac matrices, no spherical-Bessel /
Hankel numerics).

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterPinOmega

open BookProof.ChapterA3

/-! ## Integer model of the three quaternion generators -/

/-- `qi = iγ⁰` (the first Majorana matrix), integer model. -/
def qi : Matrix (Fin 4) (Fin 4) ℤ := mgammaZ 0

/-- `qj = γ⁰γ⁵ = -(iγ⁰)(iγ⁵)`, integer model.  (In the book's normalization
`γ^μ = -i(iγ^μ)`, so `γ⁰γ⁵ = (-i)(-i)(iγ⁰)(iγ⁵) = -(iγ⁰)(iγ⁵)`.) -/
def qj : Matrix (Fin 4) (Fin 4) ℤ := -(mgammaZ 0 * mgamma5Z)

/-- `qk = iγ⁵` (the fifth Majorana matrix), integer model. -/
def qk : Matrix (Fin 4) (Fin 4) ℤ := mgamma5Z

/-! ### The quaternion relations (over `ℤ`) -/

















/-! ## The eight-element group `Ω` (over `ℤ`) -/

/-- The discrete Pin subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` (integer model). -/
def Omega : Finset (Matrix (Fin 4) (Fin 4) ℤ) := {1, -1, qi, -qi, qj, -qj, qk, -qk}











/-! ## Complex model: identification with the book's `iγ⁰, γ⁰γ⁵, iγ⁵` -/

/-- `qi = iγ⁰` in the complex model. -/
noncomputable def qiC : Matrix (Fin 4) (Fin 4) ℂ := mgamma 0

/-- `qj = γ⁰γ⁵ = -(iγ⁰)(iγ⁵)` in the complex model. -/
noncomputable def qjC : Matrix (Fin 4) (Fin 4) ℂ := -(mgamma 0 * mgamma5)

/-- `qk = iγ⁵` in the complex model. -/
noncomputable def qkC : Matrix (Fin 4) (Fin 4) ℂ := mgamma5









/-! ### The quaternion relations transported to the complex model -/



















end BookProof.ChapterPinOmega


