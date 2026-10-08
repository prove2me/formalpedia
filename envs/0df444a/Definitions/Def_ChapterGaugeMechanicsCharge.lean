-- Prove2me | Definitions.Def_ChapterGaugeMechanicsCharge
-- name    : ChapterGaugeMechanicsCharge
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:39:04.936989+00:00
-- url     : https://prove2.me/theorems/0ee19680-1338-49cb-9041-554b12887718
-- title:
--   Chapter GaugeMechanicsCharge
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaugeMechanicsCharge.lean`): generated def bundle for ChapterGaugeMechanicsCharge. See BookProof/ChapterGaugeMechanicsCharge.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeMechanicsCharge.lean

import Definitions.Def_ChapterG
import Mathlib

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/

/-!
# The gauge-mechanics model: charge operator, BRST charge and the gauge-invariant algebra

Source: `book.tex`, §*"Quantization of a classical Gauge Mechanics system"*
(lines 2402–2455) of the chapter *"Gauge symmetry and dissipative dynamics in
probability spaces"*, repeated for the field-theoretic model at line 7080.
The manuscript's model has Hilbert space `L²(ℝ² × ℤ₂)` — one complex field
`φ` and one ghost degree of freedom `k ∈ {0,1}` — with

```
[φ, π] = i,      [φ, π*] = 0,      {ψ, ψ†} = 1,
Q = π φ + π* φ*        (the gauge generator / charge operator),
Ω = (π φ + π* φ*) ψ†   (the BRST charge).
```

The book then argues that the gauge-invariant algebra must commute with `Q`
while `Q` itself, and the conjugate fields `π, π*`, must be *excluded* from it —
"this is guaranteed by unconstrained gauge-fixing" — because they do not commute
with the fields `φ, φ*` generating the commutative von Neumann algebra.

This file realizes the model on the polynomial core `ℂ[φ, φ*]` of `L²(ℝ²)`
(coordinate `0` is `φ`, coordinate `1` is `φ*`), with `π_j = -i ∂_j`, and proves
the algebraic statements the manuscript makes about it.

## Main results

* `ccr_phi_pi`, `ccr_phi_piStar` — the canonical commutation relations
  `[φ, π] = i` and `[φ, π*] = 0` exactly as displayed in the book.
* `chargeQ_eq_euler` — the charge operator is `Q = -i (E + 2)` with `E` the
  Euler (degree) operator: `Q` is diagonal in the field degree.
* `chargeQ_homogeneous` — on a field configuration homogeneous of degree `n`,
  `Q p = -i (n + 2) p`.
* `chargeQ_not_commute_field` — `[Q, φ] = -i φ`: the gauge generator does
  **not** commute with the fields, i.e. it is excluded from the commutative
  von Neumann algebra they generate — the book's *unconstrained* gauge fixing.
* `mul_commutes_chargeQ_iff_euler_zero` — multiplication by a polynomial `g`
  commutes with `Q` **iff** `E g = 0`: no charged function of the fields is
  gauge invariant.
* `bilinear_commutes_chargeQ` — the degree-preserving bilinears `φ_j ∂_k` *do*
  commute with `Q`: these are gauge-invariant observables of the model.
* `brst_nilpotent`, `brst_ne_zero`, `ghost_car` — the BRST charge `Ω = Q ψ†` of
  the model is nilpotent and non-zero, with the ghost canonical anticommutation
  relation `{ψ, ψ†} = 1` (reusing the ghost algebra of `BookProof.ChapterG`).
-/

namespace BookProof.ChapterGaugeMechanicsCharge

open MvPolynomial

/-- The polynomial core `ℂ[φ, φ*]` of `L²(ℝ²)`: coordinate `0` is the field
`φ`, coordinate `1` is its conjugate `φ*`. -/
abbrev P : Type := MvPolynomial (Fin 2) ℂ

/-- The derivative operator `∂_j` as an endomorphism of the core. -/
noncomputable def derOp (j : Fin 2) : Module.End ℂ P := (pderiv j).toLinearMap

/-- Multiplication by the field coordinate: the operator `φ` (for `j = 0`) and
`φ*` (for `j = 1`). -/
noncomputable def fieldOp (j : Fin 2) : Module.End ℂ P := LinearMap.mulLeft ℂ (X j)

/-- The conjugate momentum `π_j = -i ∂_j` (`π` for `j = 0`, `π*` for `j = 1`). -/
noncomputable def momOp (j : Fin 2) : Module.End ℂ P := (-Complex.I) • derOp j

@[simp] theorem fieldOp_apply (j : Fin 2) (p : P) : fieldOp j p = X j * p := rfl

@[simp] theorem momOp_apply (j : Fin 2) (p : P) :
    momOp j p = (-Complex.I) • pderiv j p := rfl



/-! ## The canonical commutation relations -/





/-! ## The charge operator `Q = π φ + π* φ*` -/

/-- The Euler (degree) operator `E = φ ∂_φ + φ* ∂_{φ*}`. -/
noncomputable def eulerOp : Module.End ℂ P :=
  (fieldOp 0).comp (derOp 0) + (fieldOp 1).comp (derOp 1)

@[simp] theorem eulerOp_apply (p : P) :
    eulerOp p = X 0 * pderiv 0 p + X 1 * pderiv 1 p := rfl

/-- **The gauge generator of the model**, the charge operator
`Q = π φ + π* φ*` (book 2432). -/
noncomputable def chargeQ : Module.End ℂ P :=
  (momOp 0).comp (fieldOp 0) + (momOp 1).comp (fieldOp 1)





/-! ## The gauge generator is excluded from the algebra of the fields -/











/-! ## The gauge-invariant bilinears -/





/-! ## The ghost sector and the BRST charge -/

/-- The BRST charge `Ω = Q ψ†` of the gauge-mechanics model, in the `ℤ₂` ghost
representation of `BookProof.ChapterG`. -/
noncomputable def brstOmega : Matrix (Fin 2) (Fin 2) (Module.End ℂ P) :=
  ChapterG.BRST chargeQ









end BookProof.ChapterGaugeMechanicsCharge


