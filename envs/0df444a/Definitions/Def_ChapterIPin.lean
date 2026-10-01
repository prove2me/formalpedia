-- Prove2me | Definitions.Def_ChapterIPin
-- name    : ChapterIPin
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:03:30.585407+00:00
-- url     : https://prove2.me/theorems/7c2bfe06-6962-480f-b239-864271131c13
-- title:
--   Chapter IPin
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterIPin.lean`): generated def bundle for ChapterIPin. See BookProof/ChapterIPin.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterIPin.lean

import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"Real unitary representations of the Poincaré group", **Definition 77** (the `IPin(3,1)`
/ Poincaré group as a semidirect product)

`book.tex` (§"Real unitary representations of the Poincaré group", line ~6144):

> **Definition 77.** The `IPin(3,1)` group is defined as the semi-direct product
> `Pin(3,1) ⋉ ℝ⁴`, with the group's product defined as
> `(A,a)(B,b) = (A B, a + Λ(A) b)`, for `A,B ∈ Pin(3,1)` and `a,b ∈ ℝ⁴` and
> `Λ(A)` is the Lorentz transformation corresponding to `A`.

We formalize the **group-theoretic content**, which needs only:

* an abstract group `P` (the role of `Pin(3,1)` / `SL(2,ℂ)`),
* the translation module `V` (the role of `ℝ⁴`, any `AddCommGroup`),
* the linear action `Λ : P →* Multiplicative (AddAut V)` (`Λ(A)` is the additive
  automorphism of `V` given by the Lorentz transformation attached to `A`,
  transported to the multiplicative type tag so that it forms a monoid hom).

The Poincaré group `IPin` is then the Mathlib **semidirect product**
`Multiplicative V ⋊[φ] P`, where `φ : P →* MulAut (Multiplicative V)` is the action
`Λ` transported through the `Multiplicative` type-tag (`Multiplicative.toAdd`
followed by `AddEquiv.toMultiplicative`).
An element is a pair with `left : Multiplicative V` (the translation `a`, as
`toAdd left : V`) and `right : P` (the group element `A`).  The two headline lemmas
reproduce the book's product formula `(A,a)(B,b) = (A B, a + Λ(A) b)`:

* `ipin_right` — the `P` component multiplies: `(x·y).right = x.right · y.right`
  (i.e. `A B`);
* `ipin_left` — the translation component twists by `Λ`:
  `toAdd (x·y).left = toAdd x.left + toAdd (Λ x.right) (toAdd y.left)`
  (i.e. `a + Λ(A) b`).

The restriction to `ISL(2,ℂ)` (Definition 77's second paragraph) is the same
construction with `P` restricted to `Spin⁺(1,3)`; that restriction and the concrete
`Pin(3,1)`/`ℝ⁴` model are left as prose, matching the roadmap constraints (off the
gravity line, off the Hankel-transform line).

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterIPin

open Multiplicative

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

/-- The semidirect-product action `φ : P →* MulAut (Multiplicative V)` obtained from
the Lorentz action `Λ : P →* Multiplicative (AddAut V)` by transport through the
`Multiplicative` type-tag (`Multiplicative.toAdd` + `AddEquiv.toMultiplicative`). -/
noncomputable def phiHom : P →* MulAut (Multiplicative V) where
  toFun p := (Multiplicative.toAdd (Λ p)).toMultiplicative
  map_one' := by
    ext v
    show Multiplicative.ofAdd (Multiplicative.toAdd (Λ 1) (toAdd v)) = v
    simp [map_one]
  map_mul' p q := by
    ext v
    show Multiplicative.ofAdd (Multiplicative.toAdd (Λ (p * q)) (toAdd v))
        = Multiplicative.ofAdd (Multiplicative.toAdd (Λ p)
            (Multiplicative.toAdd (Λ q) (toAdd v)))
    simp [map_mul]

/-- **Definition 77.** The `IPin(3,1)` / Poincaré group `Pin(3,1) ⋉ ℝ⁴`, formalized as
the semidirect product `Multiplicative V ⋊[φ] P`. -/
noncomputable def IPin (_Λ : P →* Multiplicative (AddAut V)) : Type _ :=
  Multiplicative V ⋊[phiHom _Λ] P

noncomputable instance (Λ : P →* Multiplicative (AddAut V)) : Group (IPin Λ) :=
  SemidirectProduct.instGroup





end BookProof.ChapterIPin


