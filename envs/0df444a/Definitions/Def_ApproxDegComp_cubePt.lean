-- Prove2me | Definitions.Def_ApproxDegComp_cubePt
-- name    : ApproxDegComp_cubePt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:46.664359+00:00
-- url     : https://prove2.me/theorems/dd0b94b4-4f8a-4fa2-9e96-c5db70daeb42
-- title:
--   Points of the Boolean cube $\{0,1\}^n\subseteq\mathbb R^n$
-- statement:
--   A Boolean value is read as a real number by $\mathrm{true}\mapsto 1$ and $\mathrm{false}\mapsto 0$. For a finite index set $\iota$ (the paper's $[n]$), an input $x\in\{0,1\}^\iota$ is the point of $\mathbb R^\iota$ whose $i$-th coordinate is the real value of $x_i$. Polynomials are compared with Boolean functions at these 0/1 points.
--
--   **Formalization Note** $\{0,1\}^n$ is `ι → Bool` over a finite type; the points are 0/1 points, never $\pm1$ points.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), §2.1–2.2, pp.10–11, Definition 2

import Mathlib

namespace ApproxDegComp

/-- **Boolean values as reals and points of the Boolean cube** (§2.1–2.2, pp.10–11).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 2, p.11: Boolean functions are `f : {0, 1}ⁿ → {0, 1}` and a polynomial
`p : ℝⁿ → ℝ` is compared with `f` "for every x ∈ {0, 1}ⁿ".

`boolToReal` sends `true ↦ 1` and `false ↦ 0`; `cubePt x` is the point of `{0,1}^ι ⊆ ℝ^ι`
whose `i`-th coordinate is `boolToReal (x i)`.

**Formalization Note** `{0,1}ⁿ` is `ι → Bool` over a finite index type `ι`, with
`true ↦ 1`, `false ↦ 0`; the cube points are 0/1 points, never ±1 points. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

/-- The point of `{0,1}^ι ⊆ ℝ^ι` represented by `x : ι → Bool` (`true ↦ 1`, `false ↦ 0`). -/
def cubePt {ι : Type} (x : ι → Bool) : ι → ℝ := fun i => boolToReal (x i)

@[simp] theorem boolToReal_true : boolToReal true = 1 := rfl
@[simp] theorem boolToReal_false : boolToReal false = 0 := rfl

end ApproxDegComp


