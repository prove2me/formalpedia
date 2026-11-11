-- Prove2me | Definitions.Def_SpacePropTest_Cube
-- name    : SpacePropTest_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:52.423545+00:00
-- url     : https://prove2.me/theorems/5241e80c-13f2-4dcc-aa68-481990194272
-- title:
--   The Boolean cube $\{0,1\}^n$, distance $d(f,g)$, $\varepsilon$-far, monotone functions, bits $\lceil\log_2 M\rceil$
-- statement:
--   The **Boolean cube** $\{0,1\}^n$ carries the coordinatewise order: $x\preceq y$ iff $x_i\le y_i$ for all $i\in[n]$. For Boolean functions $f,g:\{0,1\}^n\to\{0,1\}$ the **distance** is
--
--   $$d(f,g)=\frac{|\{x\in\{0,1\}^n: f(x)\ne g(x)\}|}{2^n}.$$
--
--   1. A **property** is a set $\mathcal P$ of Boolean functions; $g$ is **$\varepsilon$-far from $\mathcal P$** if $d(f,g)\ge\varepsilon$ for every $f\in\mathcal P$, i.e. $d(g,\mathcal P)=\min_{f\in\mathcal P}d(f,g)\ge\varepsilon$ when $\mathcal P$ is non-empty.
--   2. $f$ is **monotone** (Definition 2) if $f(x)\le f(y)$ whenever $x\preceq y$; $\mathsf{Mon}$ is the set of monotone functions.
--   3. An algorithm with $M$ states uses $m=\lceil\log_2 M\rceil$ **bits** of memory.
--
--   These are the standing objects of the paper's testing problems.
--
--   **Formalization Note** Points are `Fin n → Bool` with the product order (`false < true`). "$\varepsilon$-far" is stated as $d(f,g)\ge\varepsilon$ for all $f\in\mathcal P$, which is the paper's "ε-far from every $f\in\mathcal P$" (p.16) and equals $d(g,\mathcal P)\ge\varepsilon$ for a non-empty finite property. Bits are `Nat.clog 2 M`.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), §3, p.14 (PDF 16); Definition 2, p.14 (PDF 16); §4.1, p.16 (PDF 18)

import Mathlib

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

/-- **The Boolean cube, distance, ε-far, monotonicity, bits** (C. Canonne, X. Chen, W. Pires,
T. Pitassi, R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2,
2026, sha256 65850aa6…; §3, p.14 (PDF 16), Definition 2, p.14; §4.1, p.16 (PDF 18)).

`Cube n` is `{0,1}ⁿ` as `Fin n → Bool` (`false` = 0, `true` = 1) with the coordinatewise
(product) order, so `x ≤ y` is the paper's `x ⪯ y`.

**Formalization Note.** A property is a `Set (BoolFn n)`; the paper's standing non-emptiness of a
property is stated where it is needed. "ε-far from every `f ∈ P`" is `IsFar P g ε`, i.e.
`ε ≤ d(f, g)` for every `f ∈ P`; for a non-empty finite `P` this is `d(g, P) = min_{f∈P} d(f,g) ≥ ε`. -/
abbrev Cube (n : ℕ) : Type := Fin n → Bool

/-- Boolean functions `f : {0,1}ⁿ → {0,1}`. -/
abbrev BoolFn (n : ℕ) : Type := Cube n → Bool

/-- `d(f, g) = |{x ∈ {0,1}ⁿ : f(x) ≠ g(x)}| / 2ⁿ` (§3, p.14). -/
def fnDist {n : ℕ} (f g : BoolFn n) : ℝ :=
  ((Finset.univ.filter (fun x => f x ≠ g x)).card : ℝ) / 2 ^ n

/-- `g` is `ε`-far from (every function in) the property `P`: `d(f, g) ≥ ε` for all `f ∈ P`
(§3, p.14; §4.1, p.16). -/
def IsFar {n : ℕ} (P : Set (BoolFn n)) (g : BoolFn n) (ε : ℝ) : Prop :=
  ∀ f ∈ P, ε ≤ fnDist f g

/-- The monotone functions (Definition 2, p.14): `f(x) ≤ f(y)` whenever `x ⪯ y`. -/
def Mon (n : ℕ) : Set (BoolFn n) := {f | Monotone f}

/-- Bits of memory of an `M`-state algorithm: `m = ⌈log₂ M⌉` (§4.1, p.16). -/
def bits (M : ℕ) : ℕ := Nat.clog 2 M

end

end SpacePropTest


