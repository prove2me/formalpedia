-- Prove2me | Definitions.Def_BorderDiffEq_eps
-- name    : BorderDiffEq_eps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:17.514319+00:00
-- url     : https://prove2.me/theorems/646474bd-a51b-4435-9bb7-8642ae5d0060
-- title:
--   The border parameter $\varepsilon\in F((\varepsilon))$
-- statement:
--   For a field $F$, the **border parameter** $\varepsilon$ is the formal variable of the field of formal Laurent series
--   $$
--   F((\varepsilon))=\Big\{\sum_{j\ge j_0}a_j\varepsilon^j : j_0\in\mathbb Z,\ a_j\in F\Big\}.
--   $$
--   The paper takes circuit constants in $F(\varepsilon)$ and regards $K(\varepsilon)$ as a subfield of $K((\varepsilon))$.
--
--   **Formalization Note** $F((\varepsilon))$ is Mathlib's `LaurentSeries F` $=$ `HahnSeries ℤ F`, and $\varepsilon$ is `HahnSeries.single 1 1`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §4, p.23, Notation and Circuit classes and borders

import Mathlib

namespace BorderDiffEq

/-- **The border parameter `ε`** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
§4, p.23, "Circuit classes and borders" and "Notation"): the formal variable `ε` as an element of
the field of formal Laurent series `F((ε))`.

**Formalization Note.** The paper takes constants in `F(ε)` and regards `K(ε)` as a subfield of
`K((ε))` (p.23). Here `F((ε))` is Mathlib's `LaurentSeries F = HahnSeries ℤ F`, and `ε` is the
series `HahnSeries.single 1 1`. -/
noncomputable def eps (F : Type) [Field F] : LaurentSeries F :=
  HahnSeries.single (1 : ℤ) (1 : F)

end BorderDiffEq


