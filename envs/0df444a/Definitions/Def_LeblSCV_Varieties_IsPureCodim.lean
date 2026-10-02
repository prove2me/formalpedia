-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsPureCodim
-- name    : LeblSCV_Varieties_IsPureCodim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:10:45.830481+00:00
-- url     : https://prove2.me/theorems/24099df4-fd3a-4257-9d40-bde4cb67d03e
-- title:
--   Definition 6.5.7 — pure codimension (hypervariety for codimension 1)
-- statement:
--   A set $X \subset \mathbb{C}^n$ is of **pure codimension $c$** if it is of pure dimension $n - c$: codimension is the ambient dimension minus the dimension. A subvariety of pure codimension $1$, i.e. with
--   $$\dim_q X = n - 1 \quad \text{for all } q \in X_{\mathrm{reg}},$$
--   is called a **hypervariety** (p. 188).
--
--   **Formalization Note.** The difference $n - c$ is computed in `ℤ`. In particular, for $n = 0$ no point can be regular of dimension $-1$, so the only pure-codimension-1 set in $\mathbb{C}^0$ is one without regular points.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 186, Definition 6.5.7; the word hypervariety p. 188

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsPureDim

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.7: `X ⊆ ℂⁿ` is of **pure codimension `c`** if it is of pure dimension
`n - c` (codimension = ambient dimension minus dimension), computed in `ℤ`.
A subvariety of pure codimension 1 is a **hypervariety** (p. 188). -/
def IsPureCodim {n : ℕ} (X : Set (Fin n → ℂ)) (c : ℤ) : Prop :=
  IsPureDim X ((n : ℤ) - c)

end LeblSCV.Varieties


