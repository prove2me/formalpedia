-- Prove2me | Definitions.Def_ErrAmpOV_LowDim
-- name    : ErrAmpOV_LowDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:40.409198+00:00
-- url     : https://prove2.me/theorems/cb01f596-f075-4bae-9d30-d0cf77cb5b59
-- title:
--   The low-dimensional regime $\omega(\log n)\le d(n)\le n^{o(1)}$
-- statement:
--   A dimension function $d:\mathbb N\to\mathbb N$ lies in the **low-dimensional regime**, "between $\omega(\log n)$ and $n^{o(1)}$", when
--   $$
--   \frac{d(n)}{\log n}\to\infty
--   \quad\text{and}\quad
--   \frac{\log d(n)}{\log n}\to 0
--   \qquad(n\to\infty).
--   $$
--
--   This is the standard regime for hardness conjectures on OV, and every hypothesis and conclusion on OV in the mission is quantified over such $d$.
--
--   **Formalization Note** `log` is `Real.log`, and the base does not matter for either limit. `Real.log 0 = 0` is harmless because the first limit forces $d(n)\to\infty$.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), §3, p.9

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace ErrAmpOV

/-- The low-dimensional regime: a dimension function `d : ℕ → ℕ` is "between `ω(log n)` and
`n^{o(1)}`" when `d(n) / log n → ∞` and `log d(n) / log n → 0` as `n → ∞`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
§3, p.9: "the low dimension regime … where `d` is restricted between `ω(log(n))` and
`n^{o(1)}`".

**Formalization Note.** `log` is `Real.log`; the base does not matter for either limit.
`Real.log 0 = 0` is harmless, because the first limit forces `d n → ∞`. `d(n) ≤ n^{o(1)}` means
`log d(n) ≤ ε(n) log n` with `ε(n) → 0`, which (since `log d(n) ≥ 0` eventually) is the second
limit. -/
def LowDim (d : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (d n : ℝ) / Real.log n) atTop atTop ∧
    Tendsto (fun n : ℕ => Real.log (d n) / Real.log n) atTop (𝓝 0)

end ErrAmpOV


