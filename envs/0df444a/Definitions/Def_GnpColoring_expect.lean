-- Prove2me | Definitions.Def_GnpColoring_expect
-- name    : GnpColoring_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:50.556482+00:00
-- url     : https://prove2.me/theorems/c2024820-1929-4118-925a-c2a2702b701c
-- title:
--   Expectation under a mass function
-- statement:
--   For a mass function $\nu$ on colourings $\sigma:V\to[q]$ and a function $X$, $\mathbb E_\nu[X]=\sum_\sigma\nu(\sigma)X(\sigma)$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.2, p.13

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **Expectation** `E_ν[X] = Σ_σ ν(σ) X(σ)` of a function of colourings under a mass function `ν`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.2, p.13 ("⟨f, g⟩_ν = E_ν[fg]"). -/
noncomputable def expect {n q : ℕ} (ν : (Fin n → Fin q) → ℝ) (X : (Fin n → Fin q) → ℝ) : ℝ :=
  ∑ σ, ν σ * X σ

end GnpColoring


