-- Prove2me | Definitions.Def_GnpColoring_variance
-- name    : GnpColoring_variance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:42.007008+00:00
-- url     : https://prove2.me/theorems/a328ba1f-0b81-4c25-9d2d-70680c04f246
-- title:
--   Variance $\mathrm{Var}_\nu[f]$
-- statement:
--   $$\mathrm{Var}_\nu[f]=\mathbb E_\nu[f^2]-\mathbb E_\nu[f]^2.$$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.2, p.13

import Mathlib
import Definitions.Def_GnpColoring_expect

open scoped Classical
open Finset

namespace GnpColoring

/-- **Variance** `Var_ν[f] = E_ν[f²] − E_ν[f]²`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.2, p.13: "Var_ν[f] = E_ν[f²] − E_ν[f]²." -/
noncomputable def variance {n q : ℕ} (ν : (Fin n → Fin q) → ℝ) (f : (Fin n → Fin q) → ℝ) : ℝ :=
  expect ν (fun σ => f σ ^ 2) - expect ν f ^ 2

end GnpColoring


