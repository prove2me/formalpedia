-- Prove2me | Definitions.Def_GnpColoring_condVar
-- name    : GnpColoring_condVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:01.022053+00:00
-- url     : https://prove2.me/theorems/daf19a7f-6737-490c-8607-65b8356d31e5
-- title:
--   Conditional variance $\mathrm{Var}_U[f]$
-- statement:
--   For a set $U$ of vertices, $\mathrm{Var}_U[f]$ is the variance of $f$ under $\nu$ conditioned on the colours outside $U$:
--
--   $$\mathrm{Var}_U[f](\sigma)=\mathbb E_\nu[f^2\mid\sigma_{V\setminus U}]-\mathbb E_\nu[f\mid\sigma_{V\setminus U}]^2,$$
--
--   a function of the exterior colours. For $U=\{v\}$ it is written $\mathrm{Var}_v[f]$.
--
--   **Formalization Note** Off the support of $\nu$ the conditional expectations take the junk value $0$; the quantity is only used $\nu$-weighted.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.2, p.13

import Mathlib
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **Conditional variance over the coordinates in `U`** given all other coordinates:
`Var_U[f](x) = E_ν[f² | σ_{V∖U} = x_{V∖U}] − E_ν[f | σ_{V∖U} = x_{V∖U}]²`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.2, p.13: "For U ⊆ V, the notation Var_U[f] = Var_µ[f | σ_{V∖U}] denotes a
conditional variance, which is a function of the exterior colors; for U = {v} we write Var_v[f]."

**Formalization Note** Built from `SpinGirth5.condExp` (a ratio of `ν`-sums, junk `0` off the
support of `ν`); it is only used `ν`-weighted. -/
noncomputable def condVar {n q : ℕ} (ν : (Fin n → Fin q) → ℝ) (U : Finset (Fin n))
    (f : (Fin n → Fin q) → ℝ) (x : Fin n → Fin q) : ℝ :=
  SpinGirth5.condExp ν (univ \ U) (fun y => f y ^ 2) x -
    SpinGirth5.condExp ν (univ \ U) f x ^ 2

end GnpColoring


