-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_noiseLaw
-- name    : GradSuffice_Thm8Data_noiseLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:00.245111+00:00
-- url     : https://prove2.me/theorems/6fdcecfd-8b71-4130-b6e0-6b1fd7a4120f
-- title:
--   Law of the auxiliary noise of Theorem 8
-- statement:
--   All auxiliary noise variables $Z^\pm_\xi$ (for every copy) and $Z_{t,k}$ are independent and uniformly distributed on $[-\nu,\nu]$; their joint law is the product of these uniform laws.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_NoiseIdx

namespace GradSuffice

/-- **Law of the auxiliary noise.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19: "`Z^±_ξ` are i.i.d. random variables, picked
uniformly from `[−ν, ν]`", the copies `ρ₁, …, ρ_κ` are independent, and "the `Z_{t,k}` are i.i.d.
uniformly distributed on `[−ν, ν]`".

**Formalization Note.** The product over the finite noise index set of the uniform law
`volume[|[−ν, ν]]` on `ℝ`. -/
noncomputable def Thm8Data.noiseLaw {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) :
    MeasureTheory.Measure (c.NoiseIdx → ℝ) :=
  MeasureTheory.Measure.pi (fun _ => ProbabilityTheory.cond MeasureTheory.volume (Set.Icc (-c.ν) c.ν))

end GradSuffice


