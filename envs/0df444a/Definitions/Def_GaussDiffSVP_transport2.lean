-- Prove2me | Definitions.Def_GaussDiffSVP_transport2
-- name    : GaussDiffSVP_transport2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:49.517952+00:00
-- url     : https://prove2.me/theorems/a85d1fdf-67be-4881-b25b-fa66935a9643
-- title:
--   Transport map $\Psi_q(U,V)$
-- statement:
--   For a pair map $T$ and an activation weight $q$,
--   $$\Psi_q(U,V)(z,z') = \sum_{T(x,y)=z,\ T(x',y')=z'} q(x,y)\,q(x',y')\,U(x,x')\,V(y,y'),$$
--   which transports two copies of the input counts. Sums are in $[0,\infty]$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (21), p.23

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP

/-- The positive map
`Ψ_q(U, V)(z, z′) = ∑_{T(x,y) = z, T(x′,y′) = z′} q(x, y) q(x′, y′) U(x, x′) V(y, y′)`
(Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (21), p.23), which transports two copies of the input counts.

**Formalization Note.** An unconditional sum in `ℝ≥0∞` over the quadruples with
`T(x, y) = z` and `T(x′, y′) = z′`. -/
noncomputable def transport2 {α β γ : Type*} (T : α → β → γ) (q : α → β → ℝ≥0∞)
    (U : α → α → ℝ≥0∞) (V : β → β → ℝ≥0∞) (z z' : γ) : ℝ≥0∞ :=
  ∑' p : {p : (α × β) × (α × β) // T p.1.1 p.1.2 = z ∧ T p.2.1 p.2.2 = z'},
    q p.1.1.1 p.1.1.2 * q p.1.2.1 p.1.2.2 * U p.1.1.1 p.1.2.1 * V p.1.1.2 p.1.2.2

end GaussDiffSVP


