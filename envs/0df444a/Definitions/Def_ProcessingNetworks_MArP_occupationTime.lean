-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_occupationTime
-- name    : ProcessingNetworks_MArP_occupationTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:26.441452+00:00
-- url     : https://prove2.me/theorems/379565fd-8435-4e13-bc50-daf0189daa4d
-- title:
--   The occupation time $T(s,t)$ of a state
-- statement:
--   The **occupation time** of state $s$ up to time $t$ along a path of $X$ is
--   $$
--   T(s,t)=\int_0^t 1_{\{X(u)=s\}}\,du ,
--   $$
--   the amount of time that $X$ spends in $s$ during $[0,t]$.
--
--   **Formalization Note** This is a Bochner integral, which is $0$ for a non-integrable integrand. On almost every path of a non-explosive chain the integrand is piecewise constant with finitely many pieces on $[0,t]$, so that value does not arise there.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section E.1, p.305 (PDF p.321)

import Mathlib

open MeasureTheory

namespace ProcessingNetworks.MArP

/-- The occupation time `T(s, t) = ∫₀ᵗ 1{X(u) = s} du` of state `s` up to time `t` (Dai & Harrison,
Processing Networks, pre-publication draft 2020-4-2, Section E.1, p.305, PDF p.321).

**Formalization Note.** On a path with positive clocks and `σ_n → ∞`, which is almost every path, the
integrand is piecewise constant with finitely many pieces on `[0, t]`, hence integrable, so the
Bochner integral's value `0` for a non-integrable function does not arise there. -/
noncomputable def occupationTime {S Ω : Type*} (X : ℝ → Ω → S) (s : S) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..t, Set.indicator {u | X u ω = s} (fun _ => (1 : ℝ)) u

end ProcessingNetworks.MArP


