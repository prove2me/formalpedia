-- Prove2me | Definitions.Def_GibbsCongestion_projDist
-- name    : GibbsCongestion_projDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:23.764361+00:00
-- url     : https://prove2.me/theorems/640018a1-dbf2-413b-8cea-6b7a3581a7ff
-- title:
--   Projected distribution $\bar\pi(i)=\pi(\Omega_i)$
-- statement:
--   For a partition $\Omega=\Omega_1\cup\dots\cup\Omega_m$ of the state space and a distribution $\pi$ on $\Omega$,
--   $$\bar\pi(i)=\pi(\Omega_i)=\sum_{x\in\Omega_i}\pi(x).$$
--   It is the stationary distribution of the projection chain.
--
--   **Formalization Note** The partition is given by a map $\mathrm{cls}:\Omega\to\iota$, with $\Omega_i=\mathrm{cls}^{-1}(i)$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11

import Mathlib

namespace GibbsCongestion

/-- The **projected distribution** `π̄(i) = π(Ω_i) = ∑_{x ∈ Ω_i} π(x)` for a partition
`Ω = ⋃ Ω_i` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11).

**Formalization Note** The partition is given by the map `cls : Ω → ι`, with `Ω_i = cls⁻¹(i)`. -/
noncomputable def projDist {Ω ι : Type*} [Fintype Ω] [DecidableEq ι] (π : Ω → ℝ) (cls : Ω → ι) (i : ι) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => cls x = i), π x

end GibbsCongestion


