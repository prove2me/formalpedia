-- Prove2me | Definitions.Def_GibbsCongestion_entropy
-- name    : GibbsCongestion_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:20.529114+00:00
-- url     : https://prove2.me/theorems/22abe471-467e-4d91-a033-a5c7a5640948
-- title:
--   Entropy functional $\mathrm{Ent}_\pi(f)$
-- statement:
--   For a distribution $\pi$ on a finite set $\Omega$ and $f:\Omega\to\mathbb R$, with $E_\pi(f)=\sum_x\pi(x)f(x)$,
--   $$\mathrm{Ent}_\pi(f)=E_\pi\big[f\log f-f\log E_\pi(f)\big].$$
--   It is the denominator of the modified log-Sobolev ratio.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, App. A, p.25

import Mathlib

namespace GibbsCongestion

/-- The **entropy** `Ent_π(f) = E_π[f log f − f log E_π(f)]`, with `E_π(f) = ∑_x π(x) f(x)`
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, App. A, p.25). -/
noncomputable def entropy {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, π x * (f x * Real.log (f x) - f x * Real.log (∑ y, π y * f y))

end GibbsCongestion


