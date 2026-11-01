-- Prove2me | Definitions.Def_GibbsCongestion_projChain
-- name    : GibbsCongestion_projChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:23.254186+00:00
-- url     : https://prove2.me/theorems/c9ac6bcc-98d7-430c-adc4-cc0e8fe3bb7a
-- title:
--   Projection chain $\bar P$
-- statement:
--   For a Markov chain $P$ with distribution $\pi$ and a partition $\Omega=\bigcup_i\Omega_i$, the **projection chain** has transition matrix
--   $$\bar P(i,j)=\bar\pi(i)^{-1}\sum_{x\in\Omega_i,\,y\in\Omega_j}\pi(x)P(x,y).$$
--   It is reversible with respect to $\bar\pi$. In the proof of Theorem 4.4 the partition is by strategy load profiles and $\bar\rho$ denotes its modified log-Sobolev constant.
--
--   **Formalization Note** The partition is given by a map $\mathrm{cls}:\Omega\to\iota$, with $\Omega_i=\mathrm{cls}^{-1}(i)$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11

import Mathlib
import Definitions.Def_GibbsCongestion_projDist

namespace GibbsCongestion

/-- The **projection chain** `P̄(i, j) = π̄(i)⁻¹ ∑_{x ∈ Ω_i, y ∈ Ω_j} π(x) P(x, y)` on the
classes of a partition `Ω = ⋃ Ω_i` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11).

**Formalization Note** The partition is given by `cls : Ω → ι`, with `Ω_i = cls⁻¹(i)`. -/
noncomputable def projChain {Ω ι : Type*} [Fintype Ω] [DecidableEq ι] (P : Matrix Ω Ω ℝ)
    (π : Ω → ℝ) (cls : Ω → ι) : Matrix ι ι ℝ :=
  fun i j => (projDist π cls i)⁻¹ *
    ∑ x ∈ Finset.univ.filter (fun x => cls x = i),
      ∑ y ∈ Finset.univ.filter (fun y => cls y = j), π x * P x y

end GibbsCongestion


