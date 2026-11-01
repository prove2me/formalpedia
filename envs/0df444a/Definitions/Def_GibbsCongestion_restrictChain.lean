-- Prove2me | Definitions.Def_GibbsCongestion_restrictChain
-- name    : GibbsCongestion_restrictChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:24.365748+00:00
-- url     : https://prove2.me/theorems/65b58e9a-032b-48ea-a327-aad455161de7
-- title:
--   Restriction chain $P_i$ on $\Omega_i$
-- statement:
--   For a Markov chain $P$ and a class $\Omega_i$ of a partition, the **restriction chain** on $\Omega_i$ has transition matrix
--   $$P_i(x,y)=\begin{cases}P(x,y)&x\ne y,\\ 1-\sum_{z\in\Omega_i\setminus\{x\}}P(x,z)&x=y,\end{cases}\qquad x,y\in\Omega_i.$$
--   Moves leaving $\Omega_i$ are replaced by holding. In the proof of Theorem 4.4, $\rho_\alpha$ is the modified log-Sobolev constant of the restriction to $\mathcal S(\alpha)$.
--
--   **Formalization Note** The partition is given by a map $\mathrm{cls}:\Omega\to\iota$; the restriction chain lives on $\{x:\mathrm{cls}(x)=i\}$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11

import Mathlib

namespace GibbsCongestion

/-- The **restriction chain** on the class `Ω_i` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11):
`P_i(x, y) = P(x, y)` for `x ≠ y` and `P_i(x, x) = 1 − ∑_{z ∈ Ω_i ∖ {x}} P(x, z)`.

**Formalization Note** The partition is given by `cls : Ω → ι`; the state space of the restriction
chain is the subtype `{x // cls x = i}`. -/
noncomputable def restrictChain {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] (P : Matrix Ω Ω ℝ)
    (cls : Ω → ι) (i : ι) : Matrix {x // cls x = i} {x // cls x = i} ℝ :=
  fun x y => if x = y then 1 - ∑ z ∈ Finset.univ.erase x, P x.1 z.1 else P x.1 y.1

end GibbsCongestion


