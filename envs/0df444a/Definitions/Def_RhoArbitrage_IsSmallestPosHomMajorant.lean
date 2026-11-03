-- Prove2me | Definitions.Def_RhoArbitrage_IsSmallestPosHomMajorant
-- name    : RhoArbitrage_IsSmallestPosHomMajorant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:50.449369+00:00
-- url     : https://prove2.me/theorems/206b514e-91e7-40ea-9fe0-d94d4e6ccbad
-- title:
--   Smallest positively homogeneous majorant of a map on $\mathbb R_+$
-- statement:
--   Let $g:\mathbb R_+\to[-\infty,\infty]$. A map $h:\mathbb R_+\to[-\infty,\infty]$ is a **positively homogeneous majorant** of $g$ if $h(\lambda\nu)=\lambda h(\nu)$ for all $\nu\ge0$ and $\lambda>0$, and $g\le h$ on $\mathbb R_+$. It is the **smallest** such majorant if in addition $h\le h'$ on $\mathbb R_+$ for every positively homogeneous majorant $h'$ of $g$.
--
--   These notions compare the map $\nu\mapsto\rho_\nu$ with $\nu\mapsto\rho^\infty_\nu$.
--
--   **Formalization Note** Maps on $\mathbb R_+$ are typed $\mathbb R\to$ `EReal`, and only their values at $\nu\ge0$ are constrained.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Propositions 3.9 and 3.10, p.8

import Mathlib

namespace RhoArbitrage

/-- `h` is a **positively homogeneous majorant** of `g` on `ℝ₊`: `h(λν) = λ h(ν)` for all `ν ≥ 0`
and `λ > 0`, and `g(ν) ≤ h(ν)` for all `ν ≥ 0`. Herdegen–Khan, arXiv:2202.07610v3, Proposition 3.9,
p.8, and the notion of positive homogeneity on p.4 (`λ` valued in `(0, ∞)`). Maps from `ℝ₊` to
`[-∞, ∞]` are typed `ℝ → EReal`, and only their values at `ν ≥ 0` are constrained. -/
def IsPosHomMajorant (g h : ℝ → EReal) : Prop :=
  (∀ ν : ℝ, 0 ≤ ν → ∀ lam : ℝ, 0 < lam → h (lam * ν) = (lam : EReal) * h ν) ∧
    ∀ ν : ℝ, 0 ≤ ν → g ν ≤ h ν

/-- `h` is the **smallest positively homogeneous majorant** of `g` on `ℝ₊`: it is one, and it lies
below every other one on `ℝ₊`. Herdegen–Khan, arXiv:2202.07610v3, Proposition 3.10, p.8. -/
def IsSmallestPosHomMajorant (g h : ℝ → EReal) : Prop :=
  IsPosHomMajorant g h ∧
    ∀ h' : ℝ → EReal, IsPosHomMajorant g h' → ∀ ν : ℝ, 0 ≤ ν → h ν ≤ h' ν

end RhoArbitrage


