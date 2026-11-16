-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_Supplement_EtaModel
-- name    : BourgainUnion_Euclidean_Supplement_EtaModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:05.513542+00:00
-- url     : https://prove2.me/theorems/7e1fd987-d0be-4407-9e1a-35b3260821e9
-- title:
--   The exponent $\eta(c)$ of Section 7
-- statement:
--   For a real $c\ge1$, Section 7 defines $\eta(c)$ as the unique root $\eta\ge c-1$ of
--   $$\bigl((1+\eta)^2-c^2\bigr)\bigl((1+\eta/2)^2-2\bigr)=\frac{\pi c^2}{2}.$$
--   The definition takes the infimum of the set of such roots. That the set is nonempty, so that $\eta(c)$ is itself a root, is a conclusion of the Theorem 1.7 item, together with $\eta(c)\le c-1+\pi/c$ and $\eta(1)=\eta_0$; nothing about the root is built into the definition.
--
--   **Formalization Note** Real `sInf` of an empty set is $0$; the Theorem 1.7 item asserts that the set is nonempty for every $c\ge1$, so this junk value never enters a true statement about $\eta(c)$.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 27, §7 (definition of η(c))

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

/-- §7, p. 27: for `c ≥ 1`, `η(c)` is the root `η ≥ c − 1` of
`((1+η)² − c²)((1+η/2)² − 2) = πc²/2`. Existence and uniqueness of the root are conclusions of
Theorem 1.7's item, not part of this definition. -/
def etaC (c : ℝ) : ℝ :=
  sInf {η : ℝ | c - 1 ≤ η ∧ ((1+η)^2 - c^2) * ((1+η/2)^2 - 2) = Real.pi * c^2 / 2}

end BourgainUnion.Euclidean.Supplement


