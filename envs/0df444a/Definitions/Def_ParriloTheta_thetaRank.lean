-- Prove2me | Definitions.Def_ParriloTheta_thetaRank
-- name    : ParriloTheta_thetaRank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:01.098261+00:00
-- url     : https://prove2.me/theorems/9d1565b6-398d-4f75-bf47-9682add807f5
-- title:
--   The $\vartheta$-rank of a graph
-- statement:
--   The **$\vartheta$-rank** of a graph $G$ is the smallest integer $r\ge0$ for which $\vartheta^{(r)}(G)=\alpha(G)$, with $\vartheta\text{-rank}(G)=\infty$ if no such $r$ exists. By (1.7) it is also the least $r$ with $M_G\in\mathcal K^{(r)}$.
--
--   **Formalization Note** Values in `ℕ∞`, with `⊤` for $\infty$ (the infimum of the empty set). The vertex type is only required to be finite, so induced subgraphs (subtypes) and disjoint unions need no extra instances.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, p.2

import Mathlib
import Definitions.Def_ParriloTheta_thetaR

namespace ParriloTheta

/-- **The ϑ-rank of a graph.**
Laurent & Vargas, arXiv:2109.12876v1, p.2: "the parameter ϑ-rank(G), called the ϑ-rank of G,
which is defined in [19] as the smallest integer r for which ϑ(r)(G) = α(G), setting
ϑ-rank(G) = ∞ if no such r exists."

`thetaRank G` is the least `r : ℕ` with `ϑ^(r)(G) = α(G)`, as an element of `ℕ∞`, and `⊤ = ∞`
when there is no such `r`.

**Formalization Note.** Values in `ℕ∞`: `sInf ∅ = ⊤` encodes "∞ if no such r exists". The vertex
type only needs to be `Finite`; a `Fintype` structure is chosen with `Fintype.ofFinite` (all
`Fintype` structures on a type are equal), so the ϑ-rank of an induced subgraph (a subtype) needs
no decidability instances. -/
noncomputable def thetaRank {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ∞ :=
  letI : Fintype V := Fintype.ofFinite V
  sInf ((fun r : ℕ => (r : ℕ∞)) '' {r : ℕ | thetaR r G = (G.indepNum : ℝ)})

end ParriloTheta


