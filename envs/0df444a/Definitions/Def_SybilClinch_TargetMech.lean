-- Prove2me | Definitions.Def_SybilClinch_TargetMech
-- name    : SybilClinch_TargetMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:02.532199+00:00
-- url     : https://prove2.me/theorems/1e88ed93-89bf-4174-93d2-434bfc00a770
-- title:
--   Abstract target-based mechanism $(p_\star,T,D,X_\sigma)$
-- statement:
--   An **abstract target-based mechanism** consists of an initial clock price $p_\star$, a cumulative target rule $T(p,X,Y)$ giving at the auction state $(p,X,Y)$ (clock price, aggregate allocation, aggregate payment) the cumulative quantity that may be allocated, a domain $D$ of auction states on which the rule is defined, and a capacity bound $X_\sigma\in(0,+\infty]$. The residual supply at a state is $S=T(p,X,Y)-X$.
--
--   **Formalization Note** The paper's environment description $\sigma$ is folded into the price argument of $T$ (Definition 4.1, item 2: the price argument selects any clock-indexed information in $\sigma$). The capacity is an extended real.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.1, Definition 4.1, p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.1, Definition 4.1 (Abstract target-based mechanism), printed p.13 (PDF p.15).

A target-based mechanism `(p⋆, T, D, X_σ)`: initial clock price `pstar`, cumulative target rule
`T p X Y` at the auction state `(p, X, Y)` (clock price, aggregate allocation, aggregate payment),
the domain `D` of auction states, and the capacity `cap ∈ (0, +∞]`.

**Formalization Note.** The environment description `σ` is folded into the price argument of `T`
(Definition 4.1, item 2: the explicit price argument selects any clock-indexed information
contained in `σ`), so `T` depends only on `(p, X, Y)`. The capacity is an `EReal` (`+∞ = ⊤`);
`0 < pstar`, `0 < cap` and the range `[0, cap]` of `T` are part of `TargetMech.Admissible`. -/
structure TargetMech where
  /-- The initial clock price `p⋆`. -/
  pstar : ℝ
  /-- The cumulative target rule `T_σ(p, X, Y)`. -/
  T : ℝ → ℝ → ℝ → ℝ
  /-- The domain `D_σ` of auction states `(p, X, Y)`. -/
  D : Set (ℝ × ℝ × ℝ)
  /-- The capacity bound `X_σ ∈ (0, +∞]`. -/
  cap : EReal

end SybilClinch


