-- Prove2me | Definitions.Def_SybilClinch_chordTarget
-- name    : SybilClinch_chordTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:04.323692+00:00
-- url     : https://prove2.me/theorems/c9ade1e0-c4c8-43ef-943a-f5b3d5a250ca
-- title:
--   Chord target: rightmost intersection of $K$ with a line of slope $p$
-- statement:
--   For a cost curve $K$ with capacity $\mathrm{cap}$ and an auction state $(p,X,Y)$ with $Y\ge K(X)$, the **chord target** is
--   $$T(p,X,Y):=\max\{z\in[X,\mathrm{cap}):K(z)\le Y+p(z-X)\},$$
--   the rightmost intersection of $K$ with the line of slope $p$ through $(X,Y)$. For $K=C$, $\mathrm{cap}=x_0$ this is the AMM chord target $T^{\rm amm}$ (11); for $\widetilde C_M$ and $\widetilde C^{\rm rev}_M$ it is $\widetilde T_M$ and $\widetilde T^{\rm rev}_M$.
--
--   **Formalization Note** Written as a supremum, which is the maximum on the state domain of an admissible cost; values off that domain are never used.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (11), p.9 (PDF p.11); §5.2, pp.26–27 (PDF pp.28–29)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (11), printed p.9 (PDF p.11), and §5.2, printed p.26 (PDF p.28): the chord target of
a cost curve `K` with capacity `cap` at the state `(p, X, Y)`,
`T(p, X, Y) := max {z ∈ [X, cap) : K(z) ≤ Y + p(z − X)}`, the rightmost intersection of `K` with
the line of slope `p` through `(X, Y)`.

For `K = C` and `cap = x₀` this is `T^amm` of (11); for `K = C̃_M`, `cap = M + x₀` it is `T̃_M`; for
`K = C̃^rev_M`, `cap = p₀M + y₀` it is `T̃^rev_M` (p.27).

**Formalization Note.** Written as `sSup`; on the state domain `{Y ≥ K X, 0 ≤ X < cap}` of an
admissible cost the set is nonempty, closed in `[X, cap)` and bounded away from `cap`, so the
supremum is the maximum. Outside that domain the value is junk and is never used. -/
noncomputable def chordTarget (K : ℝ → ℝ) (cap p X Y : ℝ) : ℝ :=
  sSup {z : ℝ | X ≤ z ∧ z < cap ∧ K z ≤ Y + p * (z - X)}

end SybilClinch


