-- Prove2me | Definitions.Def_IntADSat_HasProperInvariant
-- name    : IntADSat_HasProperInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:57.914277+00:00
-- url     : https://prove2.me/theorems/99f5f7df-6a89-4cea-8323-537879f82fcc
-- title:
--   $A,D$ have a nonzero proper common invariant subspace
-- statement:
--   Let $R$ be a commutative ring (in the paper, the prime field $\mathbb F_p$) and $G$ a simple graph on $[n]$, with adjacency and degree matrices $\bar A,\bar D$ reduced into $R$. The pair $(A,D)$ **has a nonzero proper common invariant subspace** over $R$ if there is a submodule $W\subseteq R^n$ with
--
--   $$
--   0\neq W\neq R^n,\qquad \bar A W\subseteq W,\qquad \bar D W\subseteq W .
--   $$
--
--   This is the event bounded in the fixed-prime and growing-prime estimates (Theorems S2.1 and S3.1); its absence implies $p$-AD-saturation, since $M_p(G)$ is a nonzero invariant subspace.
--
--   **Formalization Note** Used with $R$ = `ZMod p` for a prime $p$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S2.1, p.30 (PDF 31) and Theorem S3.1, p.35 (PDF 36)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- "`A`, `D` have a nonzero proper common invariant subspace" over `R`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S2.1, p.30 (PDF 31) and Theorem S3.1, p.35 (PDF 36)): some submodule
`W ≠ 0, W ≠ Rⁿ` is mapped into itself by the reduced adjacency matrix and the reduced degree matrix.

**Formalization Note** Used with `R = ZMod p`, `p` prime (the field `𝔽_p`); the matrices are reduced
from the integer adjacency and degree matrices by `Int.cast`. -/
def HasProperInvariant (R : Type) [CommRing R] {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ W : Submodule R (Fin n → R), W ≠ ⊥ ∧ W ≠ ⊤ ∧
    (∀ w ∈ W, ((adjacency G).map (Int.cast : ℤ → R)).mulVec w ∈ W) ∧
    (∀ w ∈ W, ((degreeMatrix G).map (Int.cast : ℤ → R)).mulVec w ∈ W)

end IntADSat


