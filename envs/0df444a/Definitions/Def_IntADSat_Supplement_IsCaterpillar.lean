-- Prove2me | Definitions.Def_IntADSat_Supplement_IsCaterpillar
-- name    : IntADSat_Supplement_IsCaterpillar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:52:19.311139+00:00
-- url     : https://prove2.me/theorems/7c31eb41-c1e4-4ff8-ad11-e16a038580a3
-- title:
--   Caterpillar
-- statement:
--   A finite simple graph $T$ is a **caterpillar** if it is isomorphic to some ordinary caterpillar $C(a_0,\dots,a_k)$, $k\ge0$, $a_i\ge0$. In particular $K_1$ is a caterpillar.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Appendix C, p.20 (PDF 21); Theorem 1.2, p.2 (PDF 3)

import Mathlib
import Definitions.Def_IntADSat_Supplement_caterpillarGraph

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `T` is an **(ordinary) caterpillar**: a finite simple graph isomorphic to some `C(a_0, …, a_k)`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix C, p.20 (PDF 21); Theorem 1.2, p.2 (PDF 3)). `K_1 = C(0)` is a caterpillar.

**Formalization Note** Any vertex type; the test trees are unlabelled, so only the isomorphism type
matters. -/
def IsCaterpillar {V : Type} (T : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (a : Fin (k + 1) → ℕ), Nonempty (T ≃g caterpillarGraph k a)

end IntADSat.Supplement


