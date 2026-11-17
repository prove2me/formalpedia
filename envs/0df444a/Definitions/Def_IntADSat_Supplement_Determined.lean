-- Prove2me | Definitions.Def_IntADSat_Supplement_Determined
-- name    : IntADSat_Supplement_Determined
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:44:59.201164+00:00
-- url     : https://prove2.me/theorems/8bc8e8f5-37bb-4f98-bbae-96383eb7f159
-- title:
--   Determined by principal moments
-- statement:
--   A graph $G$ is **determined by its principal moments** if every finite simple graph $H$ with $H\equiv_\mu G$ is isomorphic to $G$, that is, if its principal moment fibre consists of a single isomorphism class.
--
--   **Formalization Note** $H$ ranges over the simple graphs on $\{0,\dots,m-1\}$ for every $m$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorems S6.4, S6.5, p.44 (PDF 45); Corollary S4.4, p.40 (PDF 41)

import Mathlib
import Definitions.Def_IntADSat_Supplement_MomentEquiv

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `G` is **determined by its principal moments**: every finite simple graph `H` (of any order) with
`H ≡_μ G` is isomorphic to `G` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §S5–S6, pp.42–44 (PDF 43–45), e.g. Theorems S6.4, S6.5;
Corollary S4.4, p.40 (PDF 41)).

**Formalization Note** "Every finite simple graph" is every `m` and every `H : SimpleGraph (Fin m)`. -/
def Determined {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), MomentEquiv G H → Nonempty (G ≃g H)

end IntADSat.Supplement


