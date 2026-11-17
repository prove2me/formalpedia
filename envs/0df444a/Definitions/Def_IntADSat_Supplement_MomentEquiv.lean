-- Prove2me | Definitions.Def_IntADSat_Supplement_MomentEquiv
-- name    : IntADSat_Supplement_MomentEquiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:43:41.692615+00:00
-- url     : https://prove2.me/theorems/44bacf45-612c-4e6f-afab-5f781395543a
-- title:
--   Moment equivalence $G\equiv_\mu H$
-- statement:
--   Two finite simple graphs $G$ and $H$ (possibly with different vertex sets) are **moment equivalent**, $G\equiv_\mu H$, when
--   $$\mu_G(w)=\mu_H(w)\quad\text{for every word }w,$$
--   including the empty word, whose moment records the graph order. The **principal moment fibre** of $G$ consists of all graphs $H$ with $H\equiv_\mu G$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §A.3, p.13 (PDF 14); §S4, p.39 (PDF 40)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_Supplement_moment

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- `G ≡_μ H`: the principal AD-moments of `G` and `H` agree for every word, including the empty word
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §A.3, p.13 (PDF 14)). The **principal moment fibre** of `G` is the class of graphs `H` with
`H ≡_μ G` (§S4, p.39 (PDF 40)).

**Formalization Note** `G` and `H` may have different vertex types `Fin n`, `Fin m`; the empty-word
moment forces `n = m` when they are equivalent. -/
def MomentEquiv {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) : Prop :=
  ∀ w : Word, moment G w = moment H w

end IntADSat.Supplement


