-- Prove2me | Definitions.Def_IntADSat_Supplement_moment
-- name    : IntADSat_Supplement_moment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:42:57.200897+00:00
-- url     : https://prove2.me/theorems/fa4a423e-09a8-40c9-8d13-5e79898ffca2
-- title:
--   Principal AD-moment $\mu_G(w)$
-- statement:
--   For a graph $G$ on $n$ vertices and a word $w$ in the letters $a,d$, the **principal AD-moment** is
--   $$\mu_G(w)=e^{\mathsf T}w(A_G,D_G)e\in\mathbb Z,$$
--   the sum of the coordinates of the word vector $w(A_G,D_G)e$. For the empty word it equals $n$, the order of $G$. By (C.1) the moments are homomorphism counts of caterpillars.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §A.3, p.13 (PDF 14)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordVec

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- The **principal AD-moment** `μ_G(w) = eᵀ w(A_G, D_G) e` of a word `w`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §A.3, p.13 (PDF 14)).

**Formalization Note** Written as the coordinate sum of the published word vector `w(A_G, D_G)e`.
For the empty word it is `eᵀe = n`, the order of the graph. -/
noncomputable def moment {n : ℕ} (G : SimpleGraph (Fin n)) (w : Word) : ℤ :=
  ∑ i, IntADSat.wordVec G w i

end IntADSat.Supplement


