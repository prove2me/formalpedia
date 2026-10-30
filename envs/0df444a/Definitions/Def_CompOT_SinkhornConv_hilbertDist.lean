-- Prove2me | Definitions.Def_CompOT_SinkhornConv_hilbertDist
-- name    : CompOT_SinkhornConv_hilbertDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:53:44.435215+00:00
-- url     : https://prove2.me/theorems/71f55e75-e39e-4d65-86b9-987d41f2192a
-- title:
--   Hilbert projective metric $d_{\mathcal H}(u,u')$
-- statement:
--   For two vectors $u, u'$ with positive entries indexed by a finite set, the **Hilbert projective metric** is
--   $$d_{\mathcal H}(u,u') = \log \max_{i,j} \frac{u_i\,u'_j}{u_j\,u'_i}.$$
--
--   It measures how far $u$ and $u'$ are from being proportional: it vanishes exactly when $u = r u'$ for some $r > 0$, and it is unchanged when either vector is rescaled. Birkhoff's theorem shows that a matrix with positive entries contracts this metric, which is the engine of the convergence analysis of Sinkhorn's algorithm.
--
--   **Formalization Note** The paper defines $d_{\mathcal H}$ only on positive vectors. The Lean function is total (the maximum is a real supremum over the finite index set, and $\log$ is Mathlib's `Real.log`), but every statement of the mission applies it only to vectors that are assumed or proved to be entrywise positive.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, Remark 4.12, p. 439 (definition of d_H)

import Mathlib

namespace CompOT.SinkhornConv

/-- **Hilbert projective metric `d_H(u, u') = log max_{i,j} (u_i u'_j)/(u_j u'_i)`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), Remark 4.12, p. 439: "the Hilbert projective metric on Rn+,∗ (positive vectors), defined as
∀(u, u′) ∈ (Rn+,∗)², dH(u, u′) := log max_{i,j} (uiu′j)/(uju′i)."

`hilbertDist u u'` is `Real.log` of the maximum over all pairs of indices `(i, j)` of
`u i * u' j / (u j * u' i)`.

**Formalization Note.** The paper defines `d_H` only on positive vectors. The Lean function is
total, but every statement of this mission applies it only to vectors that are assumed or proved
to be entrywise positive; on such vectors the real supremum over the finite index set is the
paper's maximum. On an empty index type the value is `Real.log 0 = 0`. -/
noncomputable def hilbertDist {ι : Type*} [Fintype ι] (u u' : ι → ℝ) : ℝ :=
  Real.log (⨆ i, ⨆ j, u i * u' j / (u j * u' i))

end CompOT.SinkhornConv


