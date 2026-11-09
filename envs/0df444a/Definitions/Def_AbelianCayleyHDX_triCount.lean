-- Prove2me | Definitions.Def_AbelianCayleyHDX_triCount
-- name    : AbelianCayleyHDX_triCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:25.293864+00:00
-- url     : https://prove2.me/theorems/f0271d95-a839-4b0e-8ac1-a9e2cc6567e5
-- title:
--   Number of triangles containing a face
-- statement:
--   For a triangle set $T$ and a set $e$ of vertices, $\mathrm{triCount}(T, e) = \#\{\tau \in T : e \subseteq \tau\}$ is the number of triangles containing $e$.
--
--   For the uniform top-face distribution on $T$, the induced weight of an edge $e$ is $\mu_1(e) = \mathrm{triCount}(T,e)/(3|T|)$ (the formula for $\mu_i$ on p.8 with $d = 2$, $i = 1$), so edge weights and triangle counts are proportional.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8; Theorem 1.2, p.4

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The number of triangles containing a face** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8, and Theorem 1.2,
p.4: "every edge lies in … triangles"): `#{τ ∈ T : e ⊆ τ}`.

**Formalization Note** For the uniform top-face distribution on `T`, the induced weight of an edge
`e` is `µ₁(e) = triCount T e / (3|T|)` (p.8, the formula for `µᵢ` with `d = 2`, `i = 1`). -/
def triCount {n : ℕ} (T : Finset (Finset (Vec n))) (e : Finset (Vec n)) : ℕ :=
  (T.filter fun τ => e ⊆ τ).card

end AbelianCayleyHDX


