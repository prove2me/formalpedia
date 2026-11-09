-- Prove2me | Definitions.Def_AbelianCayleyHDX_HasLocalSpectralNorm
-- name    : AbelianCayleyHDX_HasLocalSpectralNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:48.965012+00:00
-- url     : https://prove2.me/theorems/43b1ffb9-9b80-42eb-a97f-85f0d27435d7
-- title:
--   Two-sided local spectral norm at most $\lambda$ (dimension two)
-- statement:
--   A two-dimensional complex with triangle set $T$ (uniform distribution) has **two-sided codimension-two local spectral norm at most $\lambda$** if for every vertex $v$ of the complex (every codimension-two face when $d = 2$), the weighted link graph of $v$ is connected and its random-walk operator $P_v$ satisfies $\|P_v|_{\mathbf 1^{\perp_{\pi_v}}}\|_{\pi_v} \le \lambda$, i.e. the link of $v$ is a two-sided $\lambda$-spectral expander.
--
--   **Formalization Note** The vertices of the complex are the points lying in some triangle.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8

import Mathlib
import Definitions.Def_AbelianCayleyHDX_linkVerts
import Definitions.Def_AbelianCayleyHDX_linkWeight
import Definitions.Def_AbelianCayleyHDX_IsTwoSidedSpectralExpander
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Two-sided codimension-two local spectral norm at most `λ`, dimension two** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba),
Section 2.2, p.8): for every vertex `v` of the complex (every codimension-two face when `d = 2`),
the weighted link graph of `v` is connected and its random-walk operator has norm at most `λ` on
the mean-zero functions of its stationary measure, i.e. it is a two-sided `λ`-spectral expander.

**Formalization Note** The vertices of the complex are the points lying in a triangle of `T`; the
link of `v` has vertex set `linkVerts T v` and edge weights `linkWeight T v`. -/
def HasLocalSpectralNorm {n : ℕ} (T : Finset (Finset (Vec n))) (lam : ℝ) : Prop :=
  ∀ v : Vec n, (∃ τ ∈ T, v ∈ τ) → IsTwoSidedSpectralExpander (linkVerts T v) (linkWeight T v) lam

end AbelianCayleyHDX


