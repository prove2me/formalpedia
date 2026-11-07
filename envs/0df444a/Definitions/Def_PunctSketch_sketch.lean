-- Prove2me | Definitions.Def_PunctSketch_sketch
-- name    : PunctSketch_sketch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:51.492885+00:00
-- url     : https://prove2.me/theorems/5c510c78-c83d-44ac-8f24-94cce6e91a0d
-- title:
--   The puncturable sparse-recovery sketch
-- statement:
--   The sketch of the vertex $v$ is the image of its row of $A^\pm$ under a Vandermonde matrix. Its $t$-th coordinate is
--   $$\boldsymbol s(v)_t=\sum_{u\in N(v)}A^{\pm}[v,u]\,\alpha_u^{t}=\sum_{u\in N(v)}\mathrm{sgn}(u-v)\,\alpha_u^{t}.$$
--
--   **Formalization Note** The points $\alpha$ are a parameter, and the coordinate $t$ is any natural number; statements restrict it to the source's range.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Theorem 4, pp.10–11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_PunctSketch_signedAdj

namespace PunctSketch

/-- **The puncturable sparse-recovery sketch.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Theorem 4, pp.10–11:
`𝒔(v) = Ψ 𝒂±_v` with `Ψ = Van_{2d+k}(α_1, …, α_n)`, whose `t`-th entry is
`𝒔(v)_t = Σ_{u∈N(v)} A±[v, u] α_u^t = Σ_{u∈N(v)} sgn(u − v) α_u^t`.

**Formalization Note.** Defined for every `t : ℕ`; the theorems that use it restrict `t` to the
range of the source. The points `α` are a parameter. -/
noncomputable def sketch {n Q : ℕ} (G : SimpleGraph (Fin n)) (α : Fin n → ZMod Q) (v : Fin n)
    (t : ℕ) : ZMod Q :=
  ∑ u, ((signedAdj G v u : ℤ) : ZMod Q) * α u ^ t

end PunctSketch


