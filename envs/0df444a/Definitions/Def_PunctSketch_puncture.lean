-- Prove2me | Definitions.Def_PunctSketch_puncture
-- name    : PunctSketch_puncture
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:36.404696+00:00
-- url     : https://prove2.me/theorems/38b367b8-9bb7-49ba-adc2-37f2577b9a86
-- title:
--   The artificial sketch, (6) and (7)
-- statement:
--   Given the coordinate sequence $w$ of the sketch of $v$, the artificial sketch punctured at $F$ has coordinates
--   $$\alpha_v^{t}\,P_F(\alpha_v)\sum_{i=0}^{|F|}b_{F,i}\,w_{t+i}.$$
--   With $w=\boldsymbol s(v)$ this is (6), with $w=\boldsymbol f(v)$ it is (7). It is computed from $w$ and $F$ alone, without the graph, which is what lets the coordinator delete $F$ after the messages were sent.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), p.11 (PDF p.12), eq. (6); p.13 (PDF p.14), eq. (7)

import Mathlib
import Definitions.Def_PunctSketch_puncturePoly

namespace PunctSketch

/-- **The artificial sketch, (6) and (7).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), p.11, eq. (6), and p.13, eq. (7):
`α_v^t P_F(α_v) Σ_{i=0}^{|F|} b_{F,i} w_{t+i}`, where `w` is the coordinate sequence of the sketch of
`v`, respectively `𝒔(v)` and `𝒇(v)`. The coordinator computes it from `w` and `F`, without `G`. -/
noncomputable def puncture {n Q : ℕ} (α : Fin n → ZMod Q) (F : Finset (Fin n)) (w : ℕ → ZMod Q)
    (v : Fin n) (t : ℕ) : ZMod Q :=
  α v ^ t * (puncturePoly α F).eval (α v) *
    ∑ i ∈ Finset.range (F.card + 1), (puncturePoly α F).coeff i * w (t + i)

end PunctSketch


