-- Prove2me | Definitions.Def_PunctSketch_subsampled
-- name    : PunctSketch_subsampled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:02.840206+00:00
-- url     : https://prove2.me/theorems/93ccbdef-6b3c-4a7a-acc9-b7954fb3d99e
-- title:
--   The subsampled graph $G_{r,l}$
-- statement:
--   Each unordered pair carries a coin uniform on $\{0,\dots,2^l-1\}$, and an edge of $G$ survives when its coin is $0$. So each edge survives with probability $2^{-l}$, and at $l=0$ all edges survive.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.1, p.15 (PDF p.16)

import Mathlib

namespace PunctSketch

/-- **The random subgraph `G_{r,l}`.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.1, p.15: "`E_{r,l}` contains each edge in E with
probability 2^{−l}". Each unordered pair carries a coin uniform on `Fin (2^l)`, and an edge survives
when its coin is `0`. -/
def subsampled {V : Type*} {l : ℕ} (G : SimpleGraph V) (keep : Sym2 V → Fin (2 ^ l)) :
    SimpleGraph V where
  Adj a b := G.Adj a b ∧ (keep s(a, b) : ℕ) = 0
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

end PunctSketch


