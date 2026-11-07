-- Prove2me | Definitions.Def_PunctSketch_fingerprint
-- name    : PunctSketch_fingerprint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:53.002619+00:00
-- url     : https://prove2.me/theorems/07c296c5-a760-4358-b3f9-b2a89beb7049
-- title:
--   The fingerprint sketch
-- statement:
--   With one public field element $\boldsymbol r_{\{v,u\}}$ for each unordered pair,
--   $$\boldsymbol f(v)_t=\sum_{u\in N(v)}\mathrm{sgn}(v-u)\,\boldsymbol r_{\{v,u\}}\,(\alpha_u)^{t}.$$
--
--   **Formalization Note** This is the printed formula. The paper also writes $\boldsymbol f(v)=\Phi\boldsymbol a^\pm_v$, which by (2) is the negative of the formula; nothing depends on the global sign. Using `Sym2` for pairs makes $\boldsymbol r$ symmetric, as the public coins require.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Theorem 5, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_PunctSketch_sgn

namespace PunctSketch

open Classical in
/-- **The fingerprint sketch.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Theorem 5, p.13:
`𝒇(v)_t = Σ_{u∈N(v)} sgn(v − u) 𝒓_{v,u} (α_u)^t`, with one public field element `𝒓_{v,u}` per unordered
pair, so that `v` and `u` use the same value.

**Formalization Note.** Defined by the printed formula. The paper also calls this `Φ𝒂±_v`, which
with (2) is the negative of the formula; nothing depends on the global sign. Pairs are `Sym2 (Fin n)`,
which makes `𝒓` symmetric by construction. -/
noncomputable def fingerprint {n Q : ℕ} (G : SimpleGraph (Fin n)) (α : Fin n → ZMod Q)
    (r : Sym2 (Fin n) → ZMod Q) (v : Fin n) (t : ℕ) : ZMod Q :=
  ∑ u ∈ Finset.univ.filter (G.Adj v), ((sgn v u : ℤ) : ZMod Q) * r s(v, u) * α u ^ t

end PunctSketch


