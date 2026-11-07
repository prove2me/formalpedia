-- Prove2me | Definitions.Def_PunctSketch_boundaryFp
-- name    : PunctSketch_boundaryFp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:37.540495+00:00
-- url     : https://prove2.me/theorems/5e8ed33a-b9a1-45fc-8366-c088cd107662
-- title:
--   The fingerprint of a purported boundary
-- statement:
--   For a set $E$ of pairs (a purported boundary or edge set),
--   $$\boldsymbol f(E)_t=\sum_{v\in C}\ \sum_{\substack{u\notin C\cup F\\ \{v,u\}\in E}}\mathrm{sgn}(v-u)\,\boldsymbol r_{\{v,u\}}\,(\alpha_v\alpha_u)^t\,P_F(\alpha_v)\,P_F(\alpha_u).$$
--   The coordinator computes this directly and compares it with the sum of the artificial fingerprints over $C$.
--
--   **Formalization Note** The page prints $a_v,a_u$ inside this display; these are $\alpha_v,\alpha_u$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Lemma 5.1, p.16 (PDF p.17); proof of Theorem 5, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_PunctSketch_puncturePoly
import Definitions.Def_PunctSketch_sgn

namespace PunctSketch

open Classical in
/-- **The fingerprint of a purported boundary.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Lemma 5.1, p.16:
`𝒇_{F,r,l}(𝒃)_t = Σ_{{v,u}: 𝒃_{v,u} ≠ 0, v∈C, u∉C∪F} sgn(v − u) 𝒓_{v,u} (α_v α_u)^t P_F(α_v) P_F(α_u)`,
and p.14 for a purported edge set `E′`. The set `E` holds the pairs with `𝒃_{v,u} ≠ 0`.

**Formalization Note.** `C` is disjoint from `F` wherever this is used, so `v ∉ F` is implicit. The
page prints `(a_v a_u)` and `P_F(a_v)`; these are `α`. -/
noncomputable def boundaryFp {n Q : ℕ} (α : Fin n → ZMod Q) (F C : Finset (Fin n))
    (r : Sym2 (Fin n) → ZMod Q) (E : Set (Sym2 (Fin n))) (t : ℕ) : ZMod Q :=
  ∑ v ∈ C, ∑ u ∈ Finset.univ.filter (fun u => u ∉ C ∧ u ∉ F ∧ s(v, u) ∈ E),
    ((sgn v u : ℤ) : ZMod Q) * r s(v, u) * (α v * α u) ^ t *
      (puncturePoly α F).eval (α v) * (puncturePoly α F).eval (α u)

end PunctSketch


