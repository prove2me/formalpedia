-- Prove2me | Definitions.Def_QuasiStrictNE_S2
-- name    : QuasiStrictNE_S2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:46.850968+00:00
-- url     : https://prove2.me/theorems/92de053d-08a7-4aba-9fe4-6bd36783a333
-- title:
--   The simplicial map $S_2$
-- statement:
--   The map $S_2:\Delta_n\to\Delta_n$ is the simplicial map of $K(\mathcal C_m,p)$ or $K(\mathcal C_n,q)$ induced by the vertex map
--   $$
--   S_2(q_G)=\ell_n(\mathrm{supp}(q_G))
--   $$
--   (equation (2)), extended affinely in barycentric coordinates over every simplex.
--
--   **Formalization Note** The selections $p,q$ of relative-interior points are arguments. The extension is `simplicialExt`; its well-definedness and continuity are a milestone.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, (2), p.11

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_Cn
import Definitions.Def_QuasiStrictNE_ell
import Definitions.Def_QuasiStrictNE_simplicialExt

namespace QuasiStrictNE

/-- **The simplicial map `S2`** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5, (2), p.11: "S2(qG) = ℓn(supp(qG))", extended to
"Δn → Δn").

On the vertex `q G` of `K(Cn, q)` (one for every face `G ∈ Cn`), `S2` takes the value
`ell n (supp (q G))`; on each simplex of `K(Cn, q)` it is extended affinely in barycentric coordinates
(`simplicialExt`).

**Formalization Note** The selection `q` of relative-interior points (paper (1), p.10) is an
argument; the theorems that use `S2` assume `q G ∈ intrinsicInterior ℝ G` for `G ∈ Cn`. The vertex
map is indexed by the face `G` rather than by the point `q G`, which is the same map since
distinct faces have distinct relative-interior points. -/
noncomputable def S2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (q : Set (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  simplicialExt (Cn A) q (fun G => ell n (supp (q G)))

end QuasiStrictNE


