-- Prove2me | Definitions.Def_QuasiStrictNE_R1
-- name    : QuasiStrictNE_R1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:31.860998+00:00
-- url     : https://prove2.me/theorems/e2eca96e-9885-4fc6-a805-2b314cada5de
-- title:
--   The simplicial map $R_1$
-- statement:
--   The map $R_1:\Delta_n\to\Delta_m$ is the simplicial map of $K(\mathcal C_m,p)$ or $K(\mathcal C_n,q)$ induced by the vertex map
--   $$
--   R_1(q_G)=\ell_m(BR_1(q_G))
--   $$
--   (equation (2)), extended affinely in barycentric coordinates over every simplex.
--
--   **Formalization Note** The selections $p,q$ of relative-interior points are arguments. The extension is `simplicialExt`; its well-definedness and continuity are a milestone.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, (2), p.11

import Mathlib
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_Cn
import Definitions.Def_QuasiStrictNE_ell
import Definitions.Def_QuasiStrictNE_simplicialExt

namespace QuasiStrictNE

/-- **The simplicial map `R1`** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5, (2), p.11: "R1(qG) = ℓm(BR1(qG))", extended to
"Δn → Δm").

On the vertex `q G` of `K(Cn, q)` (one for every face `G ∈ Cn`), `R1` takes the value
`ell m (BR1 A (q G))`; on each simplex of `K(Cn, q)` it is extended affinely in barycentric coordinates
(`simplicialExt`).

**Formalization Note** The selection `q` of relative-interior points (paper (1), p.10) is an
argument; the theorems that use `R1` assume `q G ∈ intrinsicInterior ℝ G` for `G ∈ Cn`. The vertex
map is indexed by the face `G` rather than by the point `q G`, which is the same map since
distinct faces have distinct relative-interior points. -/
noncomputable def R1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (q : Set (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin n → ℝ) → (Fin m → ℝ) :=
  simplicialExt (Cn A) q (fun G => ell m (BR1 A (q G)))

end QuasiStrictNE


