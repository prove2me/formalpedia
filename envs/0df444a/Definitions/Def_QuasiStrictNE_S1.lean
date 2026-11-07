-- Prove2me | Definitions.Def_QuasiStrictNE_S1
-- name    : QuasiStrictNE_S1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:37.075357+00:00
-- url     : https://prove2.me/theorems/c431d0a8-451d-4ca5-830a-d5fa22fcbee2
-- title:
--   The simplicial map $S_1$
-- statement:
--   The map $S_1:\Delta_m\to\Delta_m$ is the simplicial map of $K(\mathcal C_m,p)$ or $K(\mathcal C_n,q)$ induced by the vertex map
--   $$
--   S_1(p_F)=\ell_m(\mathrm{supp}(p_F))
--   $$
--   (equation (2)), extended affinely in barycentric coordinates over every simplex.
--
--   **Formalization Note** The selections $p,q$ of relative-interior points are arguments. The extension is `simplicialExt`; its well-definedness and continuity are a milestone.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, (2), p.11

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_ell
import Definitions.Def_QuasiStrictNE_simplicialExt

namespace QuasiStrictNE

/-- **The simplicial map `S1`** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5, (2), p.11: "S1(pF) = ℓm(supp(pF))", extended to
"Δm → Δm").

On the vertex `p F` of `K(Cm, p)` (one for every face `F ∈ Cm`), `S1` takes the value
`ell m (supp (p F))`; on each simplex of `K(Cm, p)` it is extended affinely in barycentric coordinates
(`simplicialExt`).

**Formalization Note** The selection `p` of relative-interior points (paper (1), p.10) is an
argument; the theorems that use `S1` assume `p F ∈ intrinsicInterior ℝ F` for `F ∈ Cm`. The vertex
map is indexed by the face `F` rather than by the point `p F`, which is the same map since
distinct faces have distinct relative-interior points. -/
noncomputable def S1 {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (p : Set (Fin m → ℝ) → (Fin m → ℝ)) :
    (Fin m → ℝ) → (Fin m → ℝ) :=
  simplicialExt (Cm B) p (fun F => ell m (supp (p F)))

end QuasiStrictNE


