-- Prove2me | Definitions.Def_QuasiStrictNE_R2
-- name    : QuasiStrictNE_R2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:28.134198+00:00
-- url     : https://prove2.me/theorems/1f1b63ec-0ebf-4083-b29f-6eabad06a31a
-- title:
--   The simplicial map $R_2$
-- statement:
--   The map $R_2:\Delta_m\to\Delta_n$ is the simplicial map of $K(\mathcal C_m,p)$ or $K(\mathcal C_n,q)$ induced by the vertex map
--   $$
--   R_2(p_F)=\ell_n(BR_2(p_F))
--   $$
--   (equation (2)), extended affinely in barycentric coordinates over every simplex.
--
--   **Formalization Note** The selections $p,q$ of relative-interior points are arguments. The extension is `simplicialExt`; its well-definedness and continuity are a milestone.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, (2), p.11

import Mathlib
import Definitions.Def_QuasiStrictNE_BR2
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_ell
import Definitions.Def_QuasiStrictNE_simplicialExt

namespace QuasiStrictNE

/-- **The simplicial map `R2`** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5, (2), p.11: "R2(pF) = ℓn(BR2(pF))", extended to
"Δm → Δn").

On the vertex `p F` of `K(Cm, p)` (one for every face `F ∈ Cm`), `R2` takes the value
`ell n (BR2 B (p F))`; on each simplex of `K(Cm, p)` it is extended affinely in barycentric coordinates
(`simplicialExt`).

**Formalization Note** The selection `p` of relative-interior points (paper (1), p.10) is an
argument; the theorems that use `R2` assume `p F ∈ intrinsicInterior ℝ F` for `F ∈ Cm`. The vertex
map is indexed by the face `F` rather than by the point `p F`, which is the same map since
distinct faces have distinct relative-interior points. -/
noncomputable def R2 {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (p : Set (Fin m → ℝ) → (Fin m → ℝ)) :
    (Fin m → ℝ) → (Fin n → ℝ) :=
  simplicialExt (Cm B) p (fun F => ell n (BR2 B (p F)))

end QuasiStrictNE


