-- Prove2me | Definitions.Def_QuasiStrictNE_KCp
-- name    : QuasiStrictNE_KCp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:56.09325+00:00
-- url     : https://prove2.me/theorems/a9fd889d-7cc1-4342-963c-e912bd6b7375
-- title:
--   The order-complex realisation $K(C,p)$
-- statement:
--   Let $C$ be a polyhedral complex and, for every $F\in C$, let $p_F\in\mathrm{relint}\,F$ be a selected point (the same point whenever $F$ occurs). The collection
--   $$
--   K(C,p)=\{\mathrm{conv}\{p_{F_0},\dots,p_{F_r}\} : F_0\subsetneq\cdots\subsetneq F_r,\ F_i\in C,\ r\ge 0\}
--   $$
--   realises the order complex of the face poset of $C$ geometrically.
--
--   **Formalization Note** A simplex is recorded by its vertex set $\{p_{F_0},\dots,p_{F_r}\}$, as in Mathlib's `Geometry.SimplicialComplex`. The selection $p$ is an argument; $p_F\in\mathrm{relint}\,F$ is a hypothesis of the theorems.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), p.6

import Mathlib
import Definitions.Def_QuasiStrictNE_IsFaceChain

namespace QuasiStrictNE

open Classical in
/-- **The order-complex realisation `K(C, p)`** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, p.6: "For each face F ∈ C, fix a single
point pF ∈ relint F. … Set K(C, p) = {conv{pF0, . . . , pFr} : F0 ⊊ · · · ⊊ Fr, Fi ∈ C, r ≥ 0}").

`KCp C p` is the set of vertex sets `{p F₀, …, p F_r}` of the simplices of `K(C, p)`, one for every
chain `F₀ ⊊ ⋯ ⊊ F_r` of members of `C`.

**Formalization Note** A simplex is recorded by its finite vertex set, as in Mathlib's
`Geometry.SimplicialComplex` (the simplex itself is the convex hull). The selection `p` is an
argument; the paper requires `p F ∈ relint F`, which is a hypothesis of the theorems using it. -/
noncomputable def KCp {d : ℕ} (C : Set (Set (Fin d → ℝ))) (p : Set (Fin d → ℝ) → (Fin d → ℝ)) :
    Set (Finset (Fin d → ℝ)) :=
  {τ | ∃ σ : Finset (Set (Fin d → ℝ)), IsFaceChain C σ ∧ τ = σ.image p}

end QuasiStrictNE


