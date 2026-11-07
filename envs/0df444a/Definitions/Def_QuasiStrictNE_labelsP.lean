-- Prove2me | Definitions.Def_QuasiStrictNE_labelsP
-- name    : QuasiStrictNE_labelsP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:23.8008+00:00
-- url     : https://prove2.me/theorems/da9cb37e-e9f6-4b30-a275-2624f9aeb265
-- title:
--   Input of Lemma 3 for a face $F\in\mathcal C_m$
-- statement:
--   For a face $F\in\mathcal C_m$ the label sets are
--   $$
--   I_F=\{i\in M : x_i>0 \text{ for some } x\in F\},\qquad J_F=\{j\in N : F\subseteq P_j\}.
--   $$
--   The input of Lemma 3 is the code of the game followed by the characteristic bit vectors of $I_F$ (length $m$) and $J_F$ (length $n$).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 3, p.14

import Mathlib
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_Pregion

namespace QuasiStrictNE

open Classical in
/-- **The input of Lemma 3 for a face `F ∈ Cm`** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 3, p.14: "For F ∈ Cm, let
IF = {i ∈ M : xi > 0 for some x ∈ F}, JF = {j ∈ N : F ⊆ Pj}. Given these index sets, …").

`labelsP G F` is the code of the game `G` followed by the characteristic bit vector of `I_F` (length
`m`) and that of `J_F` (length `n`).

**Formalization Note** `Pj` is taken for the real cast of the rational matrix `B`. -/
noncomputable def labelsP (G : RatGame) (F : Set (Fin G.m → ℝ)) : List Bool :=
  G.enc ++ List.ofFn (fun i : Fin G.m => decide (∃ x ∈ F, 0 < x i)) ++
    List.ofFn (fun j : Fin G.n => decide (F ⊆ Pregion (G.B.map ((↑) : ℚ → ℝ)) j))

end QuasiStrictNE


