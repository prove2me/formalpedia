-- Prove2me | Definitions.Def_QuasiStrictNE_labelsQ
-- name    : QuasiStrictNE_labelsQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:17.588205+00:00
-- url     : https://prove2.me/theorems/f829999f-b48a-4c1a-b26a-9b3314836997
-- title:
--   Input of Lemma 3 for a face $G\in\mathcal C_n$
-- statement:
--   For a face $G\in\mathcal C_n$ the label sets are
--   $$
--   I_G=\{j\in N : y_j>0 \text{ for some } y\in G\},\qquad J_G=\{i\in M : G\subseteq Q_i\}.
--   $$
--   The input of Lemma 3 is the code of the game followed by the characteristic bit vectors of $I_G$ (length $n$) and $J_G$ (length $m$).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 3, p.14 ("The same holds for G ∈ Cn")

import Mathlib
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_Qregion

namespace QuasiStrictNE

open Classical in
/-- **The input of Lemma 3 for a face `G ∈ Cn`** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 3, p.14: "The same holds for G ∈ Cn";
the label sets are `I_G = {j ∈ N : yj > 0 for some y ∈ G}` and `J_G = {i ∈ M : G ⊆ Qi}`).

`labelsQ Γ G` is the code of the game `Γ` followed by the characteristic bit vector of `I_G` (length
`n`) and that of `J_G` (length `m`).

**Formalization Note** `Qi` is taken for the real cast of the rational matrix `A`; the game is named
`Γ` here because `G` is the face. -/
noncomputable def labelsQ (Γ : RatGame) (G : Set (Fin Γ.n → ℝ)) : List Bool :=
  Γ.enc ++ List.ofFn (fun j : Fin Γ.n => decide (∃ y ∈ G, 0 < y j)) ++
    List.ofFn (fun i : Fin Γ.m => decide (G ⊆ Qregion (Γ.A.map ((↑) : ℚ → ℝ)) i))

end QuasiStrictNE


