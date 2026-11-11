-- Prove2me | Definitions.Def_QNoiseStab_eventSet
-- name    : QNoiseStab_eventSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:45.554213+00:00
-- url     : https://prove2.me/theorems/16b7bf16-3e0c-4001-a4af-96d97e66f39f
-- title:
--   The event $E_y=\{x\in X^n\setminus E_{\mathrm{free}}:(x,y)\in R\}$
-- statement:
--   Let $R\subseteq X^n\times\hat Y$ be a relation, $E_{\mathrm{free}}\subseteq X^n$ a set of inputs given away for free, and $y\in\hat Y$. The event of Theorem 3.5 is
--
--   $$
--   E_y=\{\,x\in X^n\setminus E_{\mathrm{free}} : (x,y)\in R\,\},
--   $$
--
--   the inputs outside $E_{\mathrm{free}}$ on which $y$ is a correct answer. The noise-stability bound is taken over these events, with $E_y$ itself as the target event.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.5, p.13 (definition of E_y)

import Mathlib

namespace QNoiseStab

open Classical in
/-- The event `E_y` of Theorem 3.5 (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), p.13: "for every y ∈ Ŷ, define Ey to be the set of
x ∈ Xⁿ \ Efree such that (x, y) ∈ R"): the inputs outside `E_free` for which `y` is a correct
output. -/
noncomputable def eventSet {X Ŷ : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (Efree : Finset (Fin n → X)) (R : Set ((Fin n → X) × Ŷ)) (y : Ŷ) : Finset (Fin n → X) :=
  Finset.univ.filter fun x => x ∉ Efree ∧ (x, y) ∈ R

end QNoiseStab


