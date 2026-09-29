-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator
-- name    : FoundationsML_ReinforcementLearning_BellmanOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:35:44.642975+00:00
-- url     : https://prove2.me/theorems/c6318c97-383e-4420-8438-e6446715714d
-- title:
--   Bellman optimality operator (eq. 17.8)
-- statement:
--   **§17.4.1 (Value iteration), p. 387, PDF p. 404, eq. (17.8).** For a vector $V\in\mathbb
--   R^{|S|}$, the mapping $\Phi:\mathbb R^{|S|}\to\mathbb R^{|S|}$ based on Bellman's equations
--   (17.4) is defined by
--   $$[\Phi(V)](s) = \max_{a\in A}\Big\{\mathbb E[r(s,a)] + \gamma\sum_{s'\in S} P[s'\mid s,a]
--     V(s')\Big\}, \qquad \forall s\in S.$$
--
--   **Formalization Note.** `hA : (Finset.univ : Finset A).Nonempty` supplies the finite,
--   nonempty action set the book's `max_{a∈A}` needs to be well-defined, realized as
--   `Finset.sup'`: `BellmanOperator hA P Er γ V s = Finset.univ.sup' hA (fun a => Er s a + γ *
--   ∑_{s'} P s a s' * V s')`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 387, eq. (17.8) (PDF p. 404)

import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- The Bellman optimality operator `Φ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, (17.8), p. 387, PDF p. 404):
`[Φ(V)](s) = max_{a∈A} { E[r(s,a)] + γ ∑_{s'} P[s'|s,a] V(s') }`.

**Formalization Note.** `hA : (Finset.univ : Finset A).Nonempty` supplies the finite,
nonempty action set the book's `max_{a∈A}` needs to be well-defined (`Finset.sup'`). -/
noncomputable def BellmanOperator {S A : Type*} [Fintype S] [Fintype A]
    (hA : (Finset.univ : Finset A).Nonempty)
    (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (V : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' hA (fun a : A => Er s a + γ * ∑ s' : S, P s a s' * V s')

end FoundationsML.ReinforcementLearning


