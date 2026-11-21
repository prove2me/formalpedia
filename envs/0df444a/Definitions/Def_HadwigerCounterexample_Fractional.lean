-- Prove2me | Definitions.Def_HadwigerCounterexample_Fractional
-- name    : HadwigerCounterexample_Fractional
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T21:54:45.190167+00:00
-- url     : https://prove2.me/theorems/53f14712-288d-43f0-9d80-f3ec1e8334f6
-- title:
--   Fractional chromatic number
-- statement:
--   The **fractional chromatic number** $\chi_f(G)$ of a finite simple graph $G$ is the minimum total weight of a fractional coloring. A fractional coloring assigns a nonnegative real weight $w_I$ to each independent vertex set $I$ so that every vertex is covered to total weight at least one:
--   $$\chi_f(G)=\inf\Big\{\sum_I w_I:\ w_I\ge0,\ \sum_{I\ni v}w_I\ge1\text{ for every vertex }v\Big\}.$$
--   An ordinary coloring gives a fractional coloring with unit weights on its color classes, so $\chi_f(G)\le\chi(G)$; summing the vertex constraints gives $\chi_f(G)\ge|V(G)|/\alpha(G)$. The source preprint (p. 3) uses this quantity to state its fractional-coloring counterexamples (Corollary 1.2).
--
--   **Formalization Note.** Weights are placed on all finite vertex sets (`Finset V`), with non-independent sets forced to weight zero; the infimum is a real-valued `sInf`. This matches the formalization already used on the platform for the Reed–Seymour theorem (`OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger`).
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , p. 3 (definition of fractional coloring and χf(G))

import Mathlib

namespace OAI

namespace HadwigerCounterexample

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The fractional chromatic number: the infimum of the total weight of a
fractional coloring, i.e. nonnegative weights on independent vertex sets covering
each vertex to total at least one. Weights are placed on all finite vertex sets,
with non-independent sets forced to weight zero. -/
noncomputable def fractionalChromaticNumber (G : SimpleGraph V) : ℝ :=
  sInf {c : ℝ | ∃ μ : Finset V → ℝ,
    ((∀ I, 0 ≤ μ I) ∧ (∀ I, ¬(∀ v ∈ I, ∀ u ∈ I, ¬G.Adj v u) → μ I = 0) ∧
      ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0) ∧ ∑ I, μ I = c}

end HadwigerCounterexample

end OAI


