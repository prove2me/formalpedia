-- Prove2me | Definitions.Def_HopRamsey_truncateLabels
-- name    : HopRamsey_truncateLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:11.211978+00:00
-- url     : https://prove2.me/theorems/dd5ef81f-4fad-44c8-9577-a1e3a9f763f2
-- title:
--   Replacing the labels above a threshold by $\infty$
-- statement:
--   Given an HST $U'$ and a threshold $\theta\in[0,\infty]$, the HST $U$ is obtained by replacing every label $l>\theta$ by $\infty$: on the leaves, $d_U(u,v)=\infty$ if $d_{U'}(u,v)>\theta$ and $d_U(u,v)=d_{U'}(u,v)$ otherwise. The result is again an HST with the same leaves. In §4.4 the threshold is $\theta=\omega/2$, which separates vertices at infinite $h$-hop distance in $G$.
--
--   **Formalization Note** The construction acts on the leaf ultrametric; the HST axioms of the result are proved in the definition.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §4.4, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ARTreeCover_HST

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- The HST obtained from `U′` by replacing every label `l > θ` by `∞`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §4.4, p.25
(PDF p.27): "we create a new HST U from U′ by replacing each label l such that l > ρ·Φ′ = ω/2 by
∞."

**Formalization Note.** On the leaf ultrametric `ρ_{U′}` this replaces every value `> θ` by `∞`;
the result is again an ultrametric with the same leaves (proved in the structure fields). In §4.4
the threshold is `θ = ω/2`. -/
noncomputable def truncateLabels {V : Type} (U : HST V) (θ : ℝ≥0∞) : HST V where
  leaves := U.leaves
  ρ := fun u v => if θ < U.ρ u v then ⊤ else U.ρ u v
  self := by
    intro x hx
    simp [U.self x hx]
  symm := by
    intro x y
    simp only [U.symm x y]
  ultra := by
    intro x hx y hy z hz
    have hu := U.ultra x hx y hy z hz
    by_cases hxz : θ < U.ρ x z
    · simp only [hxz, if_true]
      have : θ < max (U.ρ x y) (U.ρ y z) := lt_of_lt_of_le hxz hu
      rcases lt_max_iff.1 this with h1 | h1
      · simp [h1]
      · simp [h1]
    · simp only [hxz, if_false]
      refine le_trans hu (max_le_max ?_ ?_)
      · split_ifs <;> simp
      · split_ifs <;> simp
  off := by
    intro u v huv
    simp [U.off u v huv]

end HopRamsey


