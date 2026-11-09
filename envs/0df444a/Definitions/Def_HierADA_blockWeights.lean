-- Prove2me | Definitions.Def_HierADA_blockWeights
-- name    : HierADA_blockWeights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:00:40.918583+00:00
-- url     : https://prove2.me/theorems/377f5e4d-d72b-4dc9-a7a9-96ab0264265d
-- title:
--   Current weights $w_j$ of every block
-- statement:
--   Given the score vectors $G$, block $j$ has weights
--
--   $$
--   w_j=\begin{cases} w(G_j)\ \text{(Equation (2))} & \text{for a learned block } j<p,\\[2pt] \big(\frac1{n_p},\dots,\frac1{n_p}\big) & \text{for the anchor } j=p .\end{cases}
--   $$
--
--   The anchor is "the last block $S_p$, whose weights shall remain uniform throughout the course of the queries".
--
--   **Formalization Note** 0-based: the anchor is the block with index $p-1$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Algorithm 1 and Equation (2), pp.13–14

import Mathlib
import Definitions.Def_HierADA_regWeights

set_option autoImplicit false

namespace HierADA

/-- **The current weights of every block** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data
Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03,
sha256 f220ae51…), Algorithm 1 and Equation (2), pp.13–14.

A learned block `j` (with `j + 1 < p`) has the weights `w(G_j)` of Equation (2) computed from its
score vector; the anchor (the last block, `j + 1 = p`) keeps the uniform weights `1/n_p`
("the last block S_p … whose weights shall remain uniform", p.13). Initially all scores are `0`, and
`w(0)` is uniform. -/
noncomputable def blockWeights (τ : ℝ) {p : ℕ} (n : Fin p → ℕ)
    (G : (j : Fin p) → Fin (n j) → ℝ) (j : Fin p) : Fin (n j) → ℝ :=
  if j.val + 1 = p then fun _ => 1 / (n j : ℝ) else regWeights τ (n j) (G j)

end HierADA


