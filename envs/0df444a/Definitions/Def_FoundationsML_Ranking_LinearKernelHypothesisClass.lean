-- Prove2me | Definitions.Def_FoundationsML_Ranking_LinearKernelHypothesisClass
-- name    : FoundationsML_Ranking_LinearKernelHypothesisClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:39:11.076298+00:00
-- url     : https://prove2.me/theorems/c7a7114f-d956-45e2-9130-97700357e638
-- title:
--   Kernel-based linear scoring hypothesis class
-- statement:
--   **p. 243, PDF p. 260.** $H = \{x\mapsto w\cdot\Phi(x) : \|w\|_H\le\Lambda\}$ for a feature
--   map $\Phi:X\to H_b$ and norm bound $\Lambda$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 243 (PDF p. 260)

import Mathlib

namespace FoundationsML.Ranking

/-- The family of kernel-based linear scoring hypotheses with feature map `Φ : X → Hb` and
norm bound `Λ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 243, PDF p. 260): `H = {x ↦ w·Φ(x) : ‖w‖_H ≤ Λ}`. -/
def LinearKernelHypothesisClass {X Hb : Type*} [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (Φ : X → Hb) (Λ : ℝ) : Set (X → ℝ) :=
  {h | ∃ w : Hb, ‖w‖ ≤ Λ ∧ h = fun x => (inner (𝕜 := ℝ) w (Φ x) : ℝ)}

end FoundationsML.Ranking


