-- Prove2me | Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass
-- name    : FoundationsML_MultiClass_KernelHypothesisClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:32:15.385451+00:00
-- url     : https://prove2.me/theorems/1668f67a-ad52-4190-8cbd-de3deb1bea50
-- title:
--   Multi-class kernel-based hypothesis class H_{K,p}
-- statement:
--   **p. 219, PDF p. 236.** $H_{K,p} = \{(x,y)\mapsto w_y\cdot\Phi(x) :
--   W=(w_1,\dots,w_k),\ \|W\|_{H,p}\le\Lambda\}$, parameterized by an $L^p$-type group norm
--   across the $k$ classes' weight vectors.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 219 (PDF p. 236)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GroupNormLp

namespace FoundationsML.MultiClass

/-- The family `H_{K,p}` of multi-class kernel-based hypotheses with feature map `Φ : X → Hb`
and group-norm bound `Λ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 219, PDF p. 236):
`H_{K,p} = {(x,y) ↦ w_y · Φ(x) : W = (w_1,…,w_k), ‖W‖_{H,p} ≤ Λ}`. -/
def KernelHypothesisClass {X Hb : Type*} [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (Φ : X → Hb) (k : ℕ) (p Λ : ℝ) : Set (X × Fin k → ℝ) :=
  {h | ∃ W : Fin k → Hb, GroupNormLp p W ≤ Λ ∧
    h = fun xy => (inner (𝕜 := ℝ) (W xy.2) (Φ xy.1) : ℝ)}

end FoundationsML.MultiClass


