-- Prove2me | Definitions.Def_FoundationsML_Stability_SigmaAdmissible
-- name    : FoundationsML_Stability_SigmaAdmissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:21:58.136831+00:00
-- url     : https://prove2.me/theorems/0b06cdff-2948-4b17-bc11-5fa47a46605c
-- title:
--   Sigma-admissibility (Definition 14.3)
-- statement:
--   **Definition 14.3 (σ-admissibility), p. 337, PDF p. 354.** A loss function $L$ is
--   $\sigma$-admissible with respect to a hypothesis class $H$ if there exists $\sigma\in
--   \mathbb R_+$ such that for any two hypotheses $h,h'\in H$ and for all $(x,y)\in X\times Y$,
--   $|L(h'(x),y) - L(h(x),y)| \le \sigma|h'(x)-h(x)|$.
--
--   **Formalization Note.** `Hyp` stands for the hypothesis space itself (the book quantifies
--   over "any two hypotheses $h,h'\in H$", the whole RKHS, not a further subset); `ev : Hyp → X
--   → ℝ` is the evaluation map, the same structural device as `IsRKHSOf`'s `ev`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 337, Definition 14.3 (PDF p. 354)

import Mathlib

namespace FoundationsML.Stability

/-- Definition 14.3 (σ-admissibility; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 337, PDF p. 354). A loss function `L` is σ-admissible
(with respect to a hypothesis type whose elements are evaluated by `ev`) if for any two
hypotheses `h, h'` and for all `(x, y)`, `|L(h'(x), y) − L(h(x), y)| ≤ σ|h'(x) − h(x)|`.

**Formalization Note.** `Hyp` stands for the hypothesis space (the book's RKHS `H`, whose
elements are the hypotheses `h` themselves — Definition 14.3 quantifies over "any two
hypotheses `h, h' ∈ H`", the whole space, not a further subset); `ev : Hyp → X → ℝ` is the
evaluation map, the same structural device as `IsRKHSOf`'s `ev`. -/
def SigmaAdmissible {X Y Hyp : Type*} (ev : Hyp → X → ℝ) (L : ℝ → Y → ℝ) (σ : ℝ) : Prop :=
  ∀ h h' : Hyp, ∀ x : X, ∀ y : Y, |L (ev h' x) y - L (ev h x) y| ≤ σ * |ev h' x - ev h x|

end FoundationsML.Stability


