-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_moreauYosida
-- name    : KuhnWass2019_Reformulation_moreauYosida
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:14:33.598875+00:00
-- url     : https://prove2.me/theorems/cd389ba8-2f50-499f-8ceb-5cb5a8b5e81d
-- title:
--   Extended-real Moreau–Yosida regularization
-- statement:
--   The regularized loss is $\ell_\gamma(x)=\sup_{z\in\Xi}\{\ell(z)-\gamma\|z-x\|^p\}$. Both the input loss and the result are extended-real-valued. The empty supremum is $-\infty$ and an unbounded-above supremum is $+\infty$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 10, Theorem 7, equation (10)

import Mathlib

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Theorem 7, equation (10): regularization of an extended-real loss. -/
noncomputable def moreauYosida {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → EReal) (p γ : ℝ) (x : E) : EReal :=
  ⨆ z ∈ Ξ, ℓ z - ((γ * ‖z - x‖ ^ p : ℝ) : EReal)

end KuhnWass2019.Reformulation


