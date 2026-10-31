-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsDerivProblemSolution
-- name    : RBMSensitivity_Data_IsDerivProblemSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:09.79998+00:00
-- url     : https://prove2.me/theorems/f2c5b9cf-1598-4906-9858-24b27ee52cd7
-- title:
--   Definition 4.11: solution of the derivative problem
-- statement:
--   Given $f\in\mathbb C_G(\mathbb R^J)$, suppose $(h,g)$ is a solution to the SP for $f$. Let $\psi\in\mathbb D(\mathbb R^J)$. Then $(\phi,\eta)\in\mathbb D(\mathbb R^J)\times\mathbb D(\mathbb R^J)$ is a **solution to the derivative problem along $h$ for $\psi$** if $\eta(0)\in\mathrm{span}[d(\alpha,h(0))]$ and if for all $t\ge 0$:
--
--   1. $\phi(t)=\psi(t)+\eta(t)$;
--   2. $\phi(t)\in\mathbb H_{h(t)}$;
--   3. for all $s\in[0,t)$, $\eta(t)-\eta(s)\in\mathrm{span}\big[\bigcup_{u\in(s,t]}d(\alpha,h(u))\big]$.
--
--   It is the linearization of the Skorokhod problem along $h$, and a derivative process is a pathwise solution of it.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 4.11, p.13

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_RBMSensitivity_Data_dSpan
import Definitions.Def_RBMSensitivity_Data_spanAlong
import Definitions.Def_RBMSensitivity_SimpleCone_H
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Definition 4.11: arXiv:1907.00472v2, p.13. For `ψ ∈ D(ℝ^J)`, `(φ, η) ∈ D(ℝ^J) × D(ℝ^J)` solves the
derivative problem along `h` for `ψ` if `η(0) ∈ span[d(α, h(0))]` and for all `t ≥ 0`:
`φ(t) = ψ(t) + η(t)`; `φ(t) ∈ H_{h(t)}`; and for all `s ∈ [0, t)`,
`η(t) - η(s) ∈ span[⋃_{u ∈ (s,t]} d(α, h(u))]`.

**Formalization Note.** That `(h, g)` solves the SP is a separate hypothesis wherever this is used. -/
structure Data.IsDerivProblemSolution {J : ℕ} (D : Data J) (α : ℝ) (h ψ φ η : ℝ≥0 → E J) :
    Prop where
  ψ_rcll : IsRCLL ψ
  φ_rcll : IsRCLL φ
  η_rcll : IsRCLL η
  η_zero : η 0 ∈ D.dSpan α (h 0)
  eq : ∀ t, φ t = ψ t + η t
  mem : ∀ t, φ t ∈ D.H (h t)
  increment : ∀ s t, s < t → η t - η s ∈ D.spanAlong α h s t

end RBMSensitivity


