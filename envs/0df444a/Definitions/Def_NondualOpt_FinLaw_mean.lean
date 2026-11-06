-- Prove2me | Definitions.Def_NondualOpt_FinLaw_mean
-- name    : NondualOpt_FinLaw_mean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:31.772206+00:00
-- url     : https://prove2.me/theorems/a9e68414-a608-4be4-9811-dc1bacc5ab77
-- title:
--   Mean of a real function under a finitely supported law
-- statement:
--   For a finitely supported law $\mu$ and $\varphi:\alpha\to\mathbb R$,
--   $$
--   \int\varphi\,d\mu=\sum_{a\in\operatorname{supp}\mu}\mu(a)\,\varphi(a).
--   $$
--   For $\varphi=\ell(u)$ and $\mu=r_t(\cdot\mid\ell_{1:t-1})$ this is the conditional mean loss $m_t(u)$ of Proposition 4.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 4, p.10

import Mathlib
import Definitions.Def_NondualOpt_FinLaw

namespace NondualOpt

/-- The mean `∫ φ dμ = ∑_a μ(a) φ(a)` of a real function under a finitely supported law; for
`φ = ℓ(u)` this is the conditional mean loss `m_t(u) = ∫ ℓ(u) r_t(dℓ | ℓ_{1:t−1})`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 4, p.10. -/
noncomputable def FinLaw.mean {α : Type*} {S : Set α} (μ : FinLaw S) (φ : α → ℝ) : ℝ :=
  ∑ a ∈ μ.w.support, μ.w a * φ a

end NondualOpt


