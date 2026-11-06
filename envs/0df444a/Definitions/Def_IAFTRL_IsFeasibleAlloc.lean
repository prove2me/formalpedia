-- Prove2me | Definitions.Def_IAFTRL_IsFeasibleAlloc
-- name    : IAFTRL_IsFeasibleAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:44.060017+00:00
-- url     : https://prove2.me/theorems/ad54563d-02a5-42d4-8759-2549e5332ccb
-- title:
--   Feasible sampling allocation of (1.2)
-- statement:
--   Let $\theta\in\mathbb R^d$ with optimal action $a^*$ and loss gaps $\Delta(a)=(a-a^*)^\top\theta$. A vector $n\in\mathbb R^{\mathcal A}$ is a **(feasible) sampling allocation** if
--   1. $n_a\ge 0$ for every action $a$;
--   2. the design matrix $H_n=\sum_{a\in\mathcal A}n_a\,aa^\top$ is positive definite;
--   3. for every $a\ne a^*$,
--   $$
--   \|a\|^2_{H_n^{-1}}=a^\top H_n^{-1}a\le\frac{\Delta(a)^2}{2}.
--   $$
--
--   These are the constraints of the program (1.2) that defines the information-acquisition complexity $c^*(\mathcal A,\theta)$. Proposition 2.1 bounds the regret of IA-FTRL in terms of the cost of any such allocation.
--
--   **Formalization Note** $H_n$ is the published `BanditAlgorithm.linearAllocationMatrix arms n`. Positive definiteness is part of (1.2); it also excludes the junk inverse $0$ that Lean assigns to singular matrices.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, p.6, Eq. (1.2)

import Mathlib
import Definitions.Def_LinearBanditProtocol

namespace IAFTRL

open Matrix

/-- **Sampling allocation (feasibility in (1.2)).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.6, Eq. (1.2):
"`c*(𝒜, θ) = inf_{n∈ℝ^𝒜_{≥0}} { c^n(𝒜, θ) : H_n = Σ_a n_a a a^⊤ ≻ 0, ‖a‖²_{H_n^{-1}} ≤ Δ(a)²/2,
∀a ≠ a* }` … we call `n ∈ ℝ^𝒜_{≥0}` a sampling allocation if `n` satisfies the feasibility condition
in (1.2)".

`IsFeasibleAlloc arms θ jstar n` says: `n ≥ 0`; the design matrix `H_n = Σ_j n_j a_j a_j^⊤` is
positive definite; and `a_j^⊤ H_n^{-1} a_j ≤ Δ(a_j)²/2` for every `j ≠ jstar`, where
`Δ(a_j) = (a_j − a_{jstar})^⊤θ` is the loss gap of p.6.

**Formalization Note.** `H_n` is the published `BanditAlgorithm.linearAllocationMatrix arms n`.
Positive definiteness is part of (1.2); it also rules out Mathlib's junk inverse `0` of a
singular matrix. -/
def IsFeasibleAlloc {d K : ℕ} (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar : Fin K)
    (n : Fin K → ℝ) : Prop :=
  (∀ j, 0 ≤ n j) ∧ (BanditAlgorithm.linearAllocationMatrix arms n).PosDef ∧
    ∀ j, j ≠ jstar →
      arms j ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms n)⁻¹ *ᵥ arms j ≤
        ((arms j - arms jstar) ⬝ᵥ θ) ^ 2 / 2

end IAFTRL


