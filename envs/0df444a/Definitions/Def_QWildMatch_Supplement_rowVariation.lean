-- Prove2me | Definitions.Def_QWildMatch_Supplement_rowVariation
-- name    : QWildMatch_Supplement_rowVariation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:19:30.620605+00:00
-- url     : https://prove2.me/theorems/240c0d91-e379-4ccf-84d8-501a0a7b35cf
-- title:
--   Substitution-cost-row variation $V_\Gamma(A)$
-- statement:
--   Let $A=A[0]\cdots A[H-1]$ be a pattern over $\Sigma\cup\{\star\}$, $\mu$ a substitution-cost function and $\Gamma\ge1$ a stride. The **substitution-cost-row variation** of $A$ at stride $\Gamma$ is
--   $$V_\Gamma(A)=\#\Big\{r\in\{\Gamma,\dots,H-1\}:\ \exists\,b,c\in\Sigma,\ \mu(A[r],b)-\mu(A[r],c)\ne\mu(A[r-\Gamma],b)-\mu(A[r-\Gamma],c)\Big\}.$$
--   When $\Gamma\ge H$ the set is empty and $V_\Gamma(A)=0$.
--
--   It measures how often the cost rows of the pattern change, up to an additive constant, between offsets $\Gamma$ apart, and it is the parameter of the regime bound of Theorem 5.1.
--
--   **Formalization Note** The pattern is a function on $\mathbb N$ of which only the values at $0,\dots,H-1$ are read; $\mu$ is any real function.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), §5, p.6 (definition of V_Γ(A))

import Mathlib

namespace QWildMatch.Supplement

open Classical in
/-- The substitution-cost-row variation `V_Γ(A)` of a length-`H` pattern at stride `Γ` (Zhao, Chen, Li, Kong,
Peng, Yu, Yue, STOC 2027 submission (file sha256 9e87a9dd…), §5, p.6): the number of offsets
`r ∈ {Γ, …, H − 1}` for which some text symbols `b, c` give
`μ(A[r], b) − μ(A[r], c) ≠ μ(A[r − Γ], b) − μ(A[r − Γ], c)`. It is `0` when `Γ ≥ H`.

**Formalization Note** The pattern is a function `A : ℕ → Option Sym` read on `0, …, H − 1` (`none` is the
wildcard `⋆`); its values at `r ≥ H` never enter. The substitution cost `μ` is an arbitrary real function. -/
noncomputable def rowVariation {Sym : Type} (μ : Option Sym → Sym → ℝ) (A : ℕ → Option Sym)
    (H Γ : ℕ) : ℕ :=
  ((Finset.Ico Γ H).filter fun r =>
    ∃ b c : Sym, μ (A r) b - μ (A r) c ≠ μ (A (r - Γ)) b - μ (A (r - Γ)) c).card

end QWildMatch.Supplement


