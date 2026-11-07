-- Prove2me | Definitions.Def_LowErrExt_condOn
-- name    : LowErrExt_condOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:27.960604+00:00
-- url     : https://prove2.me/theorems/1d1bd53c-e39b-48ec-9bae-1e8660f10ba0
-- title:
--   Conditioning $\mathbf X|_{\mathbf X\in S}$ and $\Pr[\mathbf X\in S]$
-- statement:
--   For a source $\mathbf X$ on a set $A$ and an event $S\subseteq A$, $\Pr[\mathbf X\in S]$ is the total mass of $S$, and the **conditional source** $\mathbf X|_{\mathbf X\in S}$ has
--   $$\Pr[\mathbf X|_{\mathbf X\in S}=x]=\frac{\Pr[\mathbf X=x]}{\Pr[\mathbf X\in S]}\quad (x\in S),$$
--   and probability $0$ outside $S$. A subsource of deficiency $\ell$ (Definition 2.2) is $\mathbf X|_{\mathbf X\in S}$ for an event with $\Pr[\mathbf X\in S]\ge 2^{-\ell}$.
--
--   **Formalization Note** When $\Pr[\mathbf X\in S]=0$ the conditional law is undefined; the Lean function then returns $\mathbf X$. No statement of the mission conditions on a null event.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 2.2, p.10

import Mathlib

namespace LowErrExt

/-- **Probability of an event.** `probOf X S = Pr[X ∈ S]`, a real number in `[0, 1]`.
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), §2.1, p.10. -/
noncomputable def probOf {α : Type*} (X : PMF α) (S : Set α) : ℝ :=
  (X.toOuterMeasure S).toReal

/-- **Conditioning on an event (subsources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.2, p.10: "X′ := X|X∈X′" and "X′ ⊆ℓ X, if there is some X′ ⊆ supp(X) with
Pr[X ∈ X′] ≥ 2^{−ℓ} such that X′ := X|X∈X′."

`condOn X S` is the law of `X` conditioned on `X ∈ S` (Mathlib's `PMF.filter`).

**Formalization Note.** Lean functions are total: when `Pr[X ∈ S] = 0` the conditional law is
undefined in the paper, and `condOn X S` then returns `X` itself. Every statement of this mission
conditions only on events of positive probability (a subsource of deficiency `ℓ` has mass
`≥ 2^{−ℓ} > 0`, and a fiber `Γ = γ` is used only for `γ` in the support), so this value is never
reached. Conditioning depends only on `S ∩ supp(X)`, so `S` need not be a subset of the support. -/
noncomputable def condOn {α : Type*} (X : PMF α) (S : Set α) : PMF α := by
  classical
  exact if h : ∃ a ∈ S, a ∈ X.support then X.filter S h else X

end LowErrExt


