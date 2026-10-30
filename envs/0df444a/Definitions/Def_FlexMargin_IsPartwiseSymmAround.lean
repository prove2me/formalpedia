-- Prove2me | Definitions.Def_FlexMargin_IsPartwiseSymmAround
-- name    : FlexMargin_IsPartwiseSymmAround
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:22.504354+00:00
-- url     : https://prove2.me/theorems/5bd83353-6953-4249-85aa-e1d7c42a94c6
-- title:
--   Definition 2.2: part-wise independently symmetric around $\mu$
-- statement:
--   An uncertainty set $U\subset\mathbb R^n_+$ is a **part-wise independently symmetric perturbation uncertainty set** (around $\mu\in\mathbb R^n$) if the set of residuals
--
--   $$
--   E=\{d-\mu: d\in U\}
--   $$
--
--   satisfies clauses (1) and (2) of Definition 2.1. Here $\mu$ plays the role of the estimated mean demand and $E$ of the estimation errors, which fluctuate symmetrically within each category.
--
--   **Formalization Note** The centre $\mu$ is an explicit argument; the sign condition applies to $U$, not to $E$.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2.3, Definition 2.2, p. 15

import Mathlib
import Definitions.Def_FlexMargin_IsPartwiseSymmCore

namespace FlexMargin

/-- **Definition 2.2: part-wise independently symmetric perturbation uncertainty set (around μ).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2.3, Definition 2.2, p. 15: "An uncertainty set U ⊂ R^n_+ is a part-wise independently
symmetric perturbation uncertainty set if E := {d − µ | d ∈ U} is part-wise independently symmetric
for some fixed µ."

`IsPartwiseSymmAround cat μ U`: every vector of `U` is nonnegative, and the residual set
`E = {d - μ | d ∈ U}` satisfies clauses (1) and (2) of Definition 2.1
(`FlexMargin.IsPartwiseSymmCore`). The paper also says "U is part-wise independently symmetric
around μ" (Theorem 1, Proposition 3).

**Formalization Note.** The centre `μ` is an explicit argument (the paper's "for some fixed µ";
the existential form is `∃ μ, IsPartwiseSymmAround cat μ U`). `E` is not required to be
nonnegative: residuals may be negative, so the sign clause of Definition 2.1 is applied to `U`,
as the page's "U ⊂ R^n_+" says, and not to `E`. -/
def IsPartwiseSymmAround {n T : ℕ} (cat : Fin n → Fin T) (μ : Fin n → ℝ)
    (U : Set (Fin n → ℝ)) : Prop :=
  (∀ d ∈ U, ∀ i, 0 ≤ d i) ∧ IsPartwiseSymmCore cat {e | ∃ d ∈ U, e = d - μ}

end FlexMargin


