-- Prove2me | Definitions.Def_CompDesignBFM_IsXOS
-- name    : CompDesignBFM_IsXOS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:31.532713+00:00
-- url     : https://prove2.me/theorems/2ed0c112-1e5b-48fb-85a2-28e8c43a1d24
-- title:
--   XOS (fractionally subadditive) set function
-- statement:
--   A set function $v$ is **XOS** if there is a finite family $I$ of additive clauses with
--
--   $$v(S)=\max_{a\in I}\sum_{i\in S}a_i\quad\text{for every } S\subseteq N.$$
--
--   The class sits between submodular and subadditive functions.
--
--   **Formalization Note** Coefficients are real, of any sign, as on p.1 (additive means $v_i\in\mathbb R$), so nonmonotone XOS functions are covered. The family is nonempty because a maximum is attained, and $v(\emptyset)=0$ follows from the empty sum.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.1, p.1 (PDF 3)

import Mathlib

namespace CompDesignBFM

/-- An XOS set function (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.1, p.1, PDF 3): there is a finite family `I` of additive
clauses with `v S = max_(a ∈ I) ∑ i ∈ S, a i` for every `S`.
**Formalization Note.** Clause coefficients are real, of any sign, as on p.1, so nonmonotone XOS
functions are covered. `IsGreatest` makes `I` nonempty and leaves no junk value; it gives `v ∅ = 0` from
the empty sum. -/
def IsXOS {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∃ I : Finset (Fin n → ℝ), ∀ S : Finset (Fin n),
    IsGreatest ((fun a : Fin n → ℝ => ∑ i ∈ S, a i) '' (I : Set (Fin n → ℝ))) (v S)

end CompDesignBFM


