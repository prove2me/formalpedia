-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_TD
-- name    : CatalystQLB_Query_Supplement_TD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:56:41.837194+00:00
-- url     : https://prove2.me/theorems/dfcffef5-c712-43b4-aecf-fc3bf4b16cae
-- title:
--   Trace distance $\mathrm{TD}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$
-- statement:
--   For square matrices $\rho,\sigma$ of the same size, the **trace distance** is
--   $$\mathrm{TD}(\rho,\sigma) := \tfrac12\,\|\rho-\sigma\|_1,$$
--   where $\|M\|_1=\mathrm{tr}\sqrt{M^\dagger M}$ is the trace norm. For pure states, $\mathrm{TD}(|a\rangle\langle a|,|b\rangle\langle b|)=\sqrt{1-|\langle a|b\rangle|^2}$.
--
--   Every error parameter of the supplement ($\varepsilon$ in the catalytic conditions, the bounds $3\varepsilon^2/2$ and $18\varepsilon$) is measured in this halved distance.
--
--   **Formalization Note** The published `WildeQIT.traceDist` is $\|\rho-\sigma\|_1$ without the factor $\tfrac12$; `TD` divides it by $2$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Notation 9, p.17 (PDF 20)

import Mathlib
import Definitions.Def_WildeQIT_traceDist

namespace CatalystQLB.Query.Supplement

/-- The **trace distance** `TD(ρ, σ) := ½ ‖ρ − σ‖₁` (Arora, Chakraborty, Cojocaru, Saminathan,
Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Notation 9, p.17 (PDF 20)).

**Formalization Note** `WildeQIT.traceDist ρ σ = ‖ρ − σ‖₁` (published, Wilde Def. 9.1.2) has no
factor `½`; the paper's `TD` is half of it. Every bound of the supplement (`ε` in the catalytic
condition, `3ε²/2`, `18ε`) is in this halved distance, which for pure states equals
`√(1 − |⟨a|b⟩|²)`. -/
noncomputable def TD {m : Type} [Fintype m] [DecidableEq m] (ρ σ : Matrix m m ℂ) : ℝ :=
  WildeQIT.traceDist ρ σ / 2

end CatalystQLB.Query.Supplement


