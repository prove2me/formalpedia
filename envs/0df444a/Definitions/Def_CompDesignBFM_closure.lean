-- Prove2me | Definitions.Def_CompDesignBFM_closure
-- name    : CompDesignBFM_closure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:38.24134+00:00
-- url     : https://prove2.me/theorems/d22d32f8-05bb-4f7b-bdcb-990cc1d37e31
-- title:
--   Monotone closure
-- statement:
--   The **monotone closure** of a set function is $\hat v(S)=\max_{T\subseteq S}v(T)$. It reduces nonmonotone valuations to monotone ones.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Appendix A, p.40 (PDF 42)

import Mathlib

namespace CompDesignBFM

/-- The monotone closure `v̂(S) = max_(T ⊆ S) v(T)` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Appendix A, p.40, PDF 42). -/
noncomputable def closure {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  S.powerset.sup' ⟨∅, Finset.empty_mem_powerset S⟩ v

end CompDesignBFM


