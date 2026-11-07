-- Prove2me | Definitions.Def_NSWBetter_nswOpt
-- name    : NSWBetter_nswOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:58.253047+00:00
-- url     : https://prove2.me/theorems/a4ae0c90-364f-484b-8502-88a071fed591
-- title:
--   Optimal Nash welfare $\mathrm{NSW}(I)$ of an identical-valuation instance
-- statement:
--   $\mathrm{NSW}(I)$ for an instance with $\Delta$ identical agents and value multiset $s$: the maximum over allocations $X$ of $\bigl(\prod_{i=1}^{\Delta}v(X_i)\bigr)^{1/\Delta}$. Its logarithm is $\mathrm{logNSW}(I)$.
--
--   **Formalization Note** The maximum is taken over assignments of every good to some agent; for nonnegative values this is the same as over subpartitions.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.9 (NSW(I)); Section 3, p.11

import Mathlib
import Definitions.Def_NSWBetter_sortDesc

namespace NSWBetter

/-- **Optimal Nash welfare with identical valuations.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.9: "We denote the optimal Nash welfare of an instance I using NSW(I)."

`nswOpt Δ s = max_f (Π_(i<Δ) Σ_(k : f k = i) v(g_(k+1)))^(1/Δ)` over all assignments `f` of the goods to the `Δ` agents.

**Formalization Note.** The maximum is over full assignments; for nonnegative values it equals the maximum over `Δ`-subpartitions (unallocated goods can be added to any bundle). The index type is finite and nonempty for `Δ ≥ 1`, so the real `iSup` is a maximum. -/
noncomputable def nswOpt (Δ : ℕ) (s : Multiset ℝ) : ℝ :=
  ⨆ f : Fin (sortDesc s).length → Fin Δ,
    (∏ i : Fin Δ, ∑ k ∈ Finset.univ.filter (fun k => f k = i), (sortDesc s).get k) ^ ((1 : ℝ) / Δ)

end NSWBetter


