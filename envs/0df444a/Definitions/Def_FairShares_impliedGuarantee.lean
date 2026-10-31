-- Prove2me | Definitions.Def_FairShares_impliedGuarantee
-- name    : FairShares_impliedGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:40.777508+00:00
-- url     : https://prove2.me/theorems/ed9f58bb-e355-412d-b3a0-1d8395d72ea4
-- title:
--   Share implied guarantee $\hat s_v(v')$
-- statement:
--   For a share $t$ (the paper's $s(\cdot,n)$), a true valuation $v$ and a reported valuation $v'$, the **share implied guarantee** is the lowest true value of a bundle that is acceptable for the report:
--   $$
--   \hat s_v(v')=\min_{\{S\,:\,v'(S)\ge s(v',n)\}} v(S).
--   $$
--   The report $v'$ only selects which bundles count as acceptable; their values are measured by $v$.
--
--   **Formalization Note** The minimum is taken in $\mathbb R\cup\{+\infty\}$ (`WithTop ℝ`): it is the real minimum whenever some bundle is acceptable for $v'$, which realizability of the share guarantees, and $+\infty$ otherwise.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §3.2, p.11

import Mathlib

namespace FairShares

/-- **Share implied guarantee `ŝ_v(v')`.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §3.2, p.11: "For share s and any valuation v ∈ C, define the share implied guarantee when
reporting v′ ∈ C: ŝ_v(v′) = min_{S | v′(S)≥s(v′,n)} v(S) to be the lowest true value of any set
(measured by the true valuation v), among all sets that are acceptable with respect to v′."

`impliedGuarantee t v v'` is the minimum of the true values `v S` over the bundles `S` that are
acceptable for the report `v'`, i.e. `t v' ≤ v' S`, where `t` is the share `s(·, n)`.

**Formalization Note.** The minimum is `Finset.inf` in `WithTop ℝ`. When the acceptable family
is nonempty (which realizability of the share at `v'` guarantees) it is the real minimum; on an
empty family it is `⊤`, where the paper's minimum is undefined. -/
noncomputable def impliedGuarantee {m : ℕ} (t : (Finset (Fin m) → ℝ) → ℝ)
    (v v' : Finset (Fin m) → ℝ) : WithTop ℝ :=
  (Finset.univ.filter (fun S : Finset (Fin m) => t v' ≤ v' S)).inf (fun S => ((v S : ℝ) : WithTop ℝ))

end FairShares


