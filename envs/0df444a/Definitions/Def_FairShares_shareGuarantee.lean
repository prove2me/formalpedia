-- Prove2me | Definitions.Def_FairShares_shareGuarantee
-- name    : FairShares_shareGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:20.426256+00:00
-- url     : https://prove2.me/theorems/d4f7a700-d850-4d11-85c5-bcfa9bfb744c
-- title:
--   Share guarantee $\hat s(v,n)$
-- statement:
--   For a share $s$ and a valuation $v$, the **share guarantee** is the lowest value of a bundle acceptable for $v$:
--   $$
--   \hat s(v,n)=\min_{\{S\,:\,v(S)\ge s(v,n)\}} v(S)=\hat s_v(v).
--   $$
--   Every allocation that gives the agent a bundle of value at least her share gives her at least her share guarantee.
--
--   **Formalization Note** Defined as the implied guarantee with report $v'=v$, in `WithTop ℝ`.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §3, p.10; §3.2, p.11

import Mathlib
import Definitions.Def_FairShares_impliedGuarantee

namespace FairShares

/-- **Share guarantee `ŝ(v, n)`.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §3, p.10: "Given a share function s, the associated share guarantee ŝ is defined as the
function satisfying ŝ(v, n) := min_{S | v(S)≥s(v,n)} v(S)." and p.11: "Observe that the implied
guarantee when the report is the true valuation is simply the share guarantee, that is,
ŝ_v(v) = ŝ(v, n)."

`shareGuarantee t v` is the minimum value `v S` of a bundle acceptable for `v` (`t v ≤ v S`).

**Formalization Note.** Defined as `impliedGuarantee t v v`, a value in `WithTop ℝ` (`⊤` only
when no bundle is acceptable, which realizability excludes). -/
noncomputable def shareGuarantee {m : ℕ} (t : (Finset (Fin m) → ℝ) → ℝ)
    (v : Finset (Fin m) → ℝ) : WithTop ℝ :=
  impliedGuarantee t v v

end FairShares


