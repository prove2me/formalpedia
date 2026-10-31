-- Prove2me | Definitions.Def_FairShares_SelfMaxAt
-- name    : FairShares_SelfMaxAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:13.223231+00:00
-- url     : https://prove2.me/theorems/8402a1e1-b113-41cd-9358-c1f9633bc950
-- title:
--   Self-maximizing share (Definition 3), at fixed $m$ and $n$
-- statement:
--   Fix $m$ goods and $n$ agents. A share $t$ (the paper's $s(\cdot,n)$) is **self-maximizing** on a set $D$ of valuations if for every true valuation $v\in D$ and every report $v'\in D$,
--   $$
--   \hat s_v(v)=\hat s(v,n)\ \ge\ \hat s_v(v').
--   $$
--   Reporting the true valuation maximizes the worst true value of an acceptable bundle.
--
--   **Formalization Note** Both sides are minima in `WithTop ℝ` (`FairShares.impliedGuarantee`).
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Definition 3, p.12

import Mathlib
import Definitions.Def_FairShares_impliedGuarantee
import Definitions.Def_FairShares_shareGuarantee

namespace FairShares

/-- **Self-maximizing share, at a fixed number of items and agents (Definition 3).**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Definition 3, p.12: "A share s is self-maximizing for class of valuations C if for every set
M of items and number of agents n, for every true valuation v ∈ C and every report v′ ∈ C it
holds that ŝ_v(v) = ŝ(v, n) ≥ ŝ_v(v′)".

`SelfMaxAt D t`: for all `v, v' ∈ D`, `ŝ_v(v') ≤ ŝ(v, n)`, where the true valuation `v` measures the
values and the report `v'` determines which bundles are acceptable.

**Formalization Note.** Both guarantees are minima in `WithTop ℝ` (see
`FairShares.impliedGuarantee`); for a share (realizable on `D`) they are real numbers. -/
def SelfMaxAt {m : ℕ} (D : Set (Finset (Fin m) → ℝ)) (t : (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  ∀ v ∈ D, ∀ v' ∈ D, impliedGuarantee t v v' ≤ shareGuarantee t v

end FairShares


