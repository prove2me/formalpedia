-- Prove2me | Definitions.Def_InfHorizonVP_HasImproperIntegral
-- name    : InfHorizonVP_HasImproperIntegral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:21.398183+00:00
-- url     : https://prove2.me/theorems/883e5b63-bbc3-4c62-83f5-f30cb01db482
-- title:
--   The improper integral $\int_t^\infty L(s,x(s),\dot x(s))\,ds$
-- statement:
--   Let $L:\mathbb R_+\times E\times E\to\mathbb R$, $x$ an arc and $t\ge0$. The **improper integral** $\int_t^\infty L(s,x(s),\dot x(s))\,ds$ exists and equals $c\in[-\infty,+\infty]$ if $s\mapsto L(s,x(s),\dot x(s))$ is Lebesgue integrable on every $[t,T]$ and
--   $$
--   \int_t^\infty L(s,x(s),\dot x(s))\,ds=\lim_{T\to\infty}\int_t^T L(s,x(s),\dot x(s))\,ds=c .
--   $$
--
--   This is the cost of a trajectory in the variational problem $(P_t)$.
--
--   **Formalization Note** The limit is taken in the extended reals (`EReal`), so a limit $\pm\infty$ counts as existing; under (H1)–(H7) it is always finite. Integrability on each $[t,T]$ is required explicitly.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.7

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **The improper integral `∫_t^∞ L(s, x(s), ẋ(s)) ds` exists and equals `c`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.7: "Given an arc x(·) ∈ W^{1,1}_loc(R+, E), the
improper integral is defined by ∫_t^∞ L(s, x(s), ẋ(s))ds = lim_{T→∞} ∫_t^T L(s, x(s), ẋ(s))ds
for every t ∈ R+ provided that the above limit does exist."

`HasImproperIntegral L x t c` says that `s ↦ L(s, x(s), ẋ(s))` is Lebesgue integrable on every
`[t, T]` and that `∫_t^T L(s, x(s), ẋ(s)) ds → c` as `T → ∞`, the limit taken in `[-∞, +∞]`.

**Formalization Note.** The integrand is real-valued (`L : ℝ → E → E → ℝ`; under (H3) it is
finite everywhere). Integrability on each `[t, T]` is required so that the finite integrals are
genuine (Lean's Bochner integral is `0` for a non-integrable function). The limit is taken in
`EReal`, so a limit `±∞` counts as existing; under the standing hypotheses (H1)–(H7) the limit is
always finite. -/
def HasImproperIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) (x : ℝ → E) (t : ℝ) (c : EReal) : Prop :=
  (∀ T, t ≤ T → IntegrableOn (fun s => L s (x s) (deriv x s)) (Icc t T)) ∧
  Tendsto (fun T => (((∫ s in t..T, L s (x s) (deriv x s)) : ℝ) : EReal)) atTop (𝓝 c)

end InfHorizonVP


