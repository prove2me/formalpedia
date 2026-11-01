-- Prove2me | Definitions.Def_SimpleMenus_opt
-- name    : SimpleMenus_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:01.161463+00:00
-- url     : https://prove2.me/theorems/5f71d881-ec94-411b-a71a-c1d154befe59
-- title:
--   Clairvoyant benchmark $\mathrm{Rev}(\mathrm{OPT},F)$
-- statement:
--   For a valuation distribution $F$ on $[0,\bar v]$, the optimal revenue of a seller who knows $F$ is the best posted-price revenue
--
--   $$\mathrm{Rev}(\mathrm{OPT},F)=\max_{p\in[0,\bar v]} p\,\bigl(1-F(p-)\bigr)=\max_{p\in[0,\bar v]} p\,F([p,\infty)).$$
--
--   It is the denominator of the competitive ratio.
--
--   **Formalization Note** The supremum is taken over the subtype $[0,\bar v]$, with $1-F(p-)$ written as the measure of $[p,\infty)$. For a probability measure all values lie in $[0,\bar v]$, so the real supremum is the true one.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, §2, p.9, and display (1)

import Mathlib

open MeasureTheory Set

namespace SimpleMenus

/-- The clairvoyant benchmark `Rev(OPT, F) = max_{p ∈ [0, v̄]} p (1 − F(p−))` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, §2, p.9,
and display (1)).

Formalization Note: `1 − F(p−) = F([p, ∞))` for a probability measure, written `F (Ici p)`. The
supremum runs over the subtype `[0, v̄]`; for a probability measure the values lie in `[0, v̄]`, so
the real supremum is the true one (it is a maximum, but only the value is used). -/
noncomputable def opt (vbar : ℝ) (F : Measure ℝ) : ℝ :=
  ⨆ p : Icc (0 : ℝ) vbar, (p : ℝ) * (F (Ici (p : ℝ))).toReal

end SimpleMenus


