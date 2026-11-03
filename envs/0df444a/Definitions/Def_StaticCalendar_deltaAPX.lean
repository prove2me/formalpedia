-- Prove2me | Definitions.Def_StaticCalendar_deltaAPX
-- name    : StaticCalendar_deltaAPX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:55.393603+00:00
-- url     : https://prove2.me/theorems/1a46753f-696c-43f8-ba8d-26701ca5bb59
-- title:
--   The guarantee $\Delta^{APX}$
-- statement:
--   For $T\in\mathbb N$ and real $b$,
--
--   $$
--   \Delta^{APX}(T,b)=\frac{\mathbb E[\min\{\mathrm{Bin}(T,b/T),b\}]}{b}.
--   $$
--
--   This is the factor of Theorem 1. The value is meaningful for $0<b\le T$.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, (9), p.14

import Mathlib
import Definitions.Def_StaticCalendar_binomMinExp

namespace StaticCalendar

/-- `Δ^{APX} = E[min{Bin(T,b/T),b}]/b`, arXiv:1811.01077v5, (9), p.14, for real `b`.

**Formalization Note.** Meaningful for `0 < b ≤ T`; every statement of the mission assumes that
or takes a limit in `T`, where it eventually holds. -/
noncomputable def deltaAPX (T : ℕ) (b : ℝ) : ℝ :=
  binomMinExp T (b / T) b / b

end StaticCalendar


